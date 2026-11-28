import OMAReductions.R_BollobasEldridgeCatlinConjecture_bollobas_eldridge_catlin_conjecture_variants_maxDegree_le_two_R1_H2_R1
import Mathlib

-- Step BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.maxDegree_le_two.R1.H2.R1.H2 (hypothesis H2 of reduction BollobasEldridgeCatlinConjecture.bollobas_eldridge_catlin_conjecture.variants.maxDegree_le_two.R1.H2.R1): packing a graph whose
-- components are cycles and isolated vertices. Only `3 (Δ + 1) ≤ n + 1` and the cycle structure
-- are used: by the Fan–Kierstead theorem (G. Fan and H. A. Kierstead, Hamiltonian square-paths,
-- J. Combin. Theory Ser. B 67 (1996) 167–182), formalized in full below, the complement of `G₂`
-- contains a hamiltonian square-path, and every cycle numbered in zigzag order fits into it.
-- Credit: @JackTerok


/-!
# Fan–Kierstead, part 1: square paths, chords, and Lemma 1

Square paths are represented by index functions `f : ℕ → V` together with a length `n`:
the path is `f 0, f 1, …, f (n-1)`.
-/

open Finset

namespace FK

variable {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `f 0, …, f (n-1)` is a square path of `G`. -/
structure IsSq (n : ℕ) (f : ℕ → V) : Prop where
  adj1 : ∀ i, i + 1 < n → G.Adj (f i) (f (i + 1))
  adj2 : ∀ i, i + 2 < n → G.Adj (f i) (f (i + 2))
  inj : ∀ i j, i < n → j < n → f i = f j → i = j

/-- Number of `k`-chords of the path. -/
def chords (n : ℕ) (f : ℕ → V) (k : ℕ) : ℕ :=
  ((range n).filter (fun i => i + k < n ∧ G.Adj (f i) (f (i + k)))).card

/-- Number of neighbours of `x` among `f a, …, f (a+q-1)`. -/
def dseg (x : V) (f : ℕ → V) (a q : ℕ) : ℕ :=
  ((Ico a (a + q)).filter (fun i => G.Adj x (f i))).card

/-- Two paths have the same first ordered edge and the same last ordered edge. -/
def SameEnds (n : ℕ) (f : ℕ → V) (m : ℕ) (g : ℕ → V) : Prop :=
  g 0 = f 0 ∧ g 1 = f 1 ∧ g (m - 2) = f (n - 2) ∧ g (m - 1) = f (n - 1)

/-- `f` is optimal among square paths with the same end edges: longest, then most 3-chords,
then most 4-chords. -/
def OptFix (n : ℕ) (f : ℕ → V) : Prop :=
  IsSq G n f ∧ ∀ m g, IsSq G m g → SameEnds n f m g →
    m ≤ n ∧ (m = n → chords G n g 3 ≤ chords G n f 3 ∧
      (chords G n g 3 = chords G n f 3 → chords G n g 4 ≤ chords G n f 4))

variable {G}

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma IsSq.adj_close {n : ℕ} {f : ℕ → V} (h : IsSq G n f) {a b : ℕ} (_ha : a < n) (hb : b < n)
    (hab : a < b) (hb2 : b ≤ a + 2) : G.Adj (f a) (f b) := by
  rcases Nat.lt_or_ge b (a + 2) with h1 | h1
  · obtain rfl : b = a + 1 := by omega
    exact h.adj1 a hb
  · obtain rfl : b = a + 2 := by omega
    exact h.adj2 a hb

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma IsSq.adj_close' {n : ℕ} {f : ℕ → V} (h : IsSq G n f) {a b : ℕ} (ha : a < n) (hb : b < n)
    (hab : a ≠ b) (h1 : a ≤ b + 2) (h2 : b ≤ a + 2) : G.Adj (f a) (f b) := by
  rcases Nat.lt_or_gt_of_ne hab with hl | hl
  · exact h.adj_close ha hb hl (by omega)
  · exact (h.adj_close hb ha hl (by omega)).symm

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Building a square path from an index map `π` (positions other than `p`) and a new vertex `x`
at position `p`. -/
lemma isSq_of_pairs {m : ℕ} (g : ℕ → V)
    (hadj : ∀ i j, i < j → j ≤ i + 2 → j < m → G.Adj (g i) (g j))
    (hinj : ∀ i j, i < m → j < m → g i = g j → i = j) : IsSq G m g :=
  ⟨fun i hi => hadj i (i + 1) (by omega) (by omega) hi,
   fun i hi => hadj i (i + 2) (by omega) (by omega) hi, hinj⟩

/-- The path obtained from `f` by reading positions through `π`, with `x` placed at position `p`. -/
def remap (f : ℕ → V) (π : ℕ → ℕ) (p : ℕ) (x : V) : ℕ → V :=
  fun i => if i = p then x else f (π i)

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma remap_inj {n m : ℕ} {f : ℕ → V} (hf : IsSq G n f) {π : ℕ → ℕ} {p : ℕ} {x : V}
    (hx : ∀ i < n, f i ≠ x) (hπ : ∀ i < m, i ≠ p → π i < n)
    (hπinj : ∀ i j, i < m → j < m → i ≠ p → j ≠ p → π i = π j → i = j) :
    ∀ i j, i < m → j < m → remap f π p x i = remap f π p x j → i = j := by
  intro i j hi hj h
  unfold remap at h
  by_cases hip : i = p <;> by_cases hjp : j = p
  · omega
  · simp only [hip, hjp, if_true, if_false] at h
    exact absurd h.symm (hx _ (hπ j hj hjp))
  · simp only [hip, hjp, if_true, if_false] at h
    exact absurd h (hx _ (hπ i hi hip))
  · simp only [hip, hjp, if_false] at h
    exact hπinj i j hi hj hip hjp (hf.inj _ _ (hπ i hi hip) (hπ j hj hjp) h)

/- ### Reversal -/

/-- The reversed path. -/
def rev (n : ℕ) (f : ℕ → V) : ℕ → V := fun i => f (n - 1 - i)

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma IsSq.rev {n : ℕ} {f : ℕ → V} (h : IsSq G n f) : IsSq G n (rev n f) := by
  refine isSq_of_pairs _ (fun i j hij hj2 hj => ?_) (fun i j hi hj hh => ?_)
  · exact (h.adj_close (by omega) (by omega) (by omega) (by omega)).symm
  · have := h.inj _ _ (by omega) (by omega) hh
    omega

omit [DecidableEq V] in
lemma rev_rev {n : ℕ} {f : ℕ → V} {i : ℕ} (hi : i < n) : rev n (rev n f) i = f i := by
  unfold rev
  congr 1
  omega

omit [DecidableEq V] in
lemma chords_rev {n : ℕ} (f : ℕ → V) (k : ℕ) : chords G n (rev n f) k = chords G n f k := by
  unfold chords
  apply card_bij (fun i _ => n - 1 - (i + k))
  · intro i hi
    simp only [mem_filter, mem_range] at hi ⊢
    refine ⟨by omega, by omega, ?_⟩
    have e1 : n - 1 - (i + k) + k = n - 1 - i := by omega
    rw [e1]
    have := hi.2.2
    unfold rev at this
    have e2 : n - 1 - (i + k) = n - 1 - (i + k) := rfl
    exact this.symm
  · intro i hi j hj hij
    simp only [mem_filter, mem_range] at hi hj
    omega
  · intro j hj
    simp only [mem_filter, mem_range] at hj
    refine ⟨n - 1 - (j + k), ?_, by omega⟩
    simp only [mem_filter, mem_range]
    refine ⟨by omega, by omega, ?_⟩
    unfold rev
    have e1 : n - 1 - (n - 1 - (j + k)) = j + k := by omega
    have e2 : n - 1 - (n - 1 - (j + k) + k) = j := by omega
    rw [e1, e2]
    exact hj.2.2.symm

omit [DecidableEq V] in
lemma dseg_rev {n : ℕ} (x : V) (f : ℕ → V) {a q : ℕ} (h : a + q ≤ n) :
    dseg G x (rev n f) (n - (a + q)) q = dseg G x f a q := by
  unfold dseg
  apply card_bij (fun i _ => n - 1 - i)
  · intro i hi
    simp only [mem_filter, mem_Ico] at hi ⊢
    exact ⟨⟨by omega, by omega⟩, hi.2⟩
  · intro i hi j hj hij
    simp only [mem_filter, mem_Ico] at hi hj
    omega
  · intro j hj
    simp only [mem_filter, mem_Ico] at hj
    refine ⟨n - 1 - j, ?_, by omega⟩
    simp only [mem_filter, mem_Ico]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    unfold rev
    have e : n - 1 - (n - 1 - j) = j := by omega
    rw [e]
    exact hj.2

omit [DecidableEq V] in
lemma OptFix.rev {n : ℕ} {f : ℕ → V} (hn : 2 ≤ n) (h : OptFix G n f) : OptFix G n (rev n f) := by
  refine ⟨h.1.rev, fun m g hg hends => ?_⟩
  by_cases hm : m < 2
  · exact ⟨by omega, fun h' => by omega⟩
  obtain ⟨e0, e1, e2, e3⟩ := hends
  simp only [FK.rev] at e0 e1 e2 e3
  have key := h.2 m (FK.rev m g) hg.rev ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨key.1, fun hmn => ?_⟩
    subst hmn
    have k2 := key.2 rfl
    rw [chords_rev, chords_rev] at k2
    rw [chords_rev, chords_rev]
    exact k2
  · simp only [FK.rev]; convert e3 using 2 <;> omega
  · simp only [FK.rev]; convert e2 using 2 <;> omega
  · simp only [FK.rev]; convert e1 using 2 <;> omega
  · simp only [FK.rev]; convert e0 using 2 <;> omega

/- ### Counting neighbours in segments -/

omit [DecidableEq V] in
lemma dseg_add (x : V) (f : ℕ → V) (a q₁ q₂ : ℕ) :
    dseg G x f a (q₁ + q₂) = dseg G x f a q₁ + dseg G x f (a + q₁) q₂ := by
  unfold dseg
  rw [← card_union_of_disjoint]
  · congr 1
    ext i
    simp only [mem_filter, mem_Ico, mem_union]
    by_cases hadj : G.Adj x (f i) <;> simp only [hadj, and_true, and_false, or_false]; omega
  · rw [disjoint_left]
    intro i hi hi'
    simp only [mem_filter, mem_Ico] at hi hi'
    omega

omit [DecidableEq V] in
lemma dseg_le (x : V) (f : ℕ → V) (a q : ℕ) : dseg G x f a q ≤ q := by
  unfold dseg
  calc _ ≤ (Ico a (a + q)).card := card_filter_le _ _
    _ = q := by simp

omit [DecidableEq V] in
lemma dseg_one (x : V) (f : ℕ → V) (a : ℕ) :
    dseg G x f a 1 = if G.Adj x (f a) then 1 else 0 := by
  unfold dseg
  have : Ico a (a + 1) = {a} := by ext i; simp only [mem_Ico, mem_singleton]; omega
  rw [this, filter_singleton]
  by_cases h : G.Adj x (f a)
  · rw [if_pos h, if_pos h, card_singleton]
  · rw [if_neg h, if_neg h, card_empty]

omit [DecidableEq V] in
/-- Known non-neighbours reduce the count. -/
lemma dseg_add_card_le (x : V) (f : ℕ → V) (a q : ℕ) (N : Finset ℕ) (hN : N ⊆ Ico a (a + q))
    (hna : ∀ i ∈ N, ¬ G.Adj x (f i)) : dseg G x f a q + N.card ≤ q := by
  unfold dseg
  have h1 : (Ico a (a + q)).filter (fun i => G.Adj x (f i)) ⊆ Ico a (a + q) \ N := by
    intro i hi
    simp only [mem_filter] at hi
    exact mem_sdiff.2 ⟨hi.1, fun h => hna i h hi.2⟩
  have h2 := card_le_card h1
  rw [card_sdiff_of_subset hN] at h2
  simp at h2
  have := card_le_card hN
  simp at this
  omega

/- ### Building new square paths by remapping indices -/

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma remap_isSq {n m : ℕ} {f : ℕ → V} (hf : IsSq G n f) {x : V} (hx : ∀ i < n, f i ≠ x)
    (π : ℕ → ℕ) (p : ℕ)
    (hπ : ∀ i < m, i ≠ p → π i < n)
    (hπinj : ∀ i j, i < m → j < m → i ≠ p → j ≠ p → π i = π j → i = j)
    (hclose : ∀ i j, i < j → j ≤ i + 2 → j < m → i ≠ p → j ≠ p →
      (π i ≤ π j + 2 ∧ π j ≤ π i + 2) ∨ G.Adj (f (π i)) (f (π j)))
    (hxp : ∀ j, j < m → j ≠ p → j ≤ p + 2 → p ≤ j + 2 → G.Adj x (f (π j))) :
    IsSq G m (remap f π p x) := by
  refine isSq_of_pairs _ (fun i j hij hj2 hj => ?_) (remap_inj hf hx hπ hπinj)
  unfold remap
  by_cases hip : i = p
  · have hjp : j ≠ p := by omega
    simp only [hip, hjp, if_true, if_false]
    exact hxp j hj hjp (by omega) (by omega)
  · by_cases hjp : j = p
    · simp only [hip, hjp, if_true, if_false]
      exact (hxp i (by omega) hip (by omega) (by omega)).symm
    · simp only [hip, hjp, if_false]
      rcases hclose i j hij hj2 hj hip hjp with h | h
      · have hne : π i ≠ π j := fun he => by
          have := hπinj i j (by omega) hj hip hjp he
          omega
        exact hf.adj_close' (hπ i (by omega) hip) (hπ j hj hjp) hne h.1 h.2
      · exact h

omit [DecidableEq V] in
/-- Inserting a vertex adjacent to four consecutive vertices contradicts optimality. -/
lemma OptFix.no_four {n : ℕ} {f : ℕ → V} (hS : OptFix G n f) {x : V} (hx : ∀ i < n, f i ≠ x)
    {m : ℕ} (hm : m + 3 < n) (h0 : G.Adj x (f m)) (h1 : G.Adj x (f (m + 1)))
    (h2 : G.Adj x (f (m + 2))) (h3 : G.Adj x (f (m + 3))) : False := by
  let π : ℕ → ℕ := fun i => if i < m + 2 then i else i - 1
  have hg := remap_isSq (m := n + 1) hS.1 hx π (m + 2)
    (fun i hi hip => by simp only [π]; split_ifs <;> omega)
    (fun i j hi hj hip hjp h => by simp only [π] at h; split_ifs at h <;> omega)
    (fun i j hij hj2 hj hip hjp => Or.inl (by simp only [π]; split_ifs <;> omega))
    (fun j hj hjp h1' h2' => by
      simp only [π]
      have : j = m ∨ j = m + 1 ∨ j = m + 3 ∨ j = m + 4 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · simpa using h0
      · simpa using h1
      · simpa using h2
      · simpa using h3)
  have := (hS.2 (n + 1) _ hg ⟨?_, ?_, ?_, ?_⟩).1
  · omega
  · show (if (0 : ℕ) = m + 2 then x else f (π 0)) = f 0
    rw [if_neg (by omega)]; simp only [π]; rw [if_pos (by omega)]
  · show (if (1 : ℕ) = m + 2 then x else f (π 1)) = f 1
    rw [if_neg (by omega)]; simp only [π]; rw [if_pos (by omega)]
  · show (if n + 1 - 2 = m + 2 then x else f (π (n + 1 - 2))) = f (n - 2)
    rw [if_neg (by omega)]; simp only [π]; rw [if_neg (by omega)]; (try congr 1)
  · show (if n + 1 - 1 = m + 2 then x else f (π (n + 1 - 1))) = f (n - 1)
    rw [if_neg (by omega)]; simp only [π]; rw [if_neg (by omega)]; (try congr 1)

/- ### Replacing one vertex and the chord counts -/

variable (G) in
/-- Local chord count at position `p`. -/
def locC (n : ℕ) (h : ℕ → V) (p k : ℕ) : ℕ :=
  (if k ≤ p ∧ G.Adj (h (p - k)) (h p) then 1 else 0) +
    (if p + k < n ∧ G.Adj (h p) (h (p + k)) then 1 else 0)

variable (G) in
/-- The indicator of a `k`-chord at position `i`. -/
private def chT (n : ℕ) (h : ℕ → V) (k i : ℕ) : ℕ :=
  if i + k < n ∧ G.Adj (h i) (h (i + k)) then 1 else 0

omit [DecidableEq V] in
private lemma chords_eq_sum (n : ℕ) (h : ℕ → V) (k : ℕ) :
    chords G n h k = ∑ i ∈ range n, chT G n h k i := by
  unfold chords chT
  rw [card_filter]

omit [DecidableEq V] in
private lemma sum_E_eq (n : ℕ) (h : ℕ → V) {p k : ℕ} (hp : p < n) (hk : 1 ≤ k) :
    ∑ i ∈ range n, (if i = p ∨ i + k = p then chT G n h k i else 0) = locC G n h p k := by
  have hsplit : ∀ i, (if i = p ∨ i + k = p then chT G n h k i else 0) =
      (if i = p then chT G n h k p else 0) + (if i = p - k ∧ k ≤ p then chT G n h k (p - k) else 0) := by
    intro i
    by_cases h1 : i = p
    · subst h1
      rw [if_pos (Or.inl rfl), if_pos rfl, if_neg (by omega)]
      simp
    · by_cases h2 : i + k = p
      · rw [if_pos (Or.inr h2), if_neg h1, if_pos (by omega)]
        have : i = p - k := by omega
        subst this
        simp
      · rw [if_neg (by tauto), if_neg h1, if_neg (by omega)]
  rw [sum_congr rfl (fun i _ => hsplit i), sum_add_distrib, sum_ite_eq' (range n) p,
    if_pos (mem_range.2 hp)]
  unfold locC chT
  by_cases hkp : k ≤ p
  · have hmem : p - k ∈ range n := mem_range.2 (by omega)
    have : ∑ i ∈ range n, (if i = p - k ∧ k ≤ p then
        (if p - k + k < n ∧ G.Adj (h (p - k)) (h (p - k + k)) then 1 else 0) else 0) =
        (if p - k + k < n ∧ G.Adj (h (p - k)) (h (p - k + k)) then 1 else 0) := by
      simp only [hkp, and_true]
      rw [sum_ite_eq' (range n) (p - k), if_pos hmem]
    rw [this]
    have e : p - k + k = p := by omega
    simp only [e, hp, true_and, hkp]
    ring
  · have : ∑ i ∈ range n, (if i = p - k ∧ k ≤ p then
        (if p - k + k < n ∧ G.Adj (h (p - k)) (h (p - k + k)) then 1 else 0) else 0) = 0 := by
      apply sum_eq_zero
      intro i _
      rw [if_neg (by tauto)]
    rw [this]
    simp [hkp]

omit [DecidableEq V] in
lemma chords_update {n : ℕ} (f : ℕ → V) {p : ℕ} (hp : p < n) (x : V) {k : ℕ} (hk : 1 ≤ k) :
    chords G n (Function.update f p x) k + locC G n f p k =
      chords G n f k + locC G n (Function.update f p x) p k := by
  set g := Function.update f p x with hg
  rw [chords_eq_sum, chords_eq_sum, ← sum_E_eq n f hp hk, ← sum_E_eq n g hp hk,
    ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hE : i = p ∨ i + k = p
  · rw [if_pos hE, if_pos hE]
    ring
  · rw [if_neg hE, if_neg hE]
    push Not at hE
    unfold chT
    simp only [hg, Function.update_of_ne hE.1, Function.update_of_ne hE.2]

omit [DecidableEq V] in
lemma remap_id_eq_update (f : ℕ → V) (p : ℕ) (x : V) :
    remap f id p x = Function.update f p x := by
  funext i
  unfold remap
  by_cases h : i = p
  · subst h; simp
  · rw [if_neg h, Function.update_of_ne h]; rfl

omit [DecidableEq V] in
lemma locC_update {n : ℕ} (f : ℕ → V) (p : ℕ) (x : V) {k : ℕ} (hk : 1 ≤ k) :
    locC G n (Function.update f p x) p k =
      (if k ≤ p ∧ G.Adj (f (p - k)) x then 1 else 0) +
        (if p + k < n ∧ G.Adj x (f (p + k)) then 1 else 0) := by
  unfold locC
  have h1 : p - k ≠ p ∨ ¬ k ≤ p := by omega
  have h2 : p + k ≠ p := by omega
  rw [Function.update_self, Function.update_of_ne h2]
  by_cases hkp : k ≤ p
  · rw [Function.update_of_ne (by omega : p - k ≠ p)]
  · simp [hkp]

omit [DecidableEq V] in
/-- Replacing one vertex by `x` gives a competitor of the same length and ends. -/
lemma OptFix.rep {n : ℕ} {f : ℕ → V} (hS : OptFix G n f) {x : V} (hx : ∀ i < n, f i ≠ x)
    {p : ℕ} (hp2 : 2 ≤ p) (hp3 : p + 3 ≤ n)
    (hadj : ∀ i, i < n → i ≠ p → i ≤ p + 2 → p ≤ i + 2 → G.Adj x (f i)) :
    locC G n (Function.update f p x) p 3 ≤ locC G n f p 3 ∧
    (locC G n (Function.update f p x) p 3 = locC G n f p 3 →
      locC G n (Function.update f p x) p 4 ≤ locC G n f p 4) := by
  have hg : IsSq G n (Function.update f p x) := by
    rw [← remap_id_eq_update]
    exact remap_isSq hS.1 hx id p (fun i hi _ => hi) (fun i j _ _ _ _ h => h)
      (fun i j hij hj2 _ _ _ => Or.inl (by simp only [id]; omega))
      (fun j hj hjp h1 h2 => hadj j hj hjp h1 h2)
  have hends : SameEnds n f n (Function.update f p x) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Function.update_of_ne (by omega)]
  obtain ⟨-, hc⟩ := hS.2 n _ hg hends
  obtain ⟨c3, c4⟩ := hc rfl
  have e3 := chords_update (G := G) f (show p < n by omega) x (show 1 ≤ 3 by norm_num)
  have e4 := chords_update (G := G) f (show p < n by omega) x (show 1 ≤ 4 by norm_num)
  refine ⟨by omega, fun heq => ?_⟩
  have := c4 (by omega)
  omega


/-- `1` if `P` holds, `0` otherwise. -/
def bi (P : Prop) [Decidable P] : ℕ := if P then 1 else 0

lemma bi_pos {P : Prop} [Decidable P] (h : P) : bi P = 1 := if_pos h
lemma bi_neg {P : Prop} [Decidable P] (h : ¬ P) : bi P = 0 := if_neg h
lemma bi_le_one (P : Prop) [Decidable P] : bi P ≤ 1 := by unfold bi; split_ifs <;> omega
lemma bi_and_left {P : Prop} [Decidable P] (h : P) (Q : Prop) [Decidable Q] :
    bi (P ∧ Q) = bi Q := by
  unfold bi; simp [h]

lemma sum_le_two_mul_sub_three (F : ℕ → ℕ) (p : ℕ) (hp : 3 ≤ p) (hF : ∀ i, F i ≤ 2)
    (h0 : F 0 ≤ 1) (h1 : F 1 ≤ 1) (hl : F (p - 1) ≤ 1) : ∑ i ∈ range p, F i ≤ 2 * p - 3 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [sum_range_succ, ← sum_range_add_sum_Ico _ (show 2 ≤ q by omega)]
  have h01 : ∑ i ∈ range 2, F i = F 0 + F 1 := by simp [sum_range_succ]
  have hmid : ∑ k ∈ Ico 2 q, F k ≤ 2 * (q - 2) := by
    calc ∑ k ∈ Ico 2 q, F k ≤ (Ico 2 q).card • 2 := sum_le_card_nsmul (Ico 2 q) F 2 (fun i _ => hF i)
      _ = 2 * (q - 2) := by simp [Nat.card_Ico, mul_comm]
  rw [show q + 1 - 1 = q by omega] at hl
  rw [h01]
  omega

lemma card_filter_eq_sum_bi {α : Type} (A : Finset α) (P : α → Prop) [DecidablePred P] :
    (A.filter P).card = ∑ z ∈ A, bi (P z) := by
  unfold bi; rw [card_filter]

omit [DecidableEq V] in
/-- `OptFix.rep` with the local chord counts spelled out. -/
lemma OptFix.rep' {n : ℕ} {f : ℕ → V} (hS : OptFix G n f) {x : V} (hx : ∀ i < n, f i ≠ x)
    {p : ℕ} (hp2 : 2 ≤ p) (hp3 : p + 3 ≤ n)
    (hadj : ∀ i, i < n → i ≠ p → i ≤ p + 2 → p ≤ i + 2 → G.Adj x (f i)) :
    bi (3 ≤ p ∧ G.Adj (f (p - 3)) x) + bi (p + 3 < n ∧ G.Adj x (f (p + 3))) ≤
      bi (3 ≤ p ∧ G.Adj (f (p - 3)) (f p)) + bi (p + 3 < n ∧ G.Adj (f p) (f (p + 3))) ∧
    (bi (3 ≤ p ∧ G.Adj (f (p - 3)) x) + bi (p + 3 < n ∧ G.Adj x (f (p + 3))) =
      bi (3 ≤ p ∧ G.Adj (f (p - 3)) (f p)) + bi (p + 3 < n ∧ G.Adj (f p) (f (p + 3))) →
     bi (4 ≤ p ∧ G.Adj (f (p - 4)) x) + bi (p + 4 < n ∧ G.Adj x (f (p + 4))) ≤
      bi (4 ≤ p ∧ G.Adj (f (p - 4)) (f p)) + bi (p + 4 < n ∧ G.Adj (f p) (f (p + 4)))) := by
  have h := hS.rep hx hp2 hp3 hadj
  rw [locC_update f p x (by norm_num), locC_update f p x (by norm_num)] at h
  exact h

/- ### Lemma 1 -/

section Lemma1

variable {n : ℕ} {f : ℕ → V} {x : V}

/-- The adjacency pattern of a minimal counterexample segment. -/
def Pat (G : SimpleGraph V) (x : V) (f : ℕ → V) (a k : ℕ) : Prop :=
  ∀ o, o < 3 * k + 1 → (G.Adj x (f (a + o)) ↔ (o % 3 ≠ 0 ∨ o = 0 ∨ o = 3 * k))

omit [DecidableEq V] in
lemma lemma1_pattern (hS : OptFix G n f) (hx : ∀ i < n, f i ≠ x) {a q : ℕ} (haq : a + q ≤ n)
    (hviol : 2 * q + 3 < 3 * dseg G x f a q)
    (hmin : ∀ q' < q, ∀ a', a' + q' ≤ n → 3 * dseg G x f a' q' ≤ 2 * q' + 3) :
    ∃ k, 2 ≤ k ∧ q = 3 * k + 1 ∧ Pat G x f a k := by
  classical
  -- some position `a + 3t` with `t ≥ 1` is a neighbour
  have hA : ∃ t, 1 ≤ t ∧ 3 * t < q ∧ G.Adj x (f (a + 3 * t)) := by
    by_contra hne
    push Not at hne
    let N := (Ico 1 ((q + 2) / 3)).image (fun t => a + 3 * t)
    have hNsub : N ⊆ Ico a (a + q) := by
      intro i hi
      simp only [N, mem_image, mem_Ico] at hi ⊢
      obtain ⟨t, ht, rfl⟩ := hi
      omega
    have hNna : ∀ i ∈ N, ¬ G.Adj x (f i) := by
      intro i hi
      simp only [N, mem_image, mem_Ico] at hi
      obtain ⟨t, ht, rfl⟩ := hi
      exact hne t ht.1 (by omega)
    have hcard : N.card = (q + 2) / 3 - 1 := by
      rw [card_image_of_injective _ (fun t₁ t₂ h => by have h' : a + 3 * t₁ = a + 3 * t₂ := h; omega), Nat.card_Ico]
    have := dseg_add_card_le (G := G) x f a q N hNsub hNna
    omega
  let t₀ := Nat.find hA
  have ht₀ : 1 ≤ t₀ ∧ 3 * t₀ < q ∧ G.Adj x (f (a + 3 * t₀)) := Nat.find_spec hA
  have hlt : ∀ t, 1 ≤ t → t < t₀ → ¬ G.Adj x (f (a + 3 * t)) := fun t h1 h2 hadj =>
    Nat.find_min hA h2 ⟨h1, by omega, hadj⟩
  -- the first `3 t₀` positions contain at least `2 t₀ + 1` neighbours
  have hsplit := dseg_add (G := G) x f a (3 * t₀) (q - 3 * t₀)
  rw [show 3 * t₀ + (q - 3 * t₀) = q by omega] at hsplit
  have hd1 : 2 * t₀ + 1 ≤ dseg G x f a (3 * t₀) := by
    by_contra hc
    have := hmin (q - 3 * t₀) (by omega) (a + 3 * t₀) (by omega)
    omega
  -- hence the first `3 t₀ + 1` positions violate the bound, so `q = 3 t₀ + 1`
  have hq : q = 3 * t₀ + 1 := by
    by_contra hne
    have h2 := dseg_add (G := G) x f a (3 * t₀) 1
    rw [dseg_one, if_pos ht₀.2.2] at h2
    have := hmin (3 * t₀ + 1) (by omega) a (by omega)
    omega
  -- the adjacency pattern
  have hpat : Pat G x f a t₀ := by
    intro o ho
    constructor
    · intro hadj
      by_contra hc
      push Not at hc
      have hi1 : 1 ≤ o / 3 := by omega
      have hi2 : o / 3 < t₀ := by omega
      have := hlt (o / 3) hi1 hi2
      rw [show 3 * (o / 3) = o by omega] at this
      exact this hadj
    · intro ho'
      by_contra hna
      let N := insert (a + o) ((Ico 1 t₀).image (fun t => a + 3 * t))
      have hnotin : a + o ∉ (Ico 1 t₀).image (fun t => a + 3 * t) := by
        simp only [mem_image, mem_Ico, not_exists, not_and]
        intro t ht h
        omega
      have hNsub : N ⊆ Ico a (a + q) := by
        intro i hi
        simp only [N, mem_insert, mem_image, mem_Ico] at hi ⊢
        rcases hi with rfl | ⟨t, ht, rfl⟩ <;> omega
      have hNna : ∀ i ∈ N, ¬ G.Adj x (f i) := by
        intro i hi
        simp only [N, mem_insert, mem_image, mem_Ico] at hi
        rcases hi with rfl | ⟨t, ht, rfl⟩
        · exact hna
        · exact hlt t ht.1 ht.2
      have hcard : N.card = t₀ := by
        rw [card_insert_of_notMem hnotin,
          card_image_of_injective _ (fun t₁ t₂ h => by have h' : a + 3 * t₁ = a + 3 * t₂ := h; omega), Nat.card_Ico]
        omega
      have := dseg_add_card_le (G := G) x f a q N hNsub hNna
      omega
  refine ⟨t₀, ?_, hq, hpat⟩
  -- `t₀ = 1` would give four consecutive neighbours
  by_contra h1
  have ht1 : t₀ = 1 := by omega
  rw [ht1] at hpat hq
  have p0 := (hpat 0 (by omega)).2 (by omega)
  have p1 := (hpat 1 (by omega)).2 (by omega)
  have p2 := (hpat 2 (by omega)).2 (by omega)
  have p3 := (hpat 3 (by omega)).2 (by omega)
  simp only [add_zero] at p0
  exact hS.no_four hx (m := a) (by omega) p0 p1 p2 p3

end Lemma1

omit [DecidableEq V] in
lemma remap_ne {f : ℕ → V} {π : ℕ → ℕ} {p : ℕ} {x : V} {i : ℕ} (h : i ≠ p) :
    remap f π p x i = f (π i) := by
  unfold remap; rw [if_neg h]

omit [DecidableEq V] in
/-- A longer square path with the same end edges contradicts optimality. -/
lemma OptFix.no_longer {n : ℕ} {f : ℕ → V} (hS : OptFix G n f) {x : V} {π : ℕ → ℕ} {p : ℕ}
    (hg : IsSq G (n + 1) (remap f π p x)) (hp0 : p ≠ 0) (hp1 : p ≠ 1) (hp2 : p ≠ n - 1)
    (hp3 : p ≠ n) (hn : 2 ≤ n) (e0 : π 0 = 0) (e1 : π 1 = 1) (e2 : π (n - 1) = n - 2)
    (e3 : π n = n - 1) : False := by
  have := (hS.2 (n + 1) _ hg ⟨?_, ?_, ?_, ?_⟩).1
  · omega
  · rw [remap_ne (Ne.symm hp0), e0]
  · rw [remap_ne (Ne.symm hp1), e1]
  · rw [show n + 1 - 2 = n - 1 by omega, remap_ne (Ne.symm hp2), e2]
  · rw [show n + 1 - 1 = n by omega, remap_ne (Ne.symm hp3), e3]

section Lemma1b

variable {n : ℕ} {f : ℕ → V} {x : V}

omit [DecidableEq V] in
/-- Lemma 1, the path `… u_{a+1} u_{a+2} x u_{a+3} u_{a+5} u_{a+4} u_{a+6} …`. -/
lemma lemma1_fwd (hS : OptFix G n f) (hx : ∀ i < n, f i ≠ x) {a : ℕ} (han : a + 7 ≤ n)
    (x0 : G.Adj x (f a)) (x1 : G.Adj x (f (a + 1))) (x2 : G.Adj x (f (a + 2)))
    (x4 : G.Adj x (f (a + 4))) (hch : G.Adj (f (a + 3)) (f (a + 6))) : False := by
  let π : ℕ → ℕ := fun i => if i ≤ a + 1 then i else if i = a + 3 then a + 2 else
    if i = a + 4 then a + 4 else if i = a + 5 then a + 3 else i - 1
  have hg := remap_isSq (m := n + 1) hS.1 hx π (a + 2)
    (fun i hi hip => by simp only [π]; split_ifs <;> omega)
    (fun i j hi hj hip hjp h => by simp only [π] at h; split_ifs at h <;> omega)
    (fun i j hij hj2 hj hip hjp => by
      by_cases hsp : i = a + 5 ∧ j = a + 7
      · right
        obtain ⟨rfl, rfl⟩ := hsp
        have e1 : π (a + 5) = a + 3 := by simp only [π]; split_ifs <;> omega
        have e2 : π (a + 7) = a + 6 := by simp only [π]; split_ifs <;> omega
        rw [e1, e2]; exact hch
      · left; simp only [π]; split_ifs <;> omega)
    (fun j hj hjp h1 h2 => by
      have : j = a ∨ j = a + 1 ∨ j = a + 3 ∨ j = a + 4 := by omega
      rcases this with h | h | h | h <;> rw [h]
      · have e : π a = a := by simp only [π]; split_ifs <;> omega
        rw [e]; exact x0
      · have e : π (a + 1) = a + 1 := by simp only [π]; split_ifs <;> omega
        rw [e]; exact x1
      · have e : π (a + 3) = a + 2 := by simp only [π]; split_ifs <;> omega
        rw [e]; exact x2
      · have e : π (a + 4) = a + 4 := by simp only [π]; split_ifs <;> omega
        rw [e]; exact x4)
  exact hS.no_longer hg (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp only [π]; split_ifs <;> omega) (by simp only [π]; split_ifs <;> omega)
    (by simp only [π]; split_ifs <;> omega) (by simp only [π]; split_ifs <;> omega)

omit [DecidableEq V] in
/-- Lemma 1, "former case": `… u_a u_{a+1} u_{a+4} u_{a+2} u_{a+3} x u_{a+5} …` (1-based),
i.e. `f (a-1), f a, f (a+3), f (a+1), f (a+2), x, f (a+4), …`. -/
lemma lemma1_former (hS : OptFix G n f) (hx : ∀ i < n, f i ≠ x) {a : ℕ} (ha : 1 ≤ a)
    (han : a + 7 ≤ n)
    (x1 : G.Adj x (f (a + 1))) (x2 : G.Adj x (f (a + 2))) (x4 : G.Adj x (f (a + 4)))
    (x5 : G.Adj x (f (a + 5))) (c3 : G.Adj (f a) (f (a + 3))) (c4 : G.Adj (f (a - 1)) (f (a + 3))) :
    False := by
  let π : ℕ → ℕ := fun i => if i ≤ a then i else if i = a + 1 then a + 3 else
    if i = a + 2 then a + 1 else if i = a + 3 then a + 2 else i - 1
  have hg := remap_isSq (m := n + 1) hS.1 hx π (a + 4)
    (fun i hi hip => by simp only [π]; split_ifs <;> omega)
    (fun i j hi hj hip hjp h => by simp only [π] at h; split_ifs at h <;> omega)
    (fun i j hij hj2 hj hip hjp => by
      by_cases hsp : i = a - 1 ∧ j = a + 1
      · right
        obtain ⟨h1, h2⟩ := hsp
        rw [h1, h2]
        have e1 : π (a - 1) = a - 1 := by simp only [π]; split_ifs <;> omega
        have e2 : π (a + 1) = a + 3 := by simp only [π]; split_ifs <;> omega
        rw [e1, e2]; exact c4
      · by_cases hsp' : i = a ∧ j = a + 1
        · right
          obtain ⟨h1, h2⟩ := hsp'
          rw [h1, h2]
          have e1 : π a = a := by simp only [π]; split_ifs <;> omega
          have e2 : π (a + 1) = a + 3 := by simp only [π]; split_ifs <;> omega
          rw [e1, e2]; exact c3
        · left; simp only [π]; split_ifs <;> omega)
    (fun j hj hjp h1 h2 => by
      have : j = a + 2 ∨ j = a + 3 ∨ j = a + 5 ∨ j = a + 6 := by omega
      rcases this with h | h | h | h <;> rw [h]
      · have e : π (a + 2) = a + 1 := by simp only [π]; split_ifs <;> omega
        rw [e]; exact x1
      · have e : π (a + 3) = a + 2 := by simp only [π]; split_ifs <;> omega
        rw [e]; exact x2
      · have e : π (a + 5) = a + 4 := by simp only [π]; split_ifs <;> omega
        rw [e]; exact x4
      · have e : π (a + 6) = a + 5 := by simp only [π]; split_ifs <;> omega
        rw [e]; exact x5)
  exact hS.no_longer hg (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp only [π]; split_ifs <;> omega) (by simp only [π]; split_ifs; omega)
    (by simp only [π]; split_ifs <;> omega) (by simp only [π]; split_ifs <;> omega)

omit [DecidableEq V] in
/-- Lemma 1, "latter case": the block path
`u_{a+1} u_{a+2} x (u_{a+3} u_{a+5} u_{a+4}) … (u_{a+3t} u_{a+3t+2} u_{a+3t+1}) u_{a+3t+3} …`. -/
lemma lemma1_latter (hS : OptFix G n f) (hx : ∀ i < n, f i ≠ x) {a t : ℕ} (ht : 1 ≤ t)
    (han : a + 3 * t + 4 ≤ n)
    (x0 : G.Adj x (f a)) (x1 : G.Adj x (f (a + 1))) (x2 : G.Adj x (f (a + 2)))
    (x4 : G.Adj x (f (a + 4)))
    (c4 : ∀ j, 1 ≤ j → j + 1 ≤ t → G.Adj (f (a + 3 * j)) (f (a + 3 * j + 4)))
    (c3 : G.Adj (f (a + 3 * t)) (f (a + 3 * t + 3))) : False := by
  let π : ℕ → ℕ := fun i => if i ≤ a + 1 then i else if i < a + 3 + 3 * t then
    a + 3 * ((i - (a + 3)) / 3) + 2 +
      (if (i - (a + 3)) % 3 = 1 then 2 else if (i - (a + 3)) % 3 = 2 then 1 else 0)
    else i - 1
  have hg := remap_isSq (m := n + 1) hS.1 hx π (a + 2)
    (fun i hi hip => by simp only [π]; split_ifs <;> omega)
    (fun i j hi hj hip hjp h => by simp only [π] at h; split_ifs at h <;> omega)
    (fun i j hij hj2 hj hip hjp => by
      by_cases hsp : a + 3 ≤ i ∧ i < a + 3 + 3 * t ∧ (i - (a + 3)) % 3 = 2 ∧ j = i + 2
      · right
        obtain ⟨h1, h2, h3, rfl⟩ := hsp
        have e1 : π i = a + 3 * ((i - (a + 3)) / 3 + 1) := by simp only [π]; split_ifs <;> omega
        by_cases hlast : i + 2 < a + 3 + 3 * t
        · have e2 : π (i + 2) = a + 3 * ((i - (a + 3)) / 3 + 1) + 4 := by
            simp only [π]; split_ifs <;> omega
          rw [e1, e2]
          exact c4 ((i - (a + 3)) / 3 + 1) (by omega) (by omega)
        · have e2 : π (i + 2) = a + 3 * t + 3 := by simp only [π]; split_ifs <;> omega
          have e1' : a + 3 * ((i - (a + 3)) / 3 + 1) = a + 3 * t := by omega
          rw [e1, e2, e1']; exact c3
      · left; simp only [π]; split_ifs <;> omega)
    (fun j hj hjp h1 h2 => by
      have : j = a ∨ j = a + 1 ∨ j = a + 3 ∨ j = a + 4 := by omega
      rcases this with h | h | h | h <;> rw [h]
      · have e : π a = a := by simp only [π]; split_ifs <;> omega
        rw [e]; exact x0
      · have e : π (a + 1) = a + 1 := by simp only [π]; split_ifs <;> omega
        rw [e]; exact x1
      · have e : π (a + 3) = a + 2 := by simp only [π]; split_ifs <;> omega
        rw [e]; exact x2
      · have e : π (a + 4) = a + 4 := by simp only [π]; split_ifs <;> omega
        rw [e]; exact x4)
  exact hS.no_longer hg (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp only [π]; split_ifs <;> omega) (by simp only [π]; split_ifs <;> omega)
    (by simp only [π]; split_ifs <;> omega) (by simp only [π]; split_ifs <;> omega)

end Lemma1b

section Lemma1c

variable {n : ℕ} {f : ℕ → V} {x : V}

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma Pat.adj {a k : ℕ} (hpat : Pat G x f a k) {o : ℕ} (ho : o < 3 * k + 1)
    (h : o % 3 ≠ 0 ∨ o = 0 ∨ o = 3 * k) : G.Adj x (f (a + o)) := (hpat o ho).2 h

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma Pat.nadj {a k : ℕ} (hpat : Pat G x f a k) {o : ℕ} (ho : o < 3 * k + 1)
    (h : o % 3 = 0) (h1 : o ≠ 0) (h2 : o ≠ 3 * k) : ¬ G.Adj x (f (a + o)) := fun hh => by
  have := (hpat o ho).1 hh
  omega

omit [DecidableEq V] in
lemma lemma1_ends (hS : OptFix G n f) (hx : ∀ i < n, f i ≠ x) {a k : ℕ} (hk : 2 ≤ k)
    (haq : a + (3 * k + 1) ≤ n) (hpat : Pat G x f a k) :
    G.Adj (f a) (f (a + 3)) ∧ ¬ G.Adj (f (a + 3)) (f (a + 6)) := by
  have x0 : G.Adj x (f a) := by simpa using hpat.adj (o := 0) (by omega) (by omega)
  have x1 := hpat.adj (o := 1) (by omega) (by omega)
  have x2 := hpat.adj (o := 2) (by omega) (by omega)
  have x4 := hpat.adj (o := 4) (by omega) (by omega)
  have x5 := hpat.adj (o := 5) (by omega) (by omega)
  have hnf : ¬ G.Adj (f (a + 3)) (f (a + 6)) := fun h => lemma1_fwd hS hx (by omega) x0 x1 x2 x4 h
  refine ⟨?_, hnf⟩
  obtain ⟨h3, -⟩ := hS.rep' hx (p := a + 3) (by omega) (by omega) (fun i hi hip h1 h2 => by
    have : i = a + 1 ∨ i = a + 2 ∨ i = a + 4 ∨ i = a + 5 := by omega
    rcases this with h | h | h | h <;> rw [h]
    · exact x1
    · exact x2
    · exact x4
    · exact x5)
  simp only [bi_and_left (show 3 ≤ a + 3 by omega), bi_and_left (show a + 3 + 3 < n by omega),
    show a + 3 - 3 = a by omega, show a + 3 + 3 = a + 6 by omega] at h3
  rw [bi_pos x0.symm, bi_neg hnf] at h3
  by_contra hnot
  rw [bi_neg hnot] at h3
  have := bi_le_one (G.Adj x (f (a + 6)))
  omega

omit [DecidableEq V] in
lemma lemma1_ends_rev (hS : OptFix G n f) (hx : ∀ i < n, f i ≠ x) {a k : ℕ} (hk : 2 ≤ k)
    (haq : a + (3 * k + 1) ≤ n) (hpat : Pat G x f a k) :
    G.Adj (f (a + 3 * k)) (f (a + 3 * k - 3)) ∧ ¬ G.Adj (f (a + 3 * k - 3)) (f (a + 3 * k - 6)) := by
  have hn2 : 2 ≤ n := by omega
  have hS' := hS.rev hn2
  have hx' : ∀ i < n, rev n f i ≠ x := fun i hi => hx _ (by omega)
  have hpat' : Pat G x (rev n f) (n - (a + (3 * k + 1))) k := by
    intro o ho
    unfold rev
    rw [show n - 1 - (n - (a + (3 * k + 1)) + o) = a + (3 * k - o) by omega,
      hpat (3 * k - o) (by omega)]
    constructor <;> intro h <;> omega
  obtain ⟨h1, h2⟩ := lemma1_ends hS' hx' hk (by omega) hpat'
  unfold rev at h1 h2
  rw [show n - 1 - (n - (a + (3 * k + 1))) = a + 3 * k by omega,
    show n - 1 - (n - (a + (3 * k + 1)) + 3) = a + 3 * k - 3 by omega] at h1
  rw [show n - 1 - (n - (a + (3 * k + 1)) + 3) = a + 3 * k - 3 by omega,
    show n - 1 - (n - (a + (3 * k + 1)) + 6) = a + 3 * k - 6 by omega] at h2
  exact ⟨h1, h2⟩

omit [DecidableEq V] in
/-- **Lemma 1** (Fan–Kierstead). If `S` is optimal among square paths with its end edges and
`x ∉ S`, then every segment `Q` of `S` satisfies `d(x, Q) ≤ 2|Q|/3 + 1`. -/
theorem lemma1 (hS : OptFix G n f) (hx : ∀ i < n, f i ≠ x) {a q : ℕ} (haq : a + q ≤ n) :
    3 * dseg G x f a q ≤ 2 * q + 3 := by
  classical
  by_contra hc
  push Not at hc
  have hP : ∃ q, ∃ a, a + q ≤ n ∧ 2 * q + 3 < 3 * dseg G x f a q := ⟨q, a, haq, hc⟩
  obtain ⟨a0, ha0, hv0⟩ := Nat.find_spec hP
  have hmin : ∀ q' < Nat.find hP, ∀ a', a' + q' ≤ n → 3 * dseg G x f a' q' ≤ 2 * q' + 3 :=
    fun q' hq' a' h => by
      by_contra hc'
      push Not at hc'
      exact Nat.find_min hP hq' ⟨a', h, hc'⟩
  obtain ⟨k, hk, hq, hpat⟩ := lemma1_pattern hS hx ha0 hv0 hmin
  rw [hq] at ha0
  obtain ⟨e1, e2⟩ := lemma1_ends hS hx hk ha0 hpat
  obtain ⟨m1, m2⟩ := lemma1_ends_rev hS hx hk ha0 hpat
  have hk3 : 3 ≤ k := by
    by_contra h
    have hk2 : k = 2 := by omega
    subst hk2
    rw [show a0 + 3 * 2 - 3 = a0 + 3 by omega, show a0 + 3 * 2 - 6 = a0 by omega] at m2
    exact m2 e1.symm
  -- the first `t ≥ 2` such that `f (a0 + 3t)` has a 3-chord inside the segment
  have hT : ∃ t, 2 ≤ t ∧ t + 1 ≤ k ∧ (G.Adj (f (a0 + 3 * t)) (f (a0 + 3 * t - 3)) ∨
      G.Adj (f (a0 + 3 * t)) (f (a0 + 3 * t + 3))) := by
    refine ⟨k - 1, by omega, by omega, Or.inr ?_⟩
    rw [show a0 + 3 * (k - 1) = a0 + 3 * k - 3 by omega,
      show a0 + 3 * k - 3 + 3 = a0 + 3 * k by omega]
    exact m1.symm
  obtain ⟨ht2, htk, htc⟩ := Nat.find_spec hT
  set t := Nat.find hT with ht_def
  have htmin : ∀ j, 2 ≤ j → j < t → ¬ G.Adj (f (a0 + 3 * j)) (f (a0 + 3 * j - 3)) ∧
      ¬ G.Adj (f (a0 + 3 * j)) (f (a0 + 3 * j + 3)) := by
    intro j hj1 hj2
    have := Nat.find_min hT hj2
    push Not at this
    exact this hj1 (by omega)
  -- 4-chords in the middle, from optimality
  have hc4mid : ∀ j, 2 ≤ j → j < t → G.Adj (f (a0 + 3 * j)) (f (a0 + 3 * j + 4)) := by
    intro j hj1 hj2
    obtain ⟨hno1, hno2⟩ := htmin j hj1 hj2
    obtain ⟨h3, h4⟩ := hS.rep' hx (p := a0 + 3 * j) (by omega) (by omega)
      (fun i hi hip h1 h2 => by
        have hi' : i = a0 + (i - a0) := by omega
        rw [hi']
        exact hpat.adj (by omega) (by omega))
    have g1 : ¬ G.Adj (f (a0 + 3 * j - 3)) x := fun h => by
      have := hpat.nadj (o := 3 * j - 3) (by omega) (by omega) (by omega) (by omega)
      rw [show a0 + (3 * j - 3) = a0 + 3 * j - 3 by omega] at this
      exact this h.symm
    have g2 : ¬ G.Adj x (f (a0 + 3 * j + 3)) := fun h => by
      have := hpat.nadj (o := 3 * j + 3) (by omega) (by omega) (by omega) (by omega)
      rw [show a0 + (3 * j + 3) = a0 + 3 * j + 3 by omega] at this
      exact this h
    have g3 : G.Adj (f (a0 + 3 * j - 4)) x := by
      have := hpat.adj (o := 3 * j - 4) (by omega) (by omega)
      rw [show a0 + (3 * j - 4) = a0 + 3 * j - 4 by omega] at this
      exact this.symm
    have g4 : G.Adj x (f (a0 + 3 * j + 4)) := by
      have := hpat.adj (o := 3 * j + 4) (by omega) (by omega)
      rw [show a0 + (3 * j + 4) = a0 + 3 * j + 4 by omega] at this
      exact this
    simp only [bi_and_left (show 3 ≤ a0 + 3 * j by omega),
      bi_and_left (show a0 + 3 * j + 3 < n by omega),
      bi_and_left (show 4 ≤ a0 + 3 * j by omega),
      bi_and_left (show a0 + 3 * j + 4 < n by omega)] at h3 h4
    rw [bi_neg g1, bi_neg g2, bi_neg (fun h => hno1 h.symm), bi_neg hno2] at h4
    rw [bi_pos g3, bi_pos g4] at h4
    have h4' := h4 rfl
    by_contra hcon
    rw [bi_neg hcon] at h4'
    have := bi_le_one (G.Adj (f (a0 + 3 * j - 4)) (f (a0 + 3 * j)))
    omega
  -- the position `a0 + 3`
  have x0 : G.Adj x (f a0) := by simpa using hpat.adj (o := 0) (by omega) (by omega)
  have x1 := hpat.adj (o := 1) (by omega) (by omega)
  have x2 := hpat.adj (o := 2) (by omega) (by omega)
  have x4 := hpat.adj (o := 4) (by omega) (by omega)
  have x5 := hpat.adj (o := 5) (by omega) (by omega)
  have x6 := hpat.nadj (o := 6) (by omega) (by omega) (by omega) (by omega)
  have x7 := hpat.adj (o := 7) (by omega) (by omega)
  obtain ⟨h3, h4⟩ := hS.rep' hx (p := a0 + 3) (by omega) (by omega) (fun i hi hip h1 h2 => by
    have : i = a0 + 1 ∨ i = a0 + 2 ∨ i = a0 + 4 ∨ i = a0 + 5 := by omega
    rcases this with h | h | h | h <;> rw [h]
    · exact x1
    · exact x2
    · exact x4
    · exact x5)
  simp only [bi_and_left (show 3 ≤ a0 + 3 by omega), bi_and_left (show a0 + 3 + 3 < n by omega),
    bi_and_left (show a0 + 3 + 4 < n by omega), show a0 + 3 - 3 = a0 by omega,
    show a0 + 3 + 3 = a0 + 6 by omega, show a0 + 3 + 4 = a0 + 7 by omega] at h3 h4
  rw [bi_pos x0.symm, bi_neg x6, bi_pos e1, bi_neg e2, bi_pos x7] at h4
  have h4' := h4 rfl
  by_cases hfor : 1 ≤ a0 ∧ G.Adj (f (a0 - 1)) (f (a0 + 3))
  · -- former case
    exact lemma1_former hS hx hfor.1 (by omega) x1 x2 x4 x5 e1 hfor.2
  · rw [bi_neg (show ¬ (4 ≤ a0 + 3 ∧ G.Adj (f (a0 + 3 - 4)) (f (a0 + 3))) by
      rintro ⟨h1, h2⟩
      exact hfor ⟨by omega, by rw [show a0 - 1 = a0 + 3 - 4 by omega]; exact h2⟩)] at h4'
    have hlat : G.Adj (f (a0 + 3)) (f (a0 + 7)) := by
      by_contra hc
      rw [bi_neg hc] at h4'
      have := bi_le_one (4 ≤ a0 + 3 ∧ G.Adj (f (a0 + 3 - 4)) x)
      omega
    -- the forward 3-chord at `t`
    have hfwd : G.Adj (f (a0 + 3 * t)) (f (a0 + 3 * t + 3)) := by
      rcases htc with hb | hf
      · exfalso
        by_cases ht3 : 3 ≤ t
        · have := (htmin (t - 1) (by omega) (by omega)).2
          rw [show a0 + 3 * (t - 1) = a0 + 3 * t - 3 by omega,
            show a0 + 3 * t - 3 + 3 = a0 + 3 * t by omega] at this
          exact this hb.symm
        · have ht2' : t = 2 := by omega
          rw [ht2'] at hb
          rw [show a0 + 3 * 2 = a0 + 6 by omega, show a0 + 6 - 3 = a0 + 3 by omega] at hb
          exact e2 hb.symm
      · exact hf
    refine lemma1_latter hS hx (t := t) (by omega) (by omega) x0 x1 x2 x4 (fun j hj1 hj2 => ?_) hfwd
    by_cases hj : j = 1
    · subst hj; simpa using hlat
    · exact hc4mid j (by omega) (by omega)

end Lemma1c

omit [DecidableEq V] in
/-- **Lemma 2** (Fan–Kierstead). Equality in Lemma 1 forces the first two vertices of the segment
to be neighbours of `x` and the vertex before the segment not to be. -/
theorem lemma2 {n : ℕ} {f : ℕ → V} {x : V} (hS : OptFix G n f) (hx : ∀ i < n, f i ≠ x)
    {a q : ℕ} (haq : a + q ≤ n) (heq : 3 * dseg G x f a q = 2 * q + 3) :
    G.Adj x (f a) ∧ G.Adj x (f (a + 1)) ∧ (1 ≤ a → ¬ G.Adj x (f (a - 1))) := by
  have hq : 3 ≤ q := by have := dseg_le (G := G) x f a q; omega
  have h1 := lemma1 hS hx (a := a + 2) (q := q - 2) (by omega)
  have hs := dseg_add (G := G) x f a 2 (q - 2)
  rw [show 2 + (q - 2) = q by omega] at hs
  have hs2 := dseg_add (G := G) x f a 1 1
  rw [dseg_one, dseg_one] at hs2
  have ha : G.Adj x (f a) ∧ G.Adj x (f (a + 1)) := by
    by_contra hc
    have : dseg G x f a 2 ≤ 1 := by
      rw [hs2]
      by_cases h0 : G.Adj x (f a) <;> by_cases h1' : G.Adj x (f (a + 1)) <;>
        simp only [h0, h1', if_true, if_false] <;> first | omega | exact absurd ⟨h0, h1'⟩ hc
    omega
  refine ⟨ha.1, ha.2, fun ha1 hadj => ?_⟩
  have h2 := lemma1 hS hx (a := a - 1) (q := q + 1) (by omega)
  have hs3 := dseg_add (G := G) x f (a - 1) 1 q
  rw [dseg_one, if_pos hadj, show a - 1 + 1 = a by omega, show 1 + q = q + 1 by omega] at hs3
  omega

/- ### Global and start-fixed optimality -/

variable (G) in
/-- A longest square path of `G`, with the most 3-chords, then the most 4-chords. -/
def Opt (s : ℕ) (f : ℕ → V) : Prop :=
  IsSq G s f ∧ ∀ m g, IsSq G m g → m ≤ s ∧ (m = s → chords G s g 3 ≤ chords G s f 3 ∧
    (chords G s g 3 = chords G s f 3 → chords G s g 4 ≤ chords G s f 4))

variable (G) in
/-- Optimal among square paths starting with the ordered edge `f 0, f 1`. -/
def OptStart (s : ℕ) (f : ℕ → V) : Prop :=
  IsSq G s f ∧ ∀ m g, IsSq G m g → g 0 = f 0 → g 1 = f 1 → m ≤ s ∧
    (m = s → chords G s g 3 ≤ chords G s f 3 ∧
      (chords G s g 3 = chords G s f 3 → chords G s g 4 ≤ chords G s f 4))

/- ### Extension by a clique joined to a set `T` -/

variable (G) in
/-- `G` together with `k` new vertices forming a clique, each joined to every vertex of `T`. -/
def ext (T : Finset V) (k : ℕ) : SimpleGraph (V ⊕ Fin k) where
  Adj a b := Sum.elim (fun u => Sum.elim (fun v => G.Adj u v) (fun _ => u ∈ T))
    (fun i => Sum.elim (fun v => v ∈ T) (fun j => i ≠ j)) a b
  symm := ⟨by
    rintro (u | i) (v | j) h
    · exact G.adj_symm h
    · exact h
    · exact h
    · exact Ne.symm h⟩
  loopless := ⟨by
    rintro (u | i) h
    · exact G.loopless.irrefl u h
    · exact h rfl⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma ext_inl_inl {T : Finset V} {k : ℕ} {u v : V} :
    (ext G T k).Adj (Sum.inl u) (Sum.inl v) ↔ G.Adj u v := Iff.rfl
omit [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma ext_inl_inr {T : Finset V} {k : ℕ} {u : V} {j : Fin k} :
    (ext G T k).Adj (Sum.inl u) (Sum.inr j) ↔ u ∈ T := Iff.rfl
omit [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma ext_inr_inl {T : Finset V} {k : ℕ} {v : V} {i : Fin k} :
    (ext G T k).Adj (Sum.inr i) (Sum.inl v) ↔ v ∈ T := Iff.rfl
omit [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma ext_inr_inr {T : Finset V} {k : ℕ} {i j : Fin k} :
    (ext G T k).Adj (Sum.inr i) (Sum.inr j) ↔ i ≠ j := Iff.rfl

instance ext_decRel (T : Finset V) (k : ℕ) : DecidableRel (ext G T k).Adj := by
  rintro (u | i) (v | j)
  · exact decidable_of_iff _ ext_inl_inl.symm
  · exact decidable_of_iff _ ext_inl_inr.symm
  · exact decidable_of_iff _ ext_inr_inl.symm
  · exact decidable_of_iff _ ext_inr_inr.symm

omit [DecidableEq V] in
/-- Splitting the chords of a path into those between two "middle" positions `[c, m-d)` and the
rest. -/
lemma chords_split {W : Type} [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (m c d : ℕ) (hm : c + d ≤ m) (g : ℕ → W) (k : ℕ) (H' : SimpleGraph V) [DecidableRel H'.Adj]
    (h : ℕ → V) (hmid : ∀ i j, i < m - c - d → j < m - c - d →
      (H.Adj (g (i + c)) (g (j + c)) ↔ H'.Adj (h i) (h j))) :
    chords H m g k = chords H' (m - c - d) h k +
      ((range m).filter (fun i => i + k < m ∧ ¬ (c ≤ i ∧ i + k < m - d) ∧
        H.Adj (g i) (g (i + k)))).card := by
  unfold chords
  rw [← card_filter_add_card_filter_not (fun i => c ≤ i ∧ i + k < m - d)]
  congr 1
  · rw [filter_filter]
    apply card_bij (fun i _ => i - c)
    · intro i hi
      simp only [mem_filter, mem_range] at hi ⊢
      refine ⟨by omega, by omega, ?_⟩
      have := (hmid (i - c) (i - c + k) (by omega) (by omega)).1
      rw [show i - c + c = i by omega, show i - c + k + c = i + k by omega] at this
      exact this hi.2.1.2
    · intro i hi j hj hij
      simp only [mem_filter, mem_range] at hi hj
      omega
    · intro j hj
      simp only [mem_filter, mem_range] at hj
      refine ⟨j + c, ?_, by omega⟩
      simp only [mem_filter, mem_range]
      refine ⟨by omega, ⟨by omega, ?_⟩, by omega, by omega⟩
      have := (hmid j (j + k) (by omega) (by omega)).2 hj.2.2
      rw [show j + k + c = j + c + k by omega] at this
      exact this
  · rw [filter_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range]
    tauto

omit [DecidableEq V] in
/-- Every vertex of `G` is a square path of length one, so an optimal path is nonempty. -/
lemma isSq_one (v : V) : IsSq G 1 (fun _ => v) :=
  ⟨fun i hi => by omega, fun i hi => by omega, fun i j hi hj _ => by omega⟩

section Lemma4

variable {s : ℕ} {f : ℕ → V} {x : V}

/-- The path `a1 a2 S a3 a4` in `ext G T 4`. -/
def pad4 (s : ℕ) (f : ℕ → V) : ℕ → V ⊕ Fin 4 := fun i =>
  if i = 0 then Sum.inr 0 else if i = 1 then Sum.inr 1 else if i < s + 2 then Sum.inl (f (i - 2))
  else if i = s + 2 then Sum.inr 2 else Sum.inr 3

omit [DecidableEq V] in
lemma pad4_mid {s : ℕ} {f : ℕ → V} {i : ℕ} (hi : i < s) : pad4 s f (i + 2) = Sum.inl (f i) := by
  unfold pad4
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show i + 2 - 2 = i by omega]

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma pad4_isSq {T : Finset V} (hf : IsSq G s f) (hfT : ∀ i < s, f i ∈ T) :
    IsSq (ext G T 4) (s + 4) (pad4 s f) := by
  refine isSq_of_pairs _ (fun i j hij hj2 hj => ?_) (fun i j hi hj h => ?_)
  · unfold pad4
    split_ifs <;> simp only [ext_inl_inl, ext_inl_inr, ext_inr_inl, ext_inr_inr] <;>
      first
      | decide
      | exact hfT _ (by omega)
      | exact hf.adj_close' (by omega) (by omega) (by omega) (by omega) (by omega)
      | omega
  · unfold pad4 at h
    split_ifs at h <;> simp only [Sum.inl.injEq, Sum.inr.injEq] at h <;>
      first
      | omega
      | (have := hf.inj _ _ (by omega) (by omega) h; omega)

omit [DecidableEq V] in
lemma pad4_end_adj {T : Finset V} (hfT : ∀ i < s, f i ∈ T) {i k : ℕ} (hk : 1 ≤ k)
    (hik : i + k < s + 4) (hend : ¬ (2 ≤ i ∧ i + k < s + 4 - 2)) :
    (ext G T 4).Adj (pad4 s f i) (pad4 s f (i + k)) := by
  unfold pad4
  split_ifs <;> simp only [ext_inl_inl, ext_inl_inr, ext_inr_inl, ext_inr_inr] <;>
    first | decide | exact hfT _ (by omega) | omega

/-- **Lemma 4** (Fan–Kierstead). If `S` is an optimal square path and `x ∉ S`, then
`d(x, S) ≤ (2s-1)/3`. -/
theorem lemma4 (hS : Opt G s f) (hx : ∀ i < s, f i ≠ x) : 3 * dseg G x f 0 s + 1 ≤ 2 * s := by
  classical
  have hs1 : 1 ≤ s := (hS.2 1 _ (isSq_one x)).1
  set T : Finset V := insert x ((range s).image f) with hT
  have hfT : ∀ i < s, f i ∈ T := fun i hi => by
    rw [hT]; exact mem_insert_of_mem (mem_image.2 ⟨i, mem_range.2 hi, rfl⟩)
  have hxT : x ∈ T := by rw [hT]; exact mem_insert_self _ _
  set G' := ext G T 4 with hG'
  have hP := pad4_isSq (G := G) hS.1 hfT
  -- `pad4 s f` is optimal among paths with its end edges
  have hopt : OptFix G' (s + 4) (pad4 s f) := by
    refine ⟨hP, fun m g hg hends => ?_⟩
    obtain ⟨e0, e1, e2, e3⟩ := hends
    have p0 : pad4 s f 0 = Sum.inr 0 := by unfold pad4; rw [if_pos rfl]
    have p1 : pad4 s f 1 = Sum.inr 1 := by unfold pad4; rw [if_neg (by omega), if_pos rfl]
    have p2 : pad4 s f (s + 4 - 2) = Sum.inr 2 := by
      unfold pad4; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    have p3 : pad4 s f (s + 4 - 1) = Sum.inr 3 := by
      unfold pad4
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [p0] at e0
    rw [p1] at e1
    rw [p2] at e2
    rw [p3] at e3
    have hm4 : 4 ≤ m := by
      by_contra hc
      interval_cases m <;> simp_all
    -- the middle of `g` lies in `V`
    have hmid : ∀ i, 2 ≤ i → i < m - 2 → ∃ v, g i = Sum.inl v := by
      intro i h1 h2
      rcases hgi : g i with v | j
      · exact ⟨v, rfl⟩
      · exfalso
        fin_cases j
        · have := hg.inj i 0 (by omega) (by omega) (by rw [hgi, e0]; rfl); omega
        · have := hg.inj i 1 (by omega) (by omega) (by rw [hgi, e1]; rfl); omega
        · have := hg.inj i (m - 2) (by omega) (by omega) (by rw [hgi, e2]; rfl); omega
        · have := hg.inj i (m - 1) (by omega) (by omega) (by rw [hgi, e3]; rfl); omega
    let h : ℕ → V := fun i => Sum.elim id (fun _ => x) (g (i + 2))
    have hgh : ∀ i, i < m - 4 → g (i + 2) = Sum.inl (h i) := by
      intro i hi
      obtain ⟨v, hv⟩ := hmid (i + 2) (by omega) (by omega)
      simp only [h, hv, Sum.elim_inl, id]
    have hh : IsSq G (m - 4) h := by
      refine isSq_of_pairs _ (fun i j hij hj2 hj => ?_) (fun i j hi hj hij => ?_)
      · have := hg.adj_close (a := i + 2) (b := j + 2) (by omega) (by omega) (by omega) (by omega)
        rw [hgh i (by omega), hgh j hj] at this
        exact this
      · have := hg.inj (i + 2) (j + 2) (by omega) (by omega)
          (by rw [hgh i hi, hgh j hj, hij])
        omega
    obtain ⟨hle, hch⟩ := hS.2 (m - 4) h hh
    refine ⟨by omega, fun hm => ?_⟩
    subst hm
    have hmidg : ∀ i j, i < s + 4 - 2 - 2 → j < s + 4 - 2 - 2 →
        (G'.Adj (g (i + 2)) (g (j + 2)) ↔ G.Adj (h i) (h j)) := by
      intro i j hi hj
      rw [hgh i (by omega), hgh j (by omega)]
      exact ext_inl_inl
    have hmidP : ∀ i j, i < s + 4 - 2 - 2 → j < s + 4 - 2 - 2 →
        (G'.Adj (pad4 s f (i + 2)) (pad4 s f (j + 2)) ↔ G.Adj (f i) (f j)) := by
      intro i j hi hj
      rw [pad4_mid (by omega), pad4_mid (by omega)]
      exact ext_inl_inl
    have hsplit : ∀ k, chords G' (s + 4) g k = chords G s h k +
        ((range (s + 4)).filter (fun i => i + k < s + 4 ∧ ¬ (2 ≤ i ∧ i + k < s + 4 - 2) ∧
          G'.Adj (g i) (g (i + k)))).card := by
      intro k
      have := chords_split G' (s + 4) 2 2 (by omega) g k G h hmidg
      rwa [show s + 4 - 2 - 2 = s by omega] at this
    have hsplitP : ∀ k, 1 ≤ k → chords G' (s + 4) (pad4 s f) k = chords G s f k +
        ((range (s + 4)).filter (fun i => i + k < s + 4 ∧ ¬ (2 ≤ i ∧ i + k < s + 4 - 2))).card := by
      intro k hk
      have := chords_split G' (s + 4) 2 2 (by omega) (pad4 s f) k G f hmidP
      rw [show s + 4 - 2 - 2 = s by omega] at this
      rw [this]
      congr 2
      ext i
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨h1, h2, h3, -⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, h3, pad4_end_adj hfT hk h2 h3⟩
    have d3 := hsplitP 3 (by norm_num)
    have d4 := hsplitP 4 (by norm_num)
    have c3 := hsplit 3
    have c4 := hsplit 4
    have le : ∀ k, ((range (s + 4)).filter (fun i => i + k < s + 4 ∧ ¬ (2 ≤ i ∧ i + k < s + 4 - 2) ∧
          G'.Adj (g i) (g (i + k)))).card ≤
        ((range (s + 4)).filter (fun i => i + k < s + 4 ∧ ¬ (2 ≤ i ∧ i + k < s + 4 - 2))).card := by
      intro k
      apply card_le_card
      intro i
      simp only [mem_filter, mem_range]
      tauto
    have le3 := le 3
    have le4 := le 4
    obtain ⟨hc3, hc4⟩ := hch (by omega)
    refine ⟨by omega, fun heq => ?_⟩
    have := hc4 (by omega)
    omega
  -- apply Lemma 1 to the padded path
  have hxP : ∀ i < s + 4, pad4 s f i ≠ Sum.inl x := by
    intro i hi
    unfold pad4
    split_ifs <;> simp only [ne_eq, Sum.inl.injEq, reduceCtorEq, not_false_eq_true]
    exact hx _ (by omega)
  have L1 := lemma1 hopt hxP (a := 0) (q := s + 4) (by omega)
  have hd1 := dseg_add (G := G') (Sum.inl x) (pad4 s f) 0 2 (s + 2)
  have hd2 := dseg_add (G := G') (Sum.inl x) (pad4 s f) (0 + 2) s 2
  have hd3 := dseg_add (G := G') (Sum.inl x) (pad4 s f) 0 1 1
  have hd4 := dseg_add (G := G') (Sum.inl x) (pad4 s f) (0 + 2 + s) 1 1
  rw [dseg_one, dseg_one, show (1 : ℕ) + 1 = 2 from rfl] at hd3 hd4
  have q0 : pad4 s f 0 = Sum.inr 0 := by unfold pad4; rw [if_pos rfl]
  have q1 : pad4 s f (0 + 1) = Sum.inr 1 := by unfold pad4; rw [if_neg (by omega), if_pos rfl]
  have q2 : pad4 s f (0 + 2 + s) = Sum.inr 2 := by
    unfold pad4; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have q3 : pad4 s f (0 + 2 + s + 1) = Sum.inr 3 := by
    unfold pad4
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [q0, q1, if_pos (ext_inl_inr.2 hxT), if_pos (ext_inl_inr.2 hxT)] at hd3
  rw [q2, q3, if_pos (ext_inl_inr.2 hxT), if_pos (ext_inl_inr.2 hxT)] at hd4
  have hmid : dseg G' (Sum.inl x) (pad4 s f) (0 + 2) s = dseg G x f 0 s := by
    unfold dseg
    apply card_bij (fun i _ => i - 2)
    · intro i hi
      simp only [mem_filter, mem_Ico] at hi ⊢
      refine ⟨by omega, ?_⟩
      have := hi.2
      rw [show i = (i - 2) + 2 by omega, pad4_mid (by omega)] at this
      exact this
    · intro i hi j hj hij
      simp only [mem_filter, mem_Ico] at hi hj
      omega
    · intro j hj
      simp only [mem_filter, mem_Ico] at hj
      refine ⟨j + 2, ?_, by omega⟩
      simp only [mem_filter, mem_Ico]
      refine ⟨by omega, ?_⟩
      rw [pad4_mid (by omega)]
      exact hj.2
  rw [show 2 + (s + 2) = s + 4 by omega] at hd1
  rw [show s + 2 = s + 2 from rfl] at hd2
  simp only [Nat.zero_add] at hd1 hd2 hd3 hd4 hmid
  omega

lemma pad4_optFix {s : ℕ} {f : ℕ → V} (hS : Opt G s f) (x : V) (T : Finset V)
    (hfT : ∀ i < s, f i ∈ T) : OptFix (ext G T 4) (s + 4) (pad4 s f) := by
  have hP := pad4_isSq (G := G) hS.1 hfT
  refine ⟨hP, fun m g hg hends => ?_⟩
  obtain ⟨e0, e1, e2, e3⟩ := hends
  have p0 : pad4 s f 0 = Sum.inr 0 := by unfold pad4; rw [if_pos rfl]
  have p1 : pad4 s f 1 = Sum.inr 1 := by unfold pad4; rw [if_neg (by omega), if_pos rfl]
  have p2 : pad4 s f (s + 4 - 2) = Sum.inr 2 := by
    unfold pad4; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have p3 : pad4 s f (s + 4 - 1) = Sum.inr 3 := by
    unfold pad4
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [p0] at e0
  rw [p1] at e1
  rw [p2] at e2
  rw [p3] at e3
  have hm4 : 4 ≤ m := by
    by_contra hc
    interval_cases m <;> simp_all
  -- the middle of `g` lies in `V`
  have hmid : ∀ i, 2 ≤ i → i < m - 2 → ∃ v, g i = Sum.inl v := by
    intro i h1 h2
    rcases hgi : g i with v | j
    · exact ⟨v, rfl⟩
    · exfalso
      fin_cases j
      · have := hg.inj i 0 (by omega) (by omega) (by rw [hgi, e0]; rfl); omega
      · have := hg.inj i 1 (by omega) (by omega) (by rw [hgi, e1]; rfl); omega
      · have := hg.inj i (m - 2) (by omega) (by omega) (by rw [hgi, e2]; rfl); omega
      · have := hg.inj i (m - 1) (by omega) (by omega) (by rw [hgi, e3]; rfl); omega
  let h : ℕ → V := fun i => Sum.elim id (fun _ => x) (g (i + 2))
  have hgh : ∀ i, i < m - 4 → g (i + 2) = Sum.inl (h i) := by
    intro i hi
    obtain ⟨v, hv⟩ := hmid (i + 2) (by omega) (by omega)
    simp only [h, hv, Sum.elim_inl, id]
  have hh : IsSq G (m - 4) h := by
    refine isSq_of_pairs _ (fun i j hij hj2 hj => ?_) (fun i j hi hj hij => ?_)
    · have := hg.adj_close (a := i + 2) (b := j + 2) (by omega) (by omega) (by omega) (by omega)
      rw [hgh i (by omega), hgh j hj] at this
      exact this
    · have := hg.inj (i + 2) (j + 2) (by omega) (by omega)
        (by rw [hgh i hi, hgh j hj, hij])
      omega
  obtain ⟨hle, hch⟩ := hS.2 (m - 4) h hh
  refine ⟨by omega, fun hm => ?_⟩
  subst hm
  have hmidg : ∀ i j, i < s + 4 - 2 - 2 → j < s + 4 - 2 - 2 →
      ((ext G T 4).Adj (g (i + 2)) (g (j + 2)) ↔ G.Adj (h i) (h j)) := by
    intro i j hi hj
    rw [hgh i (by omega), hgh j (by omega)]
    exact ext_inl_inl
  have hmidP : ∀ i j, i < s + 4 - 2 - 2 → j < s + 4 - 2 - 2 →
      ((ext G T 4).Adj (pad4 s f (i + 2)) (pad4 s f (j + 2)) ↔ G.Adj (f i) (f j)) := by
    intro i j hi hj
    rw [pad4_mid (by omega), pad4_mid (by omega)]
    exact ext_inl_inl
  have hsplit : ∀ k, chords (ext G T 4) (s + 4) g k = chords G s h k +
      ((range (s + 4)).filter (fun i => i + k < s + 4 ∧ ¬ (2 ≤ i ∧ i + k < s + 4 - 2) ∧
        (ext G T 4).Adj (g i) (g (i + k)))).card := by
    intro k
    have := chords_split (ext G T 4) (s + 4) 2 2 (by omega) g k G h hmidg
    rwa [show s + 4 - 2 - 2 = s by omega] at this
  have hsplitP : ∀ k, 1 ≤ k → chords (ext G T 4) (s + 4) (pad4 s f) k = chords G s f k +
      ((range (s + 4)).filter (fun i => i + k < s + 4 ∧ ¬ (2 ≤ i ∧ i + k < s + 4 - 2))).card := by
    intro k hk
    have := chords_split (ext G T 4) (s + 4) 2 2 (by omega) (pad4 s f) k G f hmidP
    rw [show s + 4 - 2 - 2 = s by omega] at this
    rw [this]
    congr 2
    ext i
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨h1, h2, h3, -⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, h3, pad4_end_adj hfT hk h2 h3⟩
  have d3 := hsplitP 3 (by norm_num)
  have d4 := hsplitP 4 (by norm_num)
  have c3 := hsplit 3
  have c4 := hsplit 4
  have le : ∀ k, ((range (s + 4)).filter (fun i => i + k < s + 4 ∧ ¬ (2 ≤ i ∧ i + k < s + 4 - 2) ∧
        (ext G T 4).Adj (g i) (g (i + k)))).card ≤
      ((range (s + 4)).filter (fun i => i + k < s + 4 ∧ ¬ (2 ≤ i ∧ i + k < s + 4 - 2))).card := by
    intro k
    apply card_le_card
    intro i
    simp only [mem_filter, mem_range]
    tauto
  have le3 := le 3
  have le4 := le 4
  obtain ⟨hc3, hc4⟩ := hch (by omega)
  refine ⟨by omega, fun heq => ?_⟩
  have := hc4 (by omega)
  omega

lemma pad4_dseg {s : ℕ} {f : ℕ → V} (T : Finset V) {x : V} (hxT : x ∈ T) :
    dseg (ext G T 4) (Sum.inl x) (pad4 s f) 0 (s + 4) = dseg G x f 0 s + 4 := by
  have hd1 := dseg_add (G := (ext G T 4)) (Sum.inl x) (pad4 s f) 0 2 (s + 2)
  have hd2 := dseg_add (G := (ext G T 4)) (Sum.inl x) (pad4 s f) (0 + 2) s 2
  have hd3 := dseg_add (G := (ext G T 4)) (Sum.inl x) (pad4 s f) 0 1 1
  have hd4 := dseg_add (G := (ext G T 4)) (Sum.inl x) (pad4 s f) (0 + 2 + s) 1 1
  rw [dseg_one, dseg_one, show (1 : ℕ) + 1 = 2 from rfl] at hd3 hd4
  have q0 : pad4 s f 0 = Sum.inr 0 := by unfold pad4; rw [if_pos rfl]
  have q1 : pad4 s f (0 + 1) = Sum.inr 1 := by unfold pad4; rw [if_neg (by omega), if_pos rfl]
  have q2 : pad4 s f (0 + 2 + s) = Sum.inr 2 := by
    unfold pad4; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have q3 : pad4 s f (0 + 2 + s + 1) = Sum.inr 3 := by
    unfold pad4
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [q0, q1, if_pos (ext_inl_inr.2 hxT), if_pos (ext_inl_inr.2 hxT)] at hd3
  rw [q2, q3, if_pos (ext_inl_inr.2 hxT), if_pos (ext_inl_inr.2 hxT)] at hd4
  have hmid : dseg (ext G T 4) (Sum.inl x) (pad4 s f) (0 + 2) s = dseg G x f 0 s := by
    unfold dseg
    apply card_bij (fun i _ => i - 2)
    · intro i hi
      simp only [mem_filter, mem_Ico] at hi ⊢
      refine ⟨by omega, ?_⟩
      have := hi.2
      rw [show i = (i - 2) + 2 by omega, pad4_mid (by omega)] at this
      exact this
    · intro i hi j hj hij
      simp only [mem_filter, mem_Ico] at hi hj
      omega
    · intro j hj
      simp only [mem_filter, mem_Ico] at hj
      refine ⟨j + 2, ?_, by omega⟩
      simp only [mem_filter, mem_Ico]
      refine ⟨by omega, ?_⟩
      rw [pad4_mid (by omega)]
      exact hj.2
  rw [show 2 + (s + 2) = s + 4 by omega] at hd1
  rw [show s + 2 = s + 2 from rfl] at hd2
  simp only [Nat.zero_add] at hd1 hd2 hd3 hd4 hmid
  omega

end Lemma4

section Lemma3

variable {s : ℕ} {f : ℕ → V} {x : V}

/-- The path `S a b` in `ext G T 2`. -/
def pad2 (s : ℕ) (f : ℕ → V) : ℕ → V ⊕ Fin 2 := fun i =>
  if i < s then Sum.inl (f i) else if i = s then Sum.inr 0 else Sum.inr 1

omit [DecidableEq V] in
lemma pad2_mid {i : ℕ} (hi : i < s) : pad2 s f i = Sum.inl (f i) := by
  unfold pad2; rw [if_pos hi]

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma pad2_isSq {T : Finset V} (hf : IsSq G s f) (hfT : ∀ i < s, f i ∈ T) :
    IsSq (ext G T 2) (s + 2) (pad2 s f) := by
  refine isSq_of_pairs _ (fun i j hij hj2 hj => ?_) (fun i j hi hj h => ?_)
  · unfold pad2
    split_ifs <;> simp only [ext_inl_inl, ext_inl_inr, ext_inr_inl, ext_inr_inr] <;>
      first
      | decide
      | exact hfT _ (by omega)
      | exact hf.adj_close' (by omega) (by omega) (by omega) (by omega) (by omega)
      | omega
  · unfold pad2 at h
    split_ifs at h <;> simp only [Sum.inl.injEq, Sum.inr.injEq] at h <;>
      first
      | omega
      | (have := hf.inj _ _ (by omega) (by omega) h; omega)

omit [DecidableEq V] in
lemma pad2_end_adj {T : Finset V} (hfT : ∀ i < s, f i ∈ T) {i k : ℕ} (hk : 1 ≤ k)
    (hik : i + k < s + 2) (hend : ¬ (0 ≤ i ∧ i + k < s + 2 - 2)) :
    (ext G T 2).Adj (pad2 s f i) (pad2 s f (i + k)) := by
  unfold pad2
  split_ifs <;> simp only [ext_inl_inl, ext_inl_inr, ext_inr_inl, ext_inr_inr] <;>
    first | decide | exact hfT _ (by omega) | omega

/-- **Lemma 3** (Fan–Kierstead). If `S` is optimal among square paths starting at its first
ordered edge and `x ∉ S`, then `d(x, S) ≤ (2s+1)/3`. -/
theorem lemma3 (hS : OptStart G s f) (hs : 2 ≤ s) (hx : ∀ i < s, f i ≠ x) :
    3 * dseg G x f 0 s ≤ 2 * s + 1 := by
  classical
  set T : Finset V := insert x ((range s).image f) with hT
  have hfT : ∀ i < s, f i ∈ T := fun i hi => by
    rw [hT]; exact mem_insert_of_mem (mem_image.2 ⟨i, mem_range.2 hi, rfl⟩)
  have hxT : x ∈ T := by rw [hT]; exact mem_insert_self _ _
  set G' := ext G T 2 with hG'
  have hP := pad2_isSq (G := G) hS.1 hfT
  have hopt : OptFix G' (s + 2) (pad2 s f) := by
    refine ⟨hP, fun m g hg hends => ?_⟩
    obtain ⟨e0, e1, e2, e3⟩ := hends
    have p0 : pad2 s f 0 = Sum.inl (f 0) := pad2_mid (by omega)
    have p1 : pad2 s f 1 = Sum.inl (f 1) := pad2_mid (by omega)
    have p2 : pad2 s f (s + 2 - 2) = Sum.inr 0 := by
      unfold pad2; rw [if_neg (by omega), if_pos (by omega)]
    have p3 : pad2 s f (s + 2 - 1) = Sum.inr 1 := by
      unfold pad2; rw [if_neg (by omega), if_neg (by omega)]
    rw [p0] at e0
    rw [p1] at e1
    rw [p2] at e2
    rw [p3] at e3
    have hm4 : 4 ≤ m := by
      by_contra hc
      interval_cases m <;> simp_all
    have hmid : ∀ i, i < m - 2 → ∃ v, g i = Sum.inl v := by
      intro i h2
      rcases hgi : g i with v | j
      · exact ⟨v, rfl⟩
      · exfalso
        fin_cases j
        · have := hg.inj i (m - 2) (by omega) (by omega) (by rw [hgi, e2]; rfl); omega
        · have := hg.inj i (m - 1) (by omega) (by omega) (by rw [hgi, e3]; rfl); omega
    let h : ℕ → V := fun i => Sum.elim id (fun _ => x) (g i)
    have hgh : ∀ i, i < m - 2 → g i = Sum.inl (h i) := by
      intro i hi
      obtain ⟨v, hv⟩ := hmid i hi
      simp only [h, hv, Sum.elim_inl, id]
    have hh : IsSq G (m - 2) h := by
      refine isSq_of_pairs _ (fun i j hij hj2 hj => ?_) (fun i j hi hj hij => ?_)
      · have := hg.adj_close (a := i) (b := j) (by omega) (by omega) (by omega) (by omega)
        rw [hgh i (by omega), hgh j hj] at this
        exact this
      · exact hg.inj i j (by omega) (by omega) (by rw [hgh i hi, hgh j hj, hij])
    have h0 : h 0 = f 0 := by
      have := hgh 0 (by omega); rw [e0] at this; exact (Sum.inl.inj this).symm
    have h1 : h 1 = f 1 := by
      have := hgh 1 (by omega); rw [e1] at this; exact (Sum.inl.inj this).symm
    obtain ⟨hle, hch⟩ := hS.2 (m - 2) h hh h0 h1
    refine ⟨by omega, fun hm => ?_⟩
    subst hm
    have hmidg : ∀ i j, i < s + 2 - 0 - 2 → j < s + 2 - 0 - 2 →
        (G'.Adj (g (i + 0)) (g (j + 0)) ↔ G.Adj (h i) (h j)) := by
      intro i j hi hj
      rw [Nat.add_zero, Nat.add_zero, hgh i (by omega), hgh j (by omega)]
      exact ext_inl_inl
    have hmidP : ∀ i j, i < s + 2 - 0 - 2 → j < s + 2 - 0 - 2 →
        (G'.Adj (pad2 s f (i + 0)) (pad2 s f (j + 0)) ↔ G.Adj (f i) (f j)) := by
      intro i j hi hj
      rw [Nat.add_zero, Nat.add_zero, pad2_mid (by omega), pad2_mid (by omega)]
      exact ext_inl_inl
    have hsplit : ∀ k, chords G' (s + 2) g k = chords G s h k +
        ((range (s + 2)).filter (fun i => i + k < s + 2 ∧ ¬ (0 ≤ i ∧ i + k < s + 2 - 2) ∧
          G'.Adj (g i) (g (i + k)))).card := by
      intro k
      have := chords_split G' (s + 2) 0 2 (by omega) g k G h hmidg
      rwa [show s + 2 - 0 - 2 = s by omega] at this
    have hsplitP : ∀ k, 1 ≤ k → chords G' (s + 2) (pad2 s f) k = chords G s f k +
        ((range (s + 2)).filter (fun i => i + k < s + 2 ∧ ¬ (0 ≤ i ∧ i + k < s + 2 - 2))).card := by
      intro k hk
      have := chords_split G' (s + 2) 0 2 (by omega) (pad2 s f) k G f hmidP
      rw [show s + 2 - 0 - 2 = s by omega] at this
      rw [this]
      congr 2
      ext i
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨h1, h2, h3, -⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, h3, pad2_end_adj hfT hk h2 h3⟩
    have d3 := hsplitP 3 (by norm_num)
    have d4 := hsplitP 4 (by norm_num)
    have c3 := hsplit 3
    have c4 := hsplit 4
    have le : ∀ k, ((range (s + 2)).filter (fun i => i + k < s + 2 ∧ ¬ (0 ≤ i ∧ i + k < s + 2 - 2) ∧
          G'.Adj (g i) (g (i + k)))).card ≤
        ((range (s + 2)).filter (fun i => i + k < s + 2 ∧ ¬ (0 ≤ i ∧ i + k < s + 2 - 2))).card := by
      intro k
      apply card_le_card
      intro i
      simp only [mem_filter, mem_range]
      tauto
    have le3 := le 3
    have le4 := le 4
    obtain ⟨hc3, hc4⟩ := hch (by omega)
    refine ⟨by omega, fun heq => ?_⟩
    have := hc4 (by omega)
    omega
  have hxP : ∀ i < s + 2, pad2 s f i ≠ Sum.inl x := by
    intro i hi
    unfold pad2
    split_ifs <;> simp only [ne_eq, Sum.inl.injEq, reduceCtorEq, not_false_eq_true]
    exact hx _ (by omega)
  have L1 := lemma1 hopt hxP (a := 0) (q := s + 2) (by omega)
  have hd1 := dseg_add (G := G') (Sum.inl x) (pad2 s f) 0 s 2
  have hd4 := dseg_add (G := G') (Sum.inl x) (pad2 s f) (0 + s) 1 1
  rw [dseg_one, dseg_one, show (1 : ℕ) + 1 = 2 from rfl] at hd4
  have q2 : pad2 s f (0 + s) = Sum.inr 0 := by
    unfold pad2; rw [if_neg (by omega), if_pos (by omega)]
  have q3 : pad2 s f (0 + s + 1) = Sum.inr 1 := by
    unfold pad2; rw [if_neg (by omega), if_neg (by omega)]
  rw [q2, q3, if_pos (ext_inl_inr.2 hxT), if_pos (ext_inl_inr.2 hxT)] at hd4
  have hmid : dseg G' (Sum.inl x) (pad2 s f) 0 s = dseg G x f 0 s := by
    unfold dseg
    congr 1
    ext i
    simp only [mem_filter, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩; rw [pad2_mid (by omega)] at h2; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; rw [pad2_mid (by omega)]; exact ⟨h1, h2⟩
  simp only [Nat.zero_add] at hd1 hd4 hmid
  omega

end Lemma3

/- ### Concatenation, prefixes, cube paths (Lemma 7) -/

/-- `A 0 … A (a-1)` followed by `B 0, B 1, …`. -/
def cat (a : ℕ) (A B : ℕ → V) : ℕ → V := fun i => if i < a then A i else B (i - a)

omit [DecidableEq V] in
lemma isSq_cat {a b : ℕ} {A B : ℕ → V} (hA : IsSq G a A) (hB : IsSq G b B)
    (hdisj : ∀ i < a, ∀ j < b, A i ≠ B j)
    (j1 : 1 ≤ a → 1 ≤ b → G.Adj (A (a - 1)) (B 0))
    (j2 : 2 ≤ a → 1 ≤ b → G.Adj (A (a - 2)) (B 0))
    (j3 : 1 ≤ a → 2 ≤ b → G.Adj (A (a - 1)) (B 1)) : IsSq G (a + b) (cat a A B) := by
  refine isSq_of_pairs _ (fun i j hij hj2 hj => ?_) (fun i j hi hj h => ?_)
  · unfold cat
    by_cases hi : i < a <;> by_cases hj' : j < a
    · rw [if_pos hi, if_pos hj']; exact hA.adj_close hi hj' hij hj2
    · rw [if_pos hi, if_neg hj']
      have : (i + 1 = a ∧ j = a) ∨ (i + 2 = a ∧ j = a) ∨ (i + 1 = a ∧ j = a + 1) := by omega
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [show i = a - 1 by omega, h2, Nat.sub_self]; exact j1 (by omega) (by omega)
      · rw [show i = a - 2 by omega, h2, Nat.sub_self]; exact j2 (by omega) (by omega)
      · rw [show i = a - 1 by omega, h2, show a + 1 - a = 1 by omega]
        exact j3 (by omega) (by omega)
    · omega
    · rw [if_neg hi, if_neg hj']
      exact hB.adj_close (by omega) (by omega) (by omega) (by omega)
  · unfold cat at h
    by_cases hi' : i < a <;> by_cases hj' : j < a <;> simp only [hi', hj', if_true, if_false] at h
    · exact hA.inj i j hi' hj' h
    · exact absurd h (hdisj i hi' (j - a) (by omega))
    · exact absurd h.symm (hdisj j hj' (i - a) (by omega))
    · have := hB.inj _ _ (by omega) (by omega) h; omega

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma IsSq.take {n m : ℕ} {f : ℕ → V} (h : IsSq G n f) (hm : m ≤ n) : IsSq G m f :=
  ⟨fun i hi => h.adj1 i (by omega), fun i hi => h.adj2 i (by omega),
    fun i j hi hj => h.inj i j (by omega) (by omega)⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma IsSq.shift {n : ℕ} {f : ℕ → V} (h : IsSq G n f) (a : ℕ) :
    IsSq G (n - a) (fun i => f (a + i)) :=
  ⟨fun i hi => by have := h.adj1 (a + i) (by omega); rwa [show a + i + 1 = a + (i + 1) by omega] at this,
   fun i hi => by have := h.adj2 (a + i) (by omega); rwa [show a + i + 2 = a + (i + 2) by omega] at this,
   fun i j hi hj hh => by have := h.inj (a + i) (a + j) (by omega) (by omega) hh; omega⟩

variable (G) in
/-- `f 0, …, f (n-1)` is a cube path (third power of a path). -/
structure IsCube (n : ℕ) (f : ℕ → V) : Prop where
  adj : ∀ i j, i < j → j ≤ i + 3 → j < n → G.Adj (f i) (f j)
  inj : ∀ i j, i < n → j < n → f i = f j → i = j

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma IsCube.isSq {n : ℕ} {f : ℕ → V} (h : IsCube G n f) : IsSq G n f :=
  isSq_of_pairs f (fun i j hij hj2 hj => h.adj i j hij (by omega) hj) h.inj

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Reading a cube path through an index map that moves neighbours at most three apart. -/
lemma IsCube.isSq_comp {n m : ℕ} {f : ℕ → V} (h : IsCube G n f) (π : ℕ → ℕ)
    (hπ : ∀ i < m, π i < n)
    (hπinj : ∀ i j, i < m → j < m → π i = π j → i = j)
    (hclose : ∀ i j, i < j → j ≤ i + 2 → j < m → π i ≤ π j + 3 ∧ π j ≤ π i + 3) :
    IsSq G m (fun i => f (π i)) := by
  refine isSq_of_pairs _ (fun i j hij hj2 hj => ?_) (fun i j hi hj hh => ?_)
  · have hne : π i ≠ π j := fun he => by have := hπinj i j (by omega) hj he; omega
    obtain ⟨c1, c2⟩ := hclose i j hij hj2 hj
    rcases Nat.lt_or_gt_of_ne hne with hl | hl
    · exact h.adj _ _ hl (by omega) (hπ j hj)
    · exact (h.adj _ _ hl (by omega) (hπ i (by omega))).symm
  · exact hπinj i j hi hj (h.inj _ _ (hπ i hi) (hπ j hj) hh)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Reading a square path through an index map moving neighbours at most two apart. -/
lemma IsSq.isSq_comp_close {n m : ℕ} {f : ℕ → V} (h : IsSq G n f) (π : ℕ → ℕ)
    (hπ : ∀ i < m, π i < n)
    (hπinj : ∀ i j, i < m → j < m → π i = π j → i = j)
    (hclose : ∀ i j, i < j → j ≤ i + 2 → j < m → π i ≤ π j + 2 ∧ π j ≤ π i + 2) :
    IsSq G m (fun i => f (π i)) := by
  refine isSq_of_pairs _ (fun i j hij hj2 hj => ?_) (fun i j hi hj hh => ?_)
  · have hne : π i ≠ π j := fun he => by have := hπinj i j (by omega) hj he; omega
    obtain ⟨c1, c2⟩ := hclose i j hij hj2 hj
    exact h.adj_close' (hπ i (by omega)) (hπ j hj) hne c1 c2
  · exact hπinj i j hi hj (h.inj _ _ (hπ i hi) (hπ j hj) hh)

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma IsCube.rev {n : ℕ} {f : ℕ → V} (h : IsCube G n f) : IsCube G n (rev n f) :=
  ⟨fun i j hij hj3 hj => (h.adj _ _ (by omega) (by omega) (by omega)).symm,
   fun i j hi hj hh => by have := h.inj _ _ (by omega) (by omega) hh; omega⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **Lemma 7** (Fan–Kierstead): square paths with the vertex set of a cube path `c`, starting at
`c1 c0`, `c0 c2`, `c2 c0` (all `p` vertices). -/
lemma lemma7_swap01 {p : ℕ} {c : ℕ → V} (h : IsCube G p c) (hp : 2 ≤ p) :
    IsSq G p (fun i => c (if i = 0 then 1 else if i = 1 then 0 else i)) :=
  h.isSq_comp _ (fun i hi => by split_ifs <;> omega)
    (fun i j hi hj hh => by split_ifs at hh <;> omega)
    (fun i j hij hj2 hj => by split_ifs <;> omega)

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma lemma7_swap12 {p : ℕ} {c : ℕ → V} (h : IsCube G p c) (hp : 3 ≤ p) :
    IsSq G p (fun i => c (if i = 1 then 2 else if i = 2 then 1 else i)) :=
  h.isSq_comp _ (fun i hi => by split_ifs <;> omega)
    (fun i j hi hj hh => by split_ifs at hh <;> omega)
    (fun i j hij hj2 hj => by split_ifs <;> omega)

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma lemma7_rot {p : ℕ} {c : ℕ → V} (h : IsCube G p c) (hp : 3 ≤ p) :
    IsSq G p (fun i => c (if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 1 else i)) :=
  h.isSq_comp _ (fun i hi => by split_ifs <;> omega)
    (fun i j hi hj hh => by split_ifs at hh <;> omega)
    (fun i j hij hj2 hj => by split_ifs <;> omega)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Square paths on `c1, …, c(p-1)` starting at `c1 c2` and at `c2 c1`. -/
lemma lemma7_drop {p : ℕ} {c : ℕ → V} (h : IsCube G p c) :
    IsSq G (p - 1) (fun i => c (i + 1)) :=
  h.isSq_comp _ (fun i hi => by omega) (fun i j hi hj hh => by omega)
    (fun i j hij hj2 hj => by omega)

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma lemma7_dropswap {p : ℕ} {c : ℕ → V} (h : IsCube G p c) (hp : 3 ≤ p) :
    IsSq G (p - 1) (fun i => c (if i = 0 then 2 else if i = 1 then 1 else i + 1)) :=
  h.isSq_comp _ (fun i hi => by split_ifs <;> omega)
    (fun i j hi hj hh => by split_ifs at hh <;> omega)
    (fun i j hij hj2 hj => by split_ifs <;> omega)

/- ### Lemma 8 -/

/-- One-sided pairing count: a `2` is always followed by a `0`. -/
lemma one_sided (c : ℕ → ℕ) (hc : ∀ i, c i ≤ 2) :
    ∀ L, (∀ i < L, c i = 2 → c (i + 1) = 0) →
      ∑ i ∈ range (L + 1), c i ≤ L + 1 + (if c L = 2 then 1 else 0) := by
  intro L
  induction L with
  | zero =>
    intro _
    simp only [zero_add, range_one, sum_singleton]
    have := hc 0
    split_ifs <;> omega
  | succ L ih =>
    intro h
    rw [sum_range_succ]
    have ih' := ih (fun i hi => h i (by omega))
    have hcL := hc (L + 1)
    by_cases h2 : c L = 2
    · have := h L (by omega) h2
      rw [if_pos h2] at ih'
      split_ifs <;> omega
    · rw [if_neg h2] at ih'
      split_ifs <;> omega

/-- **Lemma 8** (counting form). -/
lemma lemma8_count (c : ℕ → ℕ) (hc : ∀ i, c i ≤ 2) (s : ℕ)
    (h1 : ∀ i, i < s / 2 → c i = 2 → c (i + 1) = 0)
    (h2 : ∀ i, s / 2 < i → i < s → c i = 2 → c (i - 1) = 0) :
    ∑ i ∈ range s, c i ≤ s + 1 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  set M := s / 2 with hM
  have L1 := one_sided c hc M (fun i hi h => h1 i hi h)
  -- the right half, read backwards
  let c' : ℕ → ℕ := fun j => c (s - 1 - j)
  have L2 := one_sided c' (fun i => hc _) (s - 1 - M) (fun j hj h => by
    have := h2 (s - 1 - j) (by omega) (by omega) h
    simp only [c']
    rwa [show s - 1 - (j + 1) = s - 1 - j - 1 by omega])
  have hsplit : ∑ i ∈ range s, c i + c M = ∑ i ∈ range (M + 1), c i + ∑ j ∈ range (s - 1 - M + 1), c' j := by
    have e1 : ∑ i ∈ range s, c i = ∑ i ∈ range (M + 1), c i + ∑ i ∈ Ico (M + 1) s, c i := by
      rw [sum_range_add_sum_Ico _ (by omega)]
    have e2 : ∑ j ∈ range (s - 1 - M + 1), c' j = ∑ i ∈ Ico M s, c i := by
      rw [sum_bij (fun j _ => s - 1 - j)]
      · intro j hj; simp only [mem_range] at hj; simp only [mem_Ico]; omega
      · intro j hj j' hj' h; simp only [mem_range] at hj hj'; omega
      · intro i hi; simp only [mem_Ico] at hi
        exact ⟨s - 1 - i, by simp only [mem_range]; omega, by omega⟩
      · intro j hj; rfl
    have e3 : ∑ i ∈ Ico M s, c i = c M + ∑ i ∈ Ico (M + 1) s, c i := by
      rw [sum_eq_sum_Ico_succ_bot (by omega)]
    rw [e1, e2, e3]; ring
  have hcM : c' (s - 1 - M) = c M := by simp only [c']; congr 1; omega
  rw [hcM] at L2
  have := hc M
  split_ifs at L1 L2 <;> omega

/- ### Lemma 9 -/

omit [DecidableEq V] in
lemma Opt.optFix {s : ℕ} {f : ℕ → V} (h : Opt G s f) : OptFix G s f :=
  ⟨h.1, fun m g hg _ => h.2 m g hg⟩

omit [DecidableEq V] in
lemma dseg_eq_sum (x : V) (f : ℕ → V) (a q : ℕ) :
    dseg G x f a q = ∑ i ∈ Ico a (a + q), bi (G.Adj x (f i)) := by
  unfold dseg bi; rw [card_filter]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A reversed suffix of a square path is a square path. -/
lemma IsSq.revSuffix {s : ℕ} {f : ℕ → V} (h : IsSq G s f) (i : ℕ) :
    IsSq G (s - i) (fun j => f (s - 1 - j)) := h.rev.take (by omega)

section Lemma9

variable {s : ℕ} {f : ℕ → V}

/-- The count `c i = d({x,y}, f i)`. -/
def cnt2 (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (f : ℕ → V) (i : ℕ) : ℕ :=
  bi (G.Adj x (f i)) + bi (G.Adj y (f i))

omit [DecidableEq V] in
lemma cnt2_le (x y : V) (f : ℕ → V) (i : ℕ) : cnt2 G x y f i ≤ 2 := by
  unfold cnt2; have := bi_le_one (G.Adj x (f i)); have := bi_le_one (G.Adj y (f i)); omega

omit [DecidableEq V] in
lemma cnt2_two {x y : V} {f : ℕ → V} {i : ℕ} (h : cnt2 G x y f i = 2) :
    G.Adj x (f i) ∧ G.Adj y (f i) := by
  unfold cnt2 at h
  by_contra hc
  rw [not_and_or] at hc
  rcases hc with hc | hc
  · rw [bi_neg hc] at h; have := bi_le_one (G.Adj y (f i)); omega
  · rw [bi_neg hc] at h; have := bi_le_one (G.Adj x (f i)); omega

omit [DecidableEq V] in
lemma cnt2_zero {x y : V} {f : ℕ → V} {i : ℕ} (h : ¬ G.Adj x (f i)) (h' : ¬ G.Adj y (f i)) :
    cnt2 G x y f i = 0 := by unfold cnt2; rw [bi_neg h, bi_neg h']

omit [DecidableEq V] in
lemma dseg_pair_eq_sum (x y : V) (f : ℕ → V) (a q : ℕ) :
    dseg G x f a q + dseg G y f a q = ∑ i ∈ Ico a (a + q), cnt2 G x y f i := by
  rw [dseg_eq_sum, dseg_eq_sum, ← sum_add_distrib]; rfl

/-- Square paths of `p` vertices in `G - S` starting at `(x, y)`. -/
def StartsAt (G : SimpleGraph V) (s : ℕ) (f : ℕ → V) (p : ℕ) (x y : V) : Prop :=
  ∃ P : ℕ → V, IsSq G p P ∧ P 0 = x ∧ P 1 = y ∧ ∀ i < p, ∀ j < s, P i ≠ f j

omit [DecidableEq V] in
/-- If `f i` is a common neighbour of `x, y` near the start of an optimal `S`, then `f (i+1)` is
adjacent to neither (else a reversed suffix of `S` followed by a path from `x y` is longer). -/
lemma lemma9_left (hS : Opt G s f) {x y : V} {p : ℕ} (_hp : 2 ≤ p)
    (hP : StartsAt G s f p x y) (hP' : StartsAt G s f p y x) {i : ℕ} (hi : i + 1 ≤ p)
    (his : i + 1 < s) (h2 : cnt2 G x y f i = 2) : cnt2 G x y f (i + 1) = 0 := by
  obtain ⟨hx, hy⟩ := cnt2_two h2
  have key : ∀ a b : V, StartsAt G s f p a b → G.Adj a (f i) → G.Adj b (f i) →
      ¬ G.Adj a (f (i + 1)) := by
    intro a b ⟨P, hPs, hP0, hP1, hPS⟩ ha hb hab
    have hA := hS.1.revSuffix i
    have hc := isSq_cat hA hPs
      (fun j hj k hk => fun he => hPS k hk (s - 1 - j) (by omega) he.symm)
      (fun _ _ => by rw [hP0, show s - 1 - (s - i - 1) = i by omega]; exact ha.symm)
      (fun _ _ => by rw [hP0, show s - 1 - (s - i - 2) = i + 1 by omega]; exact hab.symm)
      (fun _ _ => by rw [hP1, show s - 1 - (s - i - 1) = i by omega]; exact hb.symm)
    have := (hS.2 _ _ hc).1
    omega
  exact cnt2_zero (key x y hP hx hy) (key y x hP' hy hx)

omit [DecidableEq V] in
/-- The mirror statement at the end of `S`. -/
lemma lemma9_right (hS : Opt G s f) {x y : V} {p : ℕ} (_hp : 2 ≤ p)
    (hP : StartsAt G s f p x y) (hP' : StartsAt G s f p y x) {i : ℕ} (hi : s ≤ i + p)
    (hi1 : 1 ≤ i) (his : i < s) (h2 : cnt2 G x y f i = 2) : cnt2 G x y f (i - 1) = 0 := by
  obtain ⟨hx, hy⟩ := cnt2_two h2
  have key : ∀ a b : V, StartsAt G s f p a b → G.Adj a (f i) → G.Adj b (f i) →
      ¬ G.Adj a (f (i - 1)) := by
    intro a b ⟨P, hPs, hP0, hP1, hPS⟩ ha hb hab
    have hA := hS.1.take (m := i + 1) (by omega)
    have hc := isSq_cat hA hPs
      (fun j hj k hk => fun he => hPS k hk j (by omega) he.symm)
      (fun _ _ => by rw [hP0, show i + 1 - 1 = i by omega]; exact ha.symm)
      (fun _ _ => by rw [hP0, show i + 1 - 2 = i - 1 by omega]; exact hab.symm)
      (fun _ _ => by rw [hP1, show i + 1 - 1 = i by omega]; exact hb.symm)
    have := (hS.2 _ _ hc).1
    omega
  exact cnt2_zero (key x y hP hx hy) (key y x hP' hy hx)

end Lemma9

section Lemma9b

variable {s : ℕ} {f : ℕ → V}

omit [DecidableEq V] in
lemma lemma9_block_left (hS : Opt G s f) {x y : V} {p : ℕ} (hp : 2 ≤ p) (hs : 2 * p + 2 ≤ s)
    (hP : StartsAt G s f p x y) (hP' : StartsAt G s f p y x) :
    ∃ q, (q = p ∨ q = p + 1) ∧ ∑ i ∈ range q, cnt2 G x y f i ≤ q := by
  have hL : ∀ i, i + 1 ≤ p → cnt2 G x y f i = 2 → cnt2 G x y f (i + 1) = 0 :=
    fun i hi h => lemma9_left hS hp hP hP' hi (by omega) h
  by_cases h2 : cnt2 G x y f (p - 1) = 2
  · refine ⟨p + 1, Or.inr rfl, ?_⟩
    have h0 := hL (p - 1) (by omega) h2
    rw [show p - 1 + 1 = p by omega] at h0
    have := one_sided (cnt2 G x y f) (cnt2_le x y f) p (fun i hi h => hL i (by omega) h)
    rw [if_neg (by omega)] at this
    exact this
  · refine ⟨p, Or.inl rfl, ?_⟩
    have := one_sided (cnt2 G x y f) (cnt2_le x y f) (p - 1) (fun i hi h => hL i (by omega) h)
    rw [if_neg h2, show p - 1 + 1 = p by omega] at this
    omega

omit [DecidableEq V] in
lemma lemma9_block_right (hS : Opt G s f) {x y : V} {p : ℕ} (hp : 2 ≤ p) (hs : 2 * p + 2 ≤ s)
    (hP : StartsAt G s f p x y) (hP' : StartsAt G s f p y x) :
    ∃ q, (q = p ∨ q = p + 1) ∧ ∑ i ∈ Ico (s - q) s, cnt2 G x y f i ≤ q := by
  let c' : ℕ → ℕ := fun j => cnt2 G x y f (s - 1 - j)
  have hR : ∀ j, j + 1 ≤ p → c' j = 2 → c' (j + 1) = 0 := by
    intro j hj h
    have := lemma9_right hS hp hP hP' (i := s - 1 - j) (by omega) (by omega) (by omega) h
    simp only [c']
    rwa [show s - 1 - (j + 1) = s - 1 - j - 1 by omega]
  have hconv : ∀ q, q ≤ s → ∑ i ∈ Ico (s - q) s, cnt2 G x y f i = ∑ j ∈ range q, c' j := by
    intro q hq
    symm
    apply sum_bij (fun j _ => s - 1 - j)
    · intro j hj; simp only [mem_range] at hj; simp only [mem_Ico]; omega
    · intro j hj j' hj' h; simp only [mem_range] at hj hj'; omega
    · intro i hi; simp only [mem_Ico] at hi
      exact ⟨s - 1 - i, by simp only [mem_range]; omega, by omega⟩
    · intro j hj; rfl
  have hc'le : ∀ j, c' j ≤ 2 := fun j => cnt2_le x y f _
  by_cases h2 : c' (p - 1) = 2
  · refine ⟨p + 1, Or.inr rfl, ?_⟩
    have h0 := hR (p - 1) (by omega) h2
    rw [show p - 1 + 1 = p by omega] at h0
    have := one_sided c' hc'le p (fun i hi h => hR i (by omega) h)
    rw [if_neg (by omega)] at this
    rw [hconv (p + 1) (by omega)]
    exact this
  · refine ⟨p, Or.inl rfl, ?_⟩
    have := one_sided c' hc'le (p - 1) (fun i hi h => hR i (by omega) h)
    rw [if_neg h2, show p - 1 + 1 = p by omega] at this
    rw [hconv p (by omega)]
    omega

omit [DecidableEq V] in
/-- **Lemma 9** (Fan–Kierstead). -/
theorem lemma9 (hS : Opt G s f) {x y : V} (hxS : ∀ i < s, f i ≠ x) (hyS : ∀ i < s, f i ≠ y)
    {p : ℕ} (hp : 2 ≤ p) (hs : 2 * p + 2 ≤ s)
    (hP : StartsAt G s f p x y) (hP' : StartsAt G s f p y x) :
    3 * (dseg G x f 0 s + dseg G y f 0 s) ≤ 4 * s - 2 * p + 6 ∧
    (3 * (dseg G x f 0 s + dseg G y f 0 s) = 4 * s - 2 * p + 6 →
      (G.Adj x (f (p - 2)) ∧ G.Adj y (f (p - 2))) ∧ (G.Adj x (f p) ∧ G.Adj y (f p)) ∧
      (G.Adj x (f (p + 1)) ∧ G.Adj y (f (p + 1)))) := by
  obtain ⟨q, hq, hQ⟩ := lemma9_block_left hS hp hs hP hP'
  obtain ⟨q', hq', hQ'⟩ := lemma9_block_right hS hp hs hP hP'
  set r := s - q - q' with hr
  have hsum := dseg_pair_eq_sum (G := G) x y f 0 s
  rw [zero_add, ← sum_Ico_consecutive _ (show 0 ≤ s - q' by omega) (show s - q' ≤ s by omega),
    ← sum_Ico_consecutive _ (show 0 ≤ q by omega) (show q ≤ s - q' by omega)] at hsum
  rw [← range_eq_Ico] at hsum
  have hmid := dseg_pair_eq_sum (G := G) x y f q r
  rw [show q + r = s - q' by omega] at hmid
  have L1x := lemma1 hS.optFix hxS (a := q) (q := r) (by omega)
  have L1y := lemma1 hS.optFix hyS (a := q) (q := r) (by omega)
  refine ⟨by omega, fun heq => ?_⟩
  have hqp : q = p := by omega
  have hq'p : q' = p := by omega
  have ex : 3 * dseg G x f q r = 2 * r + 3 := by omega
  have ey : 3 * dseg G y f q r = 2 * r + 3 := by omega
  have hQeq : ∑ i ∈ range q, cnt2 G x y f i = q := by omega
  obtain ⟨ax0, ax1, ax2⟩ := lemma2 hS.optFix hxS (by omega) ex
  obtain ⟨ay0, ay1, ay2⟩ := lemma2 hS.optFix hyS (by omega) ey
  rw [hqp] at ax0 ax1 ax2 ay0 ay1 ay2
  refine ⟨?_, ⟨ax0, ay0⟩, ⟨ax1, ay1⟩⟩
  -- the vertex `f (p-2)` must be a common neighbour
  have hc0 : cnt2 G x y f (p - 1) = 0 := cnt2_zero (ax2 (by omega)) (ay2 (by omega))
  by_contra hno
  have h2 : cnt2 G x y f (p - 2) ≠ 2 := fun h => hno (cnt2_two h)
  have hL : ∀ i, i + 1 ≤ p → cnt2 G x y f i = 2 → cnt2 G x y f (i + 1) = 0 :=
    fun i hi h => lemma9_left hS hp hP hP' hi (by omega) h
  have := one_sided (cnt2 G x y f) (cnt2_le x y f) (p - 2) (fun i hi h => hL i (by omega) h)
  rw [if_neg h2, show p - 2 + 1 = p - 1 by omega] at this
  rw [hqp, show p = (p - 1) + 1 by omega, sum_range_succ, hc0] at hQeq
  omega

end Lemma9b

/- ### Degree bookkeeping -/

section Degrees

variable [Fintype V]

lemma deg_split (v : V) (A B : Finset V) (hAB : Disjoint A B) :
    G.degree v = (A.filter (G.Adj v)).card + (B.filter (G.Adj v)).card +
      ((univ \ (A ∪ B)).filter (G.Adj v)).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have h1 : G.neighborFinset v = (A.filter (G.Adj v)) ∪ (B.filter (G.Adj v)) ∪
      ((univ \ (A ∪ B)).filter (G.Adj v)) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, mem_union, mem_filter, mem_sdiff, mem_univ, true_and]
    tauto
  rw [h1, card_union_of_disjoint, card_union_of_disjoint]
  · exact disjoint_filter_filter hAB
  · rw [disjoint_union_left]
    constructor <;> apply disjoint_filter_filter <;> rw [disjoint_left] <;> intro w hw hw' <;>
      simp only [mem_sdiff, mem_union] at hw' <;> tauto

omit [Fintype V] in
lemma dseg_eq_card_image {f : ℕ → V} {s : ℕ} (hinj : ∀ i j, i < s → j < s → f i = f j → i = j)
    (v : V) : dseg G v f 0 s = (((range s).image f).filter (G.Adj v)).card := by
  unfold dseg
  rw [zero_add, ← range_eq_Ico, filter_image]
  rw [card_image_of_injOn]
  intro i hi j hj h
  simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hi hj
  exact hinj i j hi.1 hj.1 h

omit [Fintype V] in
lemma card_image_range {f : ℕ → V} {s : ℕ} (hinj : ∀ i j, i < s → j < s → f i = f j → i = j) :
    ((range s).image f).card = s := by
  rw [card_image_of_injOn (fun i hi j hj h => hinj i j (mem_range.1 hi) (mem_range.1 hj) h),
    card_range]

omit [Fintype V] in
/-- Each vertex of a set `A` has at most `|A| - 1` neighbours in `A`. -/
lemma card_filter_adj_self_le {A : Finset V} {v : V} (hv : v ∈ A) :
    (A.filter (G.Adj v)).card + 1 ≤ A.card := by
  have : A.filter (G.Adj v) ⊆ A.erase v := by
    intro w hw
    simp only [mem_filter] at hw
    exact mem_erase.2 ⟨fun h => G.loopless.irrefl v (h ▸ hw.2), hw.1⟩
  have := card_le_card this
  rw [card_erase_of_mem hv] at this
  have := card_pos.2 ⟨v, hv⟩
  omega

end Degrees

/- ### Lemma 10 -/

section Lemma10

variable [Fintype V] {s : ℕ} {f : ℕ → V}

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
lemma IsCube.extend {p : ℕ} {c : ℕ → V} (hc : IsCube G p c) {z : V} (hz : ∀ i < p, c i ≠ z)
    (h1 : 1 ≤ p → G.Adj (c (p - 1)) z) (h2 : 2 ≤ p → G.Adj (c (p - 2)) z)
    (h3 : 3 ≤ p → G.Adj (c (p - 3)) z) :
    IsCube G (p + 1) (fun i => if i < p then c i else z) := by
  constructor
  · intro i j hij hj3 hj
    by_cases hjp : j < p
    · rw [if_pos (by omega), if_pos hjp]; exact hc.adj i j hij hj3 hjp
    · rw [if_pos (by omega), if_neg hjp]
      have : i + 1 = p ∨ i + 2 = p ∨ i + 3 = p := by omega
      rcases this with h | h | h
      · rw [show i = p - 1 by omega]; exact h1 (by omega)
      · rw [show i = p - 2 by omega]; exact h2 (by omega)
      · rw [show i = p - 3 by omega]; exact h3 (by omega)
  · intro i j hi hj h
    by_cases hip : i < p <;> by_cases hjp : j < p <;> simp only [hip, hjp, if_true, if_false] at h
    · exact hc.inj i j hip hjp h
    · exact absurd h (hz i hip)
    · exact absurd h.symm (hz j hjp)
    · omega


/-- A sequence reading some positions from a cube path `c` (through `α`) and the others from a
square path `f` (through `β`). -/
def two (P : ℕ → Prop) [DecidablePred P] (c f : ℕ → V) (α β : ℕ → ℕ) : ℕ → V :=
  fun i => if P i then c (α i) else f (β i)

omit [Fintype V] in
omit [DecidableEq V] [DecidableRel G.Adj] in
lemma isSq_two {p s m : ℕ} {c f : ℕ → V} (hc : IsCube G p c) (hf : IsSq G s f)
    (hdisj : ∀ i < p, ∀ j < s, c i ≠ f j) (P : ℕ → Prop) [DecidablePred P] (α β : ℕ → ℕ)
    (hα : ∀ i < m, P i → α i < p) (hβ : ∀ i < m, ¬ P i → β i < s)
    (hαinj : ∀ i j, i < m → j < m → P i → P j → α i = α j → i = j)
    (hβinj : ∀ i j, i < m → j < m → ¬ P i → ¬ P j → β i = β j → i = j)
    (hcc : ∀ i j, i < j → j ≤ i + 2 → j < m → P i → P j → α i ≤ α j + 3 ∧ α j ≤ α i + 3)
    (hff : ∀ i j, i < j → j ≤ i + 2 → j < m → ¬ P i → ¬ P j → β i ≤ β j + 2 ∧ β j ≤ β i + 2)
    (hcf : ∀ i j, i < j → j ≤ i + 2 → j < m → ((P i ∧ ¬ P j) ∨ (¬ P i ∧ P j)) →
      G.Adj (two P c f α β i) (two P c f α β j)) :
    IsSq G m (two P c f α β) := by
  refine isSq_of_pairs _ (fun i j hij hj2 hj => ?_) (fun i j hi hj h => ?_)
  · by_cases hPi : P i <;> by_cases hPj : P j
    · simp only [two, if_pos hPi, if_pos hPj]
      have hne : α i ≠ α j := fun he => by
        have := hαinj i j (by omega) hj hPi hPj he; omega
      obtain ⟨h1, h2⟩ := hcc i j hij hj2 hj hPi hPj
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · exact hc.adj _ _ hl (by omega) (hα j hj hPj)
      · exact (hc.adj _ _ hl (by omega) (hα i (by omega) hPi)).symm
    · exact hcf i j hij hj2 hj (Or.inl ⟨hPi, hPj⟩)
    · exact hcf i j hij hj2 hj (Or.inr ⟨hPi, hPj⟩)
    · simp only [two, if_neg hPi, if_neg hPj]
      have hne : β i ≠ β j := fun he => by
        have := hβinj i j (by omega) hj hPi hPj he; omega
      obtain ⟨h1, h2⟩ := hff i j hij hj2 hj hPi hPj
      exact hf.adj_close' (hβ i (by omega) hPi) (hβ j hj hPj) hne h1 h2
  · unfold two at h
    by_cases hPi : P i <;> by_cases hPj : P j <;> simp only [hPi, hPj, if_true, if_false] at h
    · exact hαinj i j hi hj hPi hPj (hc.inj _ _ (hα i hi hPi) (hα j hj hPj) h)
    · exact absurd h (hdisj _ (hα i hi hPi) _ (hβ j hj hPj))
    · exact absurd h.symm (hdisj _ (hα j hj hPj) _ (hβ i hi hPi))
    · exact hβinj i j hi hj hPi hPj (hf.inj _ _ (hβ i hi hPi) (hβ j hj hPj) h)

/-- Lemma 10, core: a maximal cube path `c` of `G - S` whose first edge has `s+2` neighbours in
`S` gives a contradiction. -/
lemma lemma10_core (hS : Opt G s f)
    (hdeg : ∀ v, (∀ j < s, f j ≠ v) → 2 * Fintype.card V ≤ 3 * G.degree v)
    {p : ℕ} {c : ℕ → V} (hc : IsCube G p c) (hp2 : 2 ≤ p)
    (hcS : ∀ i < p, ∀ j < s, c i ≠ f j)
    (hmax : ∀ z, (∀ j < s, f j ≠ z) → (∀ i < p, c i ≠ z) →
      ¬ (G.Adj (c (p - 1)) z ∧ G.Adj (c (p - 2)) z ∧ (3 ≤ p → G.Adj (c (p - 3)) z)))
    (hbig : s + 2 ≤ dseg G (c 0) f 0 s + dseg G (c 1) f 0 s) : False := by
  classical
  set n := Fintype.card V with hn
  set Sf := (range s).image f with hSf
  set Pc := (range p).image c with hPc
  have hSinj := hS.1.inj
  have hSc : Sf.card = s := card_image_range hSinj
  have hPcc : Pc.card = p := card_image_range hc.inj
  have hdisj : Disjoint Sf Pc := by
    rw [disjoint_left]
    intro w hw hw'
    simp only [hSf, hPc, mem_image, mem_range] at hw hw'
    obtain ⟨j, hj, rfl⟩ := hw
    obtain ⟨i, hi, hci⟩ := hw'
    exact hcS i hi j hj hci
  have hcard : s + p ≤ n := by
    have := card_le_univ (Sf ∪ Pc)
    rw [card_union_of_disjoint hdisj, hSc, hPcc] at this
    exact this
  have hnotS : ∀ i < p, ∀ j < s, f j ≠ c i := fun i hi j hj h => hcS i hi j hj h.symm
  -- square paths of `p` vertices from the first edge, both orders
  have hst01 : StartsAt G s f p (c 0) (c 1) :=
    ⟨c, hc.isSq, rfl, rfl, hcS⟩
  have hst10 : StartsAt G s f p (c 1) (c 0) := by
    refine ⟨_, lemma7_swap01 hc hp2, by simp, by simp, fun i hi j hj => ?_⟩
    split_ifs <;> exact hcS _ (by omega) j hj
  -- `p ≥ 3`: the first two vertices have a common neighbour outside `S`
  have hp3 : 3 ≤ p := by
    by_contra hlt
    have hp : p = 2 := by omega
    have L4a := lemma4 hS (x := c 0) (hnotS 0 (by omega))
    have L4b := lemma4 hS (x := c 1) (hnotS 1 (by omega))
    have da := deg_split (G := G) (c 0) Sf ∅ (disjoint_empty_right _)
    have db := deg_split (G := G) (c 1) Sf ∅ (disjoint_empty_right _)
    simp only [filter_empty, card_empty, add_zero, union_empty] at da db
    rw [← dseg_eq_card_image hSinj] at da db
    have ha := hdeg (c 0) (hnotS 0 (by omega))
    have hb := hdeg (c 1) (hnotS 1 (by omega))
    -- no common neighbour outside `S`
    have hnc : ∀ z ∈ univ \ Sf, ¬ (G.Adj (c 0) z ∧ G.Adj (c 1) z) := by
      intro z hz hzz
      simp only [mem_sdiff, mem_univ, true_and, hSf, mem_image, mem_range, not_exists, not_and]
        at hz
      apply hmax z (fun j hj => hz j hj) (fun i hi h => by
        have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl
        · exact G.loopless.irrefl _ (h ▸ hzz.1)
        · exact G.loopless.irrefl _ (h ▸ hzz.2))
      rw [hp]
      exact ⟨hzz.2, hzz.1, fun h => by omega⟩
    have hunion := card_union_add_card_inter ((univ \ Sf).filter (G.Adj (c 0)))
      ((univ \ Sf).filter (G.Adj (c 1)))
    have hinter : ((univ \ Sf).filter (G.Adj (c 0)) ∩ (univ \ Sf).filter (G.Adj (c 1))) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro z hz
      simp only [mem_inter, mem_filter] at hz
      exact hnc z hz.1.1 ⟨hz.1.2, hz.2.2⟩
    rw [hinter, card_empty, add_zero] at hunion
    have hsub : (univ \ Sf).filter (G.Adj (c 0)) ∪ (univ \ Sf).filter (G.Adj (c 1)) ⊆ univ \ Sf := by
      intro z hz
      simp only [mem_union, mem_filter] at hz
      rcases hz with h | h <;> exact h.1
    have := card_le_card hsub
    rw [card_univ_sdiff, hSc] at this
    omega
  have hsum01 := dseg_pair_eq_sum (G := G) (c 0) (c 1) f 0 s
  rw [zero_add, ← range_eq_Ico] at hsum01
  by_cases hsp : s ≤ 2 * p + 1
  · -- Lemma 8
    have h8 := lemma8_count (cnt2 G (c 0) (c 1) f) (cnt2_le _ _ f) s
      (fun i hi h => lemma9_left hS hp2 hst01 hst10 (i := i) (by omega) (by omega) h)
      (fun i hi1 hi2 h => lemma9_right hS hp2 hst01 hst10 (i := i) (by omega) (by omega) hi2 h)
    omega
  push Not at hsp
  -- the last three vertices `u v w` of the cube path
  set u := c (p - 3) with hu
  set v := c (p - 2) with hv
  set w := c (p - 1) with hw
  have hcr := hc.rev
  have cr0 : rev p c 0 = w := by simp only [rev, hw, Nat.sub_zero]
  have cr1 : rev p c 1 = v := by simp only [rev, hv]; congr 1
  have cr2 : rev p c 2 = u := by simp only [rev, hu]; congr 1
  have hcrS : ∀ i < p, ∀ j < s, rev p c i ≠ f j := fun i hi j hj => hcS _ (by omega) j hj
  have st_uw : StartsAt G s f p u w := ⟨_, lemma7_rot hcr hp3, by simp [cr2], by simp [cr0],
    fun i hi j hj => by split_ifs <;> exact hcrS _ (by omega) j hj⟩
  have st_wu : StartsAt G s f p w u := ⟨_, lemma7_swap12 hcr hp3, by simp [cr0], by simp [cr2],
    fun i hi j hj => by split_ifs <;> exact hcrS _ (by omega) j hj⟩
  have st_vw : StartsAt G s f p v w := ⟨_, lemma7_swap01 hcr hp2, by simp [cr1], by simp [cr0],
    fun i hi j hj => by split_ifs <;> exact hcrS _ (by omega) j hj⟩
  have st_wv : StartsAt G s f p w v := ⟨_, hcr.isSq, cr0, cr1, hcrS⟩
  have st_uv : StartsAt G s f (p - 1) u v := ⟨_, lemma7_dropswap hcr hp3, by simp [cr2],
    by simp [cr1], fun i hi j hj => by split_ifs <;> exact hcrS _ (by omega) j hj⟩
  have st_vu : StartsAt G s f (p - 1) v u := ⟨_, lemma7_drop hcr, by simp [cr1],
    by simp [cr2], fun i hi j hj => hcrS _ (by omega) j hj⟩
  have huS : ∀ j < s, f j ≠ u := hnotS _ (by omega)
  have hvS : ∀ j < s, f j ≠ v := hnotS _ (by omega)
  have hwS : ∀ j < s, f j ≠ w := hnotS _ (by omega)
  have L_uw := lemma9 hS huS hwS hp2 (by omega) st_uw st_wu
  have L_vw := lemma9 hS hvS hwS hp2 (by omega) st_vw st_wv
  have L_uv := lemma9 hS huS hvS (p := p - 1) (by omega) (by omega) st_uv st_vu
  have L_ab := lemma9 hS (hnotS 0 (by omega)) (hnotS 1 (by omega)) hp2 (by omega) hst01 hst10
  -- (2.5)
  have h25 : dseg G u f 0 s + dseg G v f 0 s + dseg G w f 0 s ≤ 2 * s - p + 2 := by
    by_cases heq2 : 3 * (dseg G u f 0 s + dseg G w f 0 s) = 4 * s - 2 * p + 6 ∧
        3 * (dseg G v f 0 s + dseg G w f 0 s) = 4 * s - 2 * p + 6
    · exfalso
      obtain ⟨⟨hu1, hw1⟩, ⟨hu2, hw2⟩, ⟨hu3, hw3⟩⟩ := L_uw.2 heq2.1
      obtain ⟨⟨hv1, -⟩, ⟨hv2, -⟩, ⟨hv3, -⟩⟩ := L_vw.2 heq2.2
      -- the path `c 0 … c (p-2), f (p-2), w, f p, …, f (s-1)` has `s+1` vertices
      have hg := isSq_two (m := s + 1) hc hS.1 hcS (fun i => i < p - 1 ∨ i = p)
        (fun i => if i = p then p - 1 else i) (fun i => if i = p - 1 then p - 2 else i - 1)
        (fun i hi hP => by split_ifs <;> omega) (fun i hi hP => by split_ifs <;> omega)
        (fun i j hi hj hPi hPj h => by split_ifs at h <;> omega)
        (fun i j hi hj hPi hPj h => by split_ifs at h <;> omega)
        (fun i j hij hj2 hj hPi hPj => by split_ifs <;> omega)
        (fun i j hij hj2 hj hPi hPj => by split_ifs <;> omega)
        (fun i j hij hj2 hj hcase => by
          simp only [two]
          rcases hcase with ⟨hPi, hPj⟩ | ⟨hPi, hPj⟩
          · rw [if_pos hPi, if_neg hPj]
            have hj' : j = p - 1 ∨ j = p + 1 ∨ j = p + 2 := by omega
            rcases hj' with hj' | hj' | hj'
            · rw [if_pos hj']
              have hi' : i = p - 3 ∨ i = p - 2 := by omega
              rcases hi' with hi' | hi'
              · rw [if_neg (show ¬ (i = p) by omega), hi']; exact hu1
              · rw [if_neg (show ¬ (i = p) by omega), hi']; exact hv1
            · rw [if_neg (show ¬ (j = p - 1) by omega), hj', show p + 1 - 1 = p by omega,
                if_pos (show i = p by omega)]
              exact hw2
            · rw [if_neg (show ¬ (j = p - 1) by omega), hj', show p + 2 - 1 = p + 1 by omega,
                if_pos (show i = p by omega)]
              exact hw3
          · rw [if_neg hPi, if_pos hPj]
            have hi' : i = p - 1 := by omega
            have hj' : j = p := by omega
            rw [if_pos hi', if_pos hj']; exact hw1.symm)
      have := (hS.2 _ _ hg).1
      omega
    · by_cases heq7 : 3 * (dseg G u f 0 s + dseg G v f 0 s) = 4 * s - 2 * (p - 1) + 6
      · exfalso
        obtain ⟨-, ⟨hu4, hv4⟩, ⟨hu5, hv5⟩⟩ := L_uv.2 heq7
        rw [show p - 1 + 1 = p by omega] at hu5 hv5
        -- the path `c 0 … c (p-2), f (p-1), …, f (s-1)` has `s` vertices
        have hg := isSq_two (m := s) hc hS.1 hcS (fun i => i < p - 1) id id
          (fun i hi hP => by simp only [id]; omega) (fun i hi hP => by simp only [id]; omega)
          (fun i j hi hj _ _ h => h) (fun i j hi hj _ _ h => h)
          (fun i j hij hj2 hj _ _ => by simp only [id]; omega)
          (fun i j hij hj2 hj _ _ => by simp only [id]; omega)
          (fun i j hij hj2 hj hcase => by
            simp only [two, id]
            rcases hcase with ⟨hPi, hPj⟩ | ⟨hPi, hPj⟩
            · rw [if_pos hPi, if_neg hPj]
              have hc' : (i = p - 3 ∧ j = p - 1) ∨ (i = p - 2 ∧ j = p - 1) ∨ (i = p - 2 ∧ j = p) := by
                omega
              rcases hc' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
              · exact hu4
              · exact hv4
              · exact hv5
            · omega)
        set g := two (fun i => i < p - 1) c f id id with hgdef
        have hg0 : g 0 = c 0 := by simp only [hgdef, two, id]; rw [if_pos (by omega)]
        have hg1 : g 1 = c 1 := by simp only [hgdef, two, id]; rw [if_pos (by omega)]
        -- nothing outside `g` is adjacent to both `c 0` and `c 1`
        have hnot : ∀ z, (∀ i < s, g i ≠ z) → ¬ (G.Adj (c 0) z ∧ G.Adj (c 1) z) := by
          intro z hz ⟨h0, h1⟩
          have := isSq_cat (isSq_one z) hg (fun i _ j hj h => hz j hj h.symm)
            (fun _ _ => by rw [hg0]; exact h0.symm) (fun h _ => by omega)
            (fun _ _ => by rw [hg1]; exact h1.symm)
          have := (hS.2 _ _ this).1
          omega
        have hRest_g : ∀ z ∈ univ \ (Sf ∪ Pc), ∀ i < s, g i ≠ z := by
          intro z hz i hi h
          simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or] at hz
          simp only [hgdef, two, id] at h
          split_ifs at h with hip
          · exact hz.2 (h ▸ mem_image_of_mem c (mem_range.2 (by omega)))
          · exact hz.1 (h ▸ mem_image_of_mem f (mem_range.2 hi))
        have hw_g : ∀ i < s, g i ≠ w := by
          intro i hi h
          simp only [hgdef, two, id] at h
          split_ifs at h with hip
          · have := hc.inj _ _ (by omega) (by omega) h; omega
          · exact hwS i hi h
        -- degree count for `c 0` and `c 1`
        have d0 := deg_split (G := G) (c 0) Sf Pc hdisj
        have d1 := deg_split (G := G) (c 1) Sf Pc hdisj
        rw [← dseg_eq_card_image hSinj] at d0 d1
        have hPsum : (Pc.filter (G.Adj (c 0))).card + (Pc.filter (G.Adj (c 1))).card ≤ 2 * p - 3 := by
          rw [card_filter_eq_sum_bi, card_filter_eq_sum_bi, ← sum_add_distrib, hPc,
            sum_image (fun i hi j hj h => hc.inj i j (mem_range.1 hi) (mem_range.1 hj) h)]
          apply sum_le_two_mul_sub_three _ p hp3
          · intro i
            have := bi_le_one (G.Adj (c 0) (c i)); have := bi_le_one (G.Adj (c 1) (c i)); omega
          · rw [bi_neg (G.irrefl (v := c 0))]; have := bi_le_one (G.Adj (c 1) (c 0)); omega
          · rw [bi_neg (G.irrefl (v := c 1))]; have := bi_le_one (G.Adj (c 0) (c 1)); omega
          · by_cases h0 : G.Adj (c 0) (c (p - 1))
            · rw [bi_pos h0, bi_neg (show ¬ G.Adj (c 1) (c (p - 1)) from fun h1 => hnot w hw_g ⟨h0, h1⟩)]
            · rw [bi_neg h0]; have := bi_le_one (G.Adj (c 1) (c (p - 1))); omega
        have hRsum : ((univ \ (Sf ∪ Pc)).filter (G.Adj (c 0))).card +
            ((univ \ (Sf ∪ Pc)).filter (G.Adj (c 1))).card ≤ (univ \ (Sf ∪ Pc)).card := by
          rw [card_filter_eq_sum_bi, card_filter_eq_sum_bi, ← sum_add_distrib, card_eq_sum_ones]
          apply sum_le_sum
          intro z hz
          by_cases h0 : G.Adj (c 0) z
          · rw [bi_pos h0, bi_neg (show ¬ G.Adj (c 1) z from fun h1 => hnot z (hRest_g z hz) ⟨h0, h1⟩)]
          · rw [bi_neg h0]; have := bi_le_one (G.Adj (c 1) z); omega
        have hRc : (univ \ (Sf ∪ Pc)).card = n - (s + p) := by
          rw [card_univ_sdiff, card_union_of_disjoint hdisj, hSc, hPcc]
        have := hdeg (c 0) (hnotS 0 (by omega))
        have := hdeg (c 1) (hnotS 1 (by omega))
        have := L_ab.1
        omega
      · have := L_uw.1
        have := L_vw.1
        have := L_uv.1
        omega
  -- (2.8): count the degrees of `u, v, w`
  have hmemP : ∀ i < p, c i ∈ Pc := fun i hi => mem_image_of_mem c (mem_range.2 hi)
  have du := deg_split (G := G) u Sf Pc hdisj
  have dv := deg_split (G := G) v Sf Pc hdisj
  have dw := deg_split (G := G) w Sf Pc hdisj
  rw [← dseg_eq_card_image hSinj] at du dv dw
  have pu : (Pc.filter (G.Adj u)).card + 1 ≤ p := by
    have := card_filter_adj_self_le (G := G) (hmemP (p - 3) (by omega)); rw [hPcc] at this; exact this
  have pv : (Pc.filter (G.Adj v)).card + 1 ≤ p := by
    have := card_filter_adj_self_le (G := G) (hmemP (p - 2) (by omega)); rw [hPcc] at this; exact this
  have pw : (Pc.filter (G.Adj w)).card + 1 ≤ p := by
    have := card_filter_adj_self_le (G := G) (hmemP (p - 1) (by omega)); rw [hPcc] at this; exact this
  have hRest : ∀ z ∈ univ \ (Sf ∪ Pc), (∀ j < s, f j ≠ z) ∧ (∀ i < p, c i ≠ z) := by
    intro z hz
    simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or] at hz
    exact ⟨fun j hj h => hz.1 (h ▸ mem_image_of_mem f (mem_range.2 hj)),
      fun i hi h => hz.2 (h ▸ hmemP i hi)⟩
  have hR : ((univ \ (Sf ∪ Pc)).filter (G.Adj u)).card + ((univ \ (Sf ∪ Pc)).filter (G.Adj v)).card +
      ((univ \ (Sf ∪ Pc)).filter (G.Adj w)).card ≤ 2 * (univ \ (Sf ∪ Pc)).card := by
    rw [card_filter_eq_sum_bi, card_filter_eq_sum_bi, card_filter_eq_sum_bi, ← sum_add_distrib,
      ← sum_add_distrib]
    calc _ ≤ (univ \ (Sf ∪ Pc)).card • 2 := sum_le_card_nsmul _ _ 2 (fun z hz => by
            obtain ⟨hzS, hzc⟩ := hRest z hz
            have hm := hmax z hzS hzc
            have := bi_le_one (G.Adj u z)
            have := bi_le_one (G.Adj v z)
            have := bi_le_one (G.Adj w z)
            by_cases h1 : G.Adj w z <;> by_cases h2 : G.Adj v z <;> by_cases h3 : G.Adj u z
            · exact absurd ⟨h1, h2, fun _ => h3⟩ hm
            all_goals first
              | (rw [bi_neg h3]; omega)
              | (rw [bi_neg h2]; omega)
              | (rw [bi_neg h1]; omega))
      _ = 2 * (univ \ (Sf ∪ Pc)).card := by rw [smul_eq_mul, mul_comm]
  have hRc : (univ \ (Sf ∪ Pc)).card = n - (s + p) := by
    rw [card_univ_sdiff, card_union_of_disjoint hdisj, hSc, hPcc]
  have := hdeg u huS
  have := hdeg v hvS
  have := hdeg w hwS
  omega


/-- (2.5) of Fan–Kierstead for the end triangle of any cube path outside `S` with `s ≥ 2p+2`,
under the weaker degree condition `δ ≥ (2n-1)/3` outside `S`. -/
lemma lemma25 (hS : Opt G s f)
    (hdeg : ∀ v, (∀ j < s, f j ≠ v) → 2 * Fintype.card V ≤ 3 * G.degree v + 1)
    {p : ℕ} {c : ℕ → V} (hc : IsCube G p c) (hp3 : 3 ≤ p)
    (hcS : ∀ i < p, ∀ j < s, c i ≠ f j) (hsp : 2 * p + 2 ≤ s) :
    dseg G (c (p - 3)) f 0 s + dseg G (c (p - 2)) f 0 s + dseg G (c (p - 1)) f 0 s ≤ 2 * s - p + 2 := by
  have hp2 : 2 ≤ p := by omega
  classical
  set n := Fintype.card V with hn
  set Sf := (range s).image f with hSf
  set Pc := (range p).image c with hPc
  have hSinj := hS.1.inj
  have hSc : Sf.card = s := card_image_range hSinj
  have hPcc : Pc.card = p := card_image_range hc.inj
  have hdisj : Disjoint Sf Pc := by
    rw [disjoint_left]
    intro w hw hw'
    simp only [hSf, hPc, mem_image, mem_range] at hw hw'
    obtain ⟨j, hj, rfl⟩ := hw
    obtain ⟨i, hi, hci⟩ := hw'
    exact hcS i hi j hj hci
  have hcard : s + p ≤ n := by
    have := card_le_univ (Sf ∪ Pc)
    rw [card_union_of_disjoint hdisj, hSc, hPcc] at this
    exact this
  have hnotS : ∀ i < p, ∀ j < s, f j ≠ c i := fun i hi j hj h => hcS i hi j hj h.symm
  -- square paths of `p` vertices from the first edge, both orders
  have hst01 : StartsAt G s f p (c 0) (c 1) :=
    ⟨c, hc.isSq, rfl, rfl, hcS⟩
  have hst10 : StartsAt G s f p (c 1) (c 0) := by
    refine ⟨_, lemma7_swap01 hc hp2, by simp, by simp, fun i hi j hj => ?_⟩
    split_ifs <;> exact hcS _ (by omega) j hj
  -- the last three vertices `u v w` of the cube path
  set u := c (p - 3) with hu
  set v := c (p - 2) with hv
  set w := c (p - 1) with hw
  have hcr := hc.rev
  have cr0 : rev p c 0 = w := by simp only [rev, hw, Nat.sub_zero]
  have cr1 : rev p c 1 = v := by simp only [rev, hv]; congr 1
  have cr2 : rev p c 2 = u := by simp only [rev, hu]; congr 1
  have hcrS : ∀ i < p, ∀ j < s, rev p c i ≠ f j := fun i hi j hj => hcS _ (by omega) j hj
  have st_uw : StartsAt G s f p u w := ⟨_, lemma7_rot hcr hp3, by simp [cr2], by simp [cr0],
    fun i hi j hj => by split_ifs <;> exact hcrS _ (by omega) j hj⟩
  have st_wu : StartsAt G s f p w u := ⟨_, lemma7_swap12 hcr hp3, by simp [cr0], by simp [cr2],
    fun i hi j hj => by split_ifs <;> exact hcrS _ (by omega) j hj⟩
  have st_vw : StartsAt G s f p v w := ⟨_, lemma7_swap01 hcr hp2, by simp [cr1], by simp [cr0],
    fun i hi j hj => by split_ifs <;> exact hcrS _ (by omega) j hj⟩
  have st_wv : StartsAt G s f p w v := ⟨_, hcr.isSq, cr0, cr1, hcrS⟩
  have st_uv : StartsAt G s f (p - 1) u v := ⟨_, lemma7_dropswap hcr hp3, by simp [cr2],
    by simp [cr1], fun i hi j hj => by split_ifs <;> exact hcrS _ (by omega) j hj⟩
  have st_vu : StartsAt G s f (p - 1) v u := ⟨_, lemma7_drop hcr, by simp [cr1],
    by simp [cr2], fun i hi j hj => hcrS _ (by omega) j hj⟩
  have huS : ∀ j < s, f j ≠ u := hnotS _ (by omega)
  have hvS : ∀ j < s, f j ≠ v := hnotS _ (by omega)
  have hwS : ∀ j < s, f j ≠ w := hnotS _ (by omega)
  have L_uw := lemma9 hS huS hwS hp2 (by omega) st_uw st_wu
  have L_vw := lemma9 hS hvS hwS hp2 (by omega) st_vw st_wv
  have L_uv := lemma9 hS huS hvS (p := p - 1) (by omega) (by omega) st_uv st_vu
  have L_ab := lemma9 hS (hnotS 0 (by omega)) (hnotS 1 (by omega)) hp2 (by omega) hst01 hst10
  -- (2.5)
  have h25 : dseg G u f 0 s + dseg G v f 0 s + dseg G w f 0 s ≤ 2 * s - p + 2 := by
    by_cases heq2 : 3 * (dseg G u f 0 s + dseg G w f 0 s) = 4 * s - 2 * p + 6 ∧
        3 * (dseg G v f 0 s + dseg G w f 0 s) = 4 * s - 2 * p + 6
    · exfalso
      obtain ⟨⟨hu1, hw1⟩, ⟨hu2, hw2⟩, ⟨hu3, hw3⟩⟩ := L_uw.2 heq2.1
      obtain ⟨⟨hv1, -⟩, ⟨hv2, -⟩, ⟨hv3, -⟩⟩ := L_vw.2 heq2.2
      -- the path `c 0 … c (p-2), f (p-2), w, f p, …, f (s-1)` has `s+1` vertices
      have hg := isSq_two (m := s + 1) hc hS.1 hcS (fun i => i < p - 1 ∨ i = p)
        (fun i => if i = p then p - 1 else i) (fun i => if i = p - 1 then p - 2 else i - 1)
        (fun i hi hP => by split_ifs <;> omega) (fun i hi hP => by split_ifs <;> omega)
        (fun i j hi hj hPi hPj h => by split_ifs at h <;> omega)
        (fun i j hi hj hPi hPj h => by split_ifs at h <;> omega)
        (fun i j hij hj2 hj hPi hPj => by split_ifs <;> omega)
        (fun i j hij hj2 hj hPi hPj => by split_ifs <;> omega)
        (fun i j hij hj2 hj hcase => by
          simp only [two]
          rcases hcase with ⟨hPi, hPj⟩ | ⟨hPi, hPj⟩
          · rw [if_pos hPi, if_neg hPj]
            have hj' : j = p - 1 ∨ j = p + 1 ∨ j = p + 2 := by omega
            rcases hj' with hj' | hj' | hj'
            · rw [if_pos hj']
              have hi' : i = p - 3 ∨ i = p - 2 := by omega
              rcases hi' with hi' | hi'
              · rw [if_neg (show ¬ (i = p) by omega), hi']; exact hu1
              · rw [if_neg (show ¬ (i = p) by omega), hi']; exact hv1
            · rw [if_neg (show ¬ (j = p - 1) by omega), hj', show p + 1 - 1 = p by omega,
                if_pos (show i = p by omega)]
              exact hw2
            · rw [if_neg (show ¬ (j = p - 1) by omega), hj', show p + 2 - 1 = p + 1 by omega,
                if_pos (show i = p by omega)]
              exact hw3
          · rw [if_neg hPi, if_pos hPj]
            have hi' : i = p - 1 := by omega
            have hj' : j = p := by omega
            rw [if_pos hi', if_pos hj']; exact hw1.symm)
      have := (hS.2 _ _ hg).1
      omega
    · by_cases heq7 : 3 * (dseg G u f 0 s + dseg G v f 0 s) = 4 * s - 2 * (p - 1) + 6
      · exfalso
        obtain ⟨-, ⟨hu4, hv4⟩, ⟨hu5, hv5⟩⟩ := L_uv.2 heq7
        rw [show p - 1 + 1 = p by omega] at hu5 hv5
        -- the path `c 0 … c (p-2), f (p-1), …, f (s-1)` has `s` vertices
        have hg := isSq_two (m := s) hc hS.1 hcS (fun i => i < p - 1) id id
          (fun i hi hP => by simp only [id]; omega) (fun i hi hP => by simp only [id]; omega)
          (fun i j hi hj _ _ h => h) (fun i j hi hj _ _ h => h)
          (fun i j hij hj2 hj _ _ => by simp only [id]; omega)
          (fun i j hij hj2 hj _ _ => by simp only [id]; omega)
          (fun i j hij hj2 hj hcase => by
            simp only [two, id]
            rcases hcase with ⟨hPi, hPj⟩ | ⟨hPi, hPj⟩
            · rw [if_pos hPi, if_neg hPj]
              have hc' : (i = p - 3 ∧ j = p - 1) ∨ (i = p - 2 ∧ j = p - 1) ∨ (i = p - 2 ∧ j = p) := by
                omega
              rcases hc' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
              · exact hu4
              · exact hv4
              · exact hv5
            · omega)
        set g := two (fun i => i < p - 1) c f id id with hgdef
        have hg0 : g 0 = c 0 := by simp only [hgdef, two, id]; rw [if_pos (by omega)]
        have hg1 : g 1 = c 1 := by simp only [hgdef, two, id]; rw [if_pos (by omega)]
        -- nothing outside `g` is adjacent to both `c 0` and `c 1`
        have hnot : ∀ z, (∀ i < s, g i ≠ z) → ¬ (G.Adj (c 0) z ∧ G.Adj (c 1) z) := by
          intro z hz ⟨h0, h1⟩
          have := isSq_cat (isSq_one z) hg (fun i _ j hj h => hz j hj h.symm)
            (fun _ _ => by rw [hg0]; exact h0.symm) (fun h _ => by omega)
            (fun _ _ => by rw [hg1]; exact h1.symm)
          have := (hS.2 _ _ this).1
          omega
        have hRest_g : ∀ z ∈ univ \ (Sf ∪ Pc), ∀ i < s, g i ≠ z := by
          intro z hz i hi h
          simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or] at hz
          simp only [hgdef, two, id] at h
          split_ifs at h with hip
          · exact hz.2 (h ▸ mem_image_of_mem c (mem_range.2 (by omega)))
          · exact hz.1 (h ▸ mem_image_of_mem f (mem_range.2 hi))
        have hw_g : ∀ i < s, g i ≠ w := by
          intro i hi h
          simp only [hgdef, two, id] at h
          split_ifs at h with hip
          · have := hc.inj _ _ (by omega) (by omega) h; omega
          · exact hwS i hi h
        -- degree count for `c 0` and `c 1`
        have d0 := deg_split (G := G) (c 0) Sf Pc hdisj
        have d1 := deg_split (G := G) (c 1) Sf Pc hdisj
        rw [← dseg_eq_card_image hSinj] at d0 d1
        have hPsum : (Pc.filter (G.Adj (c 0))).card + (Pc.filter (G.Adj (c 1))).card ≤ 2 * p - 3 := by
          rw [card_filter_eq_sum_bi, card_filter_eq_sum_bi, ← sum_add_distrib, hPc,
            sum_image (fun i hi j hj h => hc.inj i j (mem_range.1 hi) (mem_range.1 hj) h)]
          apply sum_le_two_mul_sub_three _ p hp3
          · intro i
            have := bi_le_one (G.Adj (c 0) (c i)); have := bi_le_one (G.Adj (c 1) (c i)); omega
          · rw [bi_neg (G.irrefl (v := c 0))]; have := bi_le_one (G.Adj (c 1) (c 0)); omega
          · rw [bi_neg (G.irrefl (v := c 1))]; have := bi_le_one (G.Adj (c 0) (c 1)); omega
          · by_cases h0 : G.Adj (c 0) (c (p - 1))
            · rw [bi_pos h0, bi_neg (show ¬ G.Adj (c 1) (c (p - 1)) from fun h1 => hnot w hw_g ⟨h0, h1⟩)]
            · rw [bi_neg h0]; have := bi_le_one (G.Adj (c 1) (c (p - 1))); omega
        have hRsum : ((univ \ (Sf ∪ Pc)).filter (G.Adj (c 0))).card +
            ((univ \ (Sf ∪ Pc)).filter (G.Adj (c 1))).card ≤ (univ \ (Sf ∪ Pc)).card := by
          rw [card_filter_eq_sum_bi, card_filter_eq_sum_bi, ← sum_add_distrib, card_eq_sum_ones]
          apply sum_le_sum
          intro z hz
          by_cases h0 : G.Adj (c 0) z
          · rw [bi_pos h0, bi_neg (show ¬ G.Adj (c 1) z from fun h1 => hnot z (hRest_g z hz) ⟨h0, h1⟩)]
          · rw [bi_neg h0]; have := bi_le_one (G.Adj (c 1) z); omega
        have hRc : (univ \ (Sf ∪ Pc)).card = n - (s + p) := by
          rw [card_univ_sdiff, card_union_of_disjoint hdisj, hSc, hPcc]
        have := hdeg (c 0) (hnotS 0 (by omega))
        have := hdeg (c 1) (hnotS 1 (by omega))
        have := L_ab.1
        omega
      · have := L_uw.1
        have := L_vw.1
        have := L_uv.1
        omega
  exact h25

end Lemma10

section Lemma10b

variable [Fintype V] {s : ℕ} {f : ℕ → V}

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma IsCube.le_card {p : ℕ} {c : ℕ → V} (hc : IsCube G p c) : p ≤ Fintype.card V := by
  have := Fintype.card_le_of_injective (fun i : Fin p => c i)
    (fun i j h => Fin.ext (hc.inj i j i.2 j.2 h))
  simpa using this

/-- **Lemma 10** (Fan–Kierstead, non-extremal case): if every vertex outside an optimal square path
`S` has degree at least `2n/3`, then every edge outside `S` has at most `s+1` neighbours in `S`. -/
theorem lemma10 (hS : Opt G s f)
    (hdeg : ∀ v, (∀ j < s, f j ≠ v) → 2 * Fintype.card V ≤ 3 * G.degree v)
    {x y : V} (hx : ∀ j < s, f j ≠ x) (hy : ∀ j < s, f j ≠ y) (hxy : G.Adj x y) :
    dseg G x f 0 s + dseg G y f 0 s ≤ s + 1 := by
  classical
  by_contra hcon
  push Not at hcon
  let CP : ℕ → Prop := fun p => ∃ c : ℕ → V, IsCube G p c ∧
    ((c 0 = x ∧ c 1 = y) ∨ (c 0 = y ∧ c 1 = x)) ∧ ∀ i < p, ∀ j < s, c i ≠ f j
  have hCP2 : CP 2 := by
    refine ⟨fun i => if i = 0 then x else y, ⟨fun i j hij hj3 hj => ?_, fun i j hi hj h => ?_⟩,
      Or.inl ⟨by simp, by simp⟩, fun i hi j hj => ?_⟩
    · have : i = 0 ∧ j = 1 := by omega
      obtain ⟨rfl, rfl⟩ := this
      simpa using hxy
    · by_contra hne
      have : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp at h; exact hxy.ne h
      · simp at h; exact hxy.ne h.symm
    · show (if i = 0 then x else y) ≠ f j
      split_ifs
      · exact fun h => hx j hj h.symm
      · exact fun h => hy j hj h.symm
  have hn2 : 2 ≤ Fintype.card V := by
    obtain ⟨c, hc, -⟩ := hCP2; exact hc.le_card
  set p := Nat.findGreatest CP (Fintype.card V) with hp
  have hCPp : CP p := Nat.findGreatest_spec hn2 hCP2
  have hp2 : 2 ≤ p := Nat.le_findGreatest hn2 hCP2
  obtain ⟨c, hc, hstart, hcS⟩ := hCPp
  refine lemma10_core hS hdeg hc hp2 hcS (fun z hzS hzc hadj => ?_) ?_
  · -- extending the cube path contradicts maximality
    have hext := hc.extend hzc (fun _ => hadj.1) (fun _ => hadj.2.1) hadj.2.2
    have hle := hext.le_card
    have := Nat.findGreatest_is_greatest (P := CP) (n := Fintype.card V) (k := p + 1)
      (by omega) hle
    apply this
    refine ⟨_, hext, ?_, fun i hi j hj => ?_⟩
    · simp only [show (0 : ℕ) < p by omega, show (1 : ℕ) < p by omega, if_true]; exact hstart
    · show (if i < p then c i else z) ≠ f j
      split_ifs with hip
      · exact hcS i hip j hj
      · exact fun h => hzS j hj h.symm
  · rcases hstart with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1] <;> omega

end Lemma10b

/- ### Existence of optimal square paths -/

section Exist

variable [Fintype V]

omit [DecidableEq V] [Fintype V] in
lemma chords_le (n : ℕ) (f : ℕ → V) (k : ℕ) : chords G n f k ≤ n := by
  unfold chords
  calc _ ≤ (range n).card := card_filter_le _ _
    _ = n := card_range n

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma IsSq.le_card {n : ℕ} {f : ℕ → V} (h : IsSq G n f) : n ≤ Fintype.card V := by
  have := Fintype.card_le_of_injective (fun i : Fin n => f i)
    (fun i j hh => Fin.ext (h.inj i j i.2 j.2 hh))
  simpa using this

omit [DecidableEq V] in
/-- Among the square paths satisfying `Q`, one is longest, then has the most 3-chords, then the
most 4-chords. -/
lemma exists_opt_gen (Q : ℕ → (ℕ → V) → Prop) (hQ : ∀ m g, Q m g → IsSq G m g)
    (hne : ∃ m g, Q m g) :
    ∃ s f, Q s f ∧ ∀ m g, Q m g → m ≤ s ∧ (m = s → chords G s g 3 ≤ chords G s f 3 ∧
      (chords G s g 3 = chords G s f 3 → chords G s g 4 ≤ chords G s f 4)) := by
  classical
  set N := Fintype.card V
  have hbound : ∀ m g, Q m g → m ≤ N := fun m g h => (hQ m g h).le_card
  obtain ⟨m0, g0, hm0⟩ := hne
  -- longest
  set s := Nat.findGreatest (fun m => ∃ g, Q m g) N with hs
  have hsQ : ∃ g, Q s g :=
    Nat.findGreatest_spec (P := fun m => ∃ g, Q m g) (hbound m0 g0 hm0) ⟨g0, hm0⟩
  have hsmax : ∀ m g, Q m g → m ≤ s := fun m g h =>
    Nat.le_findGreatest (P := fun m => ∃ g, Q m g) (hbound m g h) ⟨g, h⟩
  -- most 3-chords
  set k3 := Nat.findGreatest (fun k => ∃ g, Q s g ∧ chords G s g 3 = k) s with hk3
  obtain ⟨g1, hg1⟩ := hsQ
  have hk3Q : ∃ g, Q s g ∧ chords G s g 3 = k3 :=
    Nat.findGreatest_spec (P := fun k => ∃ g, Q s g ∧ chords G s g 3 = k) (chords_le s g1 3)
      ⟨g1, hg1, rfl⟩
  have hk3max : ∀ g, Q s g → chords G s g 3 ≤ k3 := fun g h =>
    Nat.le_findGreatest (P := fun k => ∃ g, Q s g ∧ chords G s g 3 = k) (chords_le s g 3)
      ⟨g, h, rfl⟩
  -- most 4-chords
  obtain ⟨g2, hg2, hg2c⟩ := hk3Q
  set k4 := Nat.findGreatest (fun k => ∃ g, Q s g ∧ chords G s g 3 = k3 ∧ chords G s g 4 = k) s
    with hk4
  have hk4Q : ∃ g, Q s g ∧ chords G s g 3 = k3 ∧ chords G s g 4 = k4 :=
    Nat.findGreatest_spec (P := fun k => ∃ g, Q s g ∧ chords G s g 3 = k3 ∧ chords G s g 4 = k)
      (chords_le s g2 4) ⟨g2, hg2, hg2c, rfl⟩
  have hk4max : ∀ g, Q s g → chords G s g 3 = k3 → chords G s g 4 ≤ k4 := fun g h h3 =>
    Nat.le_findGreatest (P := fun k => ∃ g, Q s g ∧ chords G s g 3 = k3 ∧ chords G s g 4 = k)
      (chords_le s g 4) ⟨g, h, h3, rfl⟩
  obtain ⟨f, hf, hf3, hf4⟩ := hk4Q
  refine ⟨s, f, hf, fun m g hg => ⟨hsmax m g hg, fun hm => ?_⟩⟩
  subst hm
  refine ⟨hf3 ▸ hk3max g hg, fun h3 => hf4 ▸ hk4max g hg (h3.trans hf3)⟩

omit [DecidableEq V] in
lemma exists_opt (v : V) : ∃ s f, Opt G s f := by
  obtain ⟨s, f, hf, hmax⟩ := exists_opt_gen (G := G) (fun m g => IsSq G m g) (fun m g h => h)
    ⟨1, fun _ => v, isSq_one v⟩
  exact ⟨s, f, hf, fun m g hg => hmax m g hg⟩

omit [DecidableEq V] in
lemma exists_optStart {a b : V} (hab : G.Adj a b) : ∃ s f, OptStart G s f ∧ f 0 = a ∧ f 1 = b ∧
    2 ≤ s := by
  have h2 : IsSq G 2 (fun i => if i = 0 then a else b) := by
    refine isSq_of_pairs _ (fun i j hij hj2 hj => ?_) (fun i j hi hj h => ?_)
    · have : i = 0 ∧ j = 1 := by omega
      obtain ⟨rfl, rfl⟩ := this
      simpa using hab
    · by_contra hne
      have : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp at h; exact hab.ne h
      · simp at h; exact hab.ne h.symm
  obtain ⟨s, f, ⟨hf, hf0, hf1⟩, hmax⟩ := exists_opt_gen (G := G)
    (fun m g => IsSq G m g ∧ g 0 = a ∧ g 1 = b) (fun m g h => h.1)
    ⟨2, _, h2, by simp, by simp⟩
  refine ⟨s, f, ⟨hf, fun m g hg h0 h1 => hmax m g ⟨hg, h0.trans hf0, h1.trans hf1⟩⟩, hf0, hf1, ?_⟩
  exact (hmax 2 _ ⟨h2, by simp, by simp⟩).1

end Exist

/- ### Lemma 11 -/

section Lemma11

variable [Fintype V]

/-- **Lemma 11** (Fan–Kierstead). If `δ(G) ≥ 2n/3` and every edge has degree sum at least
`5(n-1)/3`, then every ordered edge starts a hamiltonian square path. -/
theorem lemma11 (hδ : ∀ v, 2 * Fintype.card V ≤ 3 * G.degree v)
    (hedge : ∀ a b, G.Adj a b → 5 * (Fintype.card V - 1) ≤ 3 * (G.degree a + G.degree b))
    {a b : V} (hab : G.Adj a b) :
    ∃ f, IsSq G (Fintype.card V) f ∧ f 0 = a ∧ f 1 = b := by
  classical
  set n := Fintype.card V with hn
  obtain ⟨p, g, hopt, hg0, hg1, hp2⟩ := exists_optStart (G := G) hab
  have hpn : p ≤ n := hopt.1.le_card
  set Pset := (range p).image g with hPset
  have hPc : Pset.card = p := card_image_range hopt.1.inj
  have hmemP : ∀ i < p, g i ∈ Pset := fun i hi => mem_image_of_mem g (mem_range.2 hi)
  have hnotP : ∀ z, z ∉ Pset → ∀ i < p, g i ≠ z := fun z hz i hi h => hz (h ▸ hmemP i hi)
  -- a vertex outside `P` adjacent to the last two vertices could be appended
  have hcomm : ∀ z, G.Adj (g (p - 2)) z → G.Adj (g (p - 1)) z → z ∈ Pset := by
    intro z h2 h1
    by_contra hz
    have hc := isSq_cat hopt.1 (isSq_one z) (fun i hi j _ h => hnotP z hz i hi h)
      (fun _ _ => h1) (fun _ _ => h2) (fun _ h => by omega)
    have := (hopt.2 _ _ hc (by simp [cat, show (0 : ℕ) < p by omega])
      (by simp [cat, show (1 : ℕ) < p by omega])).1
    omega
  -- hence `3p ≥ 2n + 1`
  have hp3 : 2 * n + 1 ≤ 3 * p := by
    have hxy : G.Adj (g (p - 2)) (g (p - 1)) := by
      have := hopt.1.adj1 (p - 2) (by omega); rwa [show p - 2 + 1 = p - 1 by omega] at this
    have hunion := card_union_add_card_inter (G.neighborFinset (g (p - 2)))
      (G.neighborFinset (g (p - 1)))
    have hu : (G.neighborFinset (g (p - 2)) ∪ G.neighborFinset (g (p - 1))).card ≤ n :=
      card_le_univ _
    have hi : (G.neighborFinset (g (p - 2)) ∩ G.neighborFinset (g (p - 1))) ⊆
        (Pset.erase (g (p - 2))).erase (g (p - 1)) := by
      intro z hz
      simp only [mem_inter, SimpleGraph.mem_neighborFinset] at hz
      refine mem_erase.2 ⟨fun h => G.irrefl (h ▸ hz.2), mem_erase.2 ⟨fun h => G.irrefl (h ▸ hz.1),
        hcomm z hz.1 hz.2⟩⟩
    have hic := card_le_card hi
    rw [card_erase_of_mem (mem_erase.2 ⟨fun h => hxy.ne h.symm, hmemP _ (by omega)⟩),
      card_erase_of_mem (hmemP _ (by omega)), hPc] at hic
    rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hunion
    have := hedge _ _ hxy
    omega
  by_cases hpn' : p = n
  · exact ⟨g, hpn' ▸ hopt.1, hg0, hg1⟩
  exfalso
  -- a vertex `v` outside `P`, with a neighbour `w` outside `P`
  obtain ⟨v, hv⟩ : ∃ v, v ∉ Pset := by
    by_contra h
    push Not at h
    have : Pset = univ := eq_univ_of_forall h
    rw [this, card_univ] at hPc
    omega
  have L3v := lemma3 hopt hp2 (hnotP v hv)
  have dv := deg_split (G := G) v Pset ∅ (disjoint_empty_right _)
  simp only [filter_empty, card_empty, add_zero, union_empty] at dv
  rw [← dseg_eq_card_image hopt.1.inj] at dv
  have hδv := hδ v
  obtain ⟨w, hw⟩ : ∃ w, w ∈ (univ \ Pset).filter (G.Adj v) := by
    by_contra h
    push Not at h
    have : (univ \ Pset).filter (G.Adj v) = ∅ := eq_empty_of_forall_notMem h
    rw [this, card_empty] at dv
    omega
  simp only [mem_filter, mem_sdiff, mem_univ, true_and] at hw
  have L3w := lemma3 hopt hp2 (hnotP w hw.1)
  have dw := deg_split (G := G) w Pset ∅ (disjoint_empty_right _)
  simp only [filter_empty, card_empty, add_zero, union_empty] at dw
  rw [← dseg_eq_card_image hopt.1.inj] at dw
  have hout : ∀ u ∉ Pset, ((univ \ Pset).filter (G.Adj u)).card + 1 ≤ n - p := by
    intro u hu
    have := card_filter_adj_self_le (G := G) (A := univ \ Pset) (v := u)
      (by simp only [mem_sdiff, mem_univ, true_and]; exact hu)
    rwa [card_univ_sdiff, hPc] at this
  have ov := hout v hv
  have ow := hout w hw.1
  have := hedge v w hw.2
  omega

end Lemma11

/- ### Counting helpers for the end game -/

section EndHelpers

omit [DecidableEq V] in
/-- No two consecutive neighbours: at most `(q+1)/2` neighbours in a segment of length `q`. -/
lemma no_consec_bound (x : V) (f : ℕ → V) :
    ∀ q a, (∀ i, a ≤ i → i + 1 < a + q → ¬ (G.Adj x (f i) ∧ G.Adj x (f (i + 1)))) →
      2 * dseg G x f a q ≤ q + 1 := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro a h
  rcases Nat.lt_or_ge q 2 with hq | hq
  · have := dseg_le (G := G) x f a q; omega
  · have e1 := dseg_add (G := G) x f a 1 (q - 1)
    have e2 := dseg_add (G := G) x f (a + 1) 1 (q - 2)
    rw [show 1 + (q - 1) = q by omega] at e1
    rw [show 1 + (q - 2) = q - 1 by omega, show a + 1 + 1 = a + 2 by omega] at e2
    rw [dseg_one] at e1 e2
    have ih1 := ih (q - 1) (by omega) (a + 1) (fun i h1 h2 => h i (by omega) (by omega))
    have ih2 := ih (q - 2) (by omega) (a + 2) (fun i h1 h2 => h i (by omega) (by omega))
    have hnot := h a (le_refl a) (by omega)
    by_cases h0 : G.Adj x (f a)
    · have h1 : ¬ G.Adj x (f (a + 1)) := fun h1 => hnot ⟨h0, h1⟩
      rw [if_pos h0] at e1
      rw [if_neg h1] at e2
      omega
    · rw [if_neg h0] at e1
      omega

/-- If no consecutive pair has count sum `4`, the total is at most `(3q+1)/2`. -/
lemma pair_bound (c : ℕ → ℕ) (hc : ∀ i, c i ≤ 2) :
    ∀ q a, (∀ i, a ≤ i → i + 1 < a + q → c i + c (i + 1) ≤ 3) →
      2 * ∑ i ∈ Ico a (a + q), c i ≤ 3 * q + 1 := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro a h
  rcases Nat.lt_or_ge q 2 with hq | hq
  · interval_cases q
    · simp
    · simp only [Nat.Ico_succ_singleton, sum_singleton]; have := hc a; omega
  · have ih2 := ih (q - 2) (by omega) (a + 2) (fun i h1 h2 => h i (by omega) (by omega))
    have hp := h a (le_refl a) (by omega)
    rw [← sum_Ico_consecutive _ (show a ≤ a + 2 by omega) (show a + 2 ≤ a + q by omega),
      show a + q = a + 2 + (q - 2) by omega]
    have : ∑ i ∈ Ico a (a + 2), c i = c a + c (a + 1) := by
      rw [sum_Ico_eq_sum_range, show a + 2 - a = 2 by omega]; simp [sum_range_succ]
    rw [this]
    omega

variable (G) in
/-- A triple of consecutive vertices of `S` is good if every vertex outside `S` is adjacent to at
most one of them. -/
def Good (s : ℕ) (f : ℕ → V) (j : ℕ) : Prop :=
  ∀ x, (∀ i < s, f i ≠ x) → dseg G x f j 3 ≤ 1

omit [DecidableEq V] in
lemma good_triples_bound {s : ℕ} {f : ℕ → V} {x : V} (hx : ∀ i < s, f i ≠ x) (a : ℕ) :
    ∀ t, (∀ i < t, Good G s f (a + 3 * i)) → dseg G x f a (3 * t) ≤ t := by
  intro t
  induction t with
  | zero => intro _; simp [dseg]
  | succ t ih =>
    intro h
    have := dseg_add (G := G) x f a (3 * t) 3
    rw [show 3 * t + 3 = 3 * (t + 1) by ring] at this
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h t (by omega) x hx
    omega

end EndHelpers

/- ### The end game of the main proof -/

section EndGame

variable [Fintype V] {s h : ℕ} {f : ℕ → V}

lemma deg_eq_dseg_add (hinj : ∀ i j, i < s → j < s → f i = f j → i = j) (v : V) :
    G.degree v = dseg G v f 0 s + ((univ \ (range s).image f).filter (G.Adj v)).card := by
  have d := deg_split (G := G) v ((range s).image f) ∅ (disjoint_empty_right _)
  simp only [filter_empty, card_empty, add_zero, union_empty] at d
  rw [← dseg_eq_card_image hinj] at d
  exact d

lemma endgame (hS : Opt G s f) (hn : Fintype.card V = s + h) (hh : 1 ≤ h)
    (hδ : ∀ v, 2 * (s + h) ≤ 3 * G.degree v)
    (hHam : ∀ x y, (∀ i < s, f i ≠ x) → (∀ i < s, f i ≠ y) → G.Adj x y →
      ∃ P, IsSq G h P ∧ P 0 = x ∧ P 1 = y ∧ ∀ i < h, ∀ j < s, P i ≠ f j)
    (h35 : ∀ x, (∀ i < s, f i ≠ x) → ∀ i < s, G.Adj x (f i) →
      ∃ y, (∀ i < s, f i ≠ y) ∧ G.Adj x y ∧ G.Adj y (f i))
    (h36 : ∀ x, (∀ i < s, f i ≠ x) → ∀ i, i + 1 < s → ¬ (G.Adj x (f i) ∧ G.Adj x (f (i + 1))))
    (h34 : 3 * s + 3 ≤ 2 * (s + h)) (h37 : h + 1 ≤ s)
    {t t' : ℕ} (htt : t ≤ t') (hsum : 3 * t + 3 * t' ≤ s)
    (hgood1 : ∀ i < t, Good G s f (3 * i)) (hgood2 : ∀ i < t', Good G s f (s - 3 - 3 * i))
    (hnext : 3 * t + 3 * t' + 3 ≤ s → ¬ Good G s f (3 * t)) : False := by
  classical
  have hSinj := hS.1.inj
  set Sset := (range s).image f with hSset
  have hSc : Sset.card = s := card_image_range hSinj
  have hHc : (univ \ Sset).card = h := by rw [card_univ_sdiff, hSc, hn]; omega
  have hnotS_of : ∀ z ∈ univ \ Sset, ∀ i < s, f i ≠ z := by
    intro z hz i hi h'
    simp only [mem_sdiff, mem_univ, true_and] at hz
    exact hz (h' ▸ mem_image_of_mem f (mem_range.2 hi))
  -- vertices outside `S` have at most `h - 1` neighbours outside `S`
  have hout : ∀ v, (∀ i < s, f i ≠ v) → ((univ \ Sset).filter (G.Adj v)).card + 1 ≤ h := by
    intro v hv
    have hvm : v ∈ univ \ Sset := by
      simp only [mem_sdiff, mem_univ, true_and, hSset, mem_image, mem_range, not_exists, not_and]
      exact fun i hi => hv i hi
    have := card_filter_adj_self_le (G := G) hvm
    rwa [hHc] at this
  -- Step 1: counting at a vertex outside `S`
  obtain ⟨v0, hv0⟩ : ∃ v, v ∈ univ \ Sset := by
    by_contra hne
    push Not at hne
    have : univ \ Sset = ∅ := eq_empty_of_forall_notMem hne
    rw [this, card_empty] at hHc
    omega
  have hv0S := hnotS_of v0 hv0
  set r := s - 3 * t - 3 * t' with hr
  have hd1 := good_triples_bound (G := G) hv0S 0 t (fun i hi => by simpa using hgood1 i hi)
  have hd3 := good_triples_bound (G := G) hv0S (s - 3 * t') t' (fun k hk => by
    have := hgood2 (t' - 1 - k) (by omega)
    rwa [show s - 3 - 3 * (t' - 1 - k) = s - 3 * t' + 3 * k by omega] at this)
  have hd2 := no_consec_bound (G := G) v0 f r (3 * t) (fun i h1 h2 => h36 v0 hv0S i (by omega))
  have hsplit1 := dseg_add (G := G) v0 f 0 (3 * t) (r + 3 * t')
  have hsplit2 := dseg_add (G := G) v0 f (0 + 3 * t) r (3 * t')
  rw [show 3 * t + (r + 3 * t') = s by omega] at hsplit1
  rw [show 0 + 3 * t + r = s - 3 * t' by omega] at hsplit2
  simp only [Nat.zero_add] at hsplit1 hsplit2
  have hdeg0 : G.degree v0 = dseg G v0 f 0 s + ((univ \ Sset).filter (G.Adj v0)).card :=
    deg_eq_dseg_add (G := G) hSinj v0
  have hδ0 := hδ v0
  have ho0 := hout v0 hv0S
  have hr5 : 5 ≤ r := by omega
  have h2h : s + 6 * t + 3 ≤ 2 * h := by omega
  -- Step 2: the triple at `a = 3t` is not good
  set a := 3 * t with ha
  have hng := hnext (by omega)
  unfold Good at hng
  push Not at hng
  obtain ⟨x, hxS, hx2⟩ := hng
  have e1 := dseg_add (G := G) x f a 1 2
  have e2 := dseg_add (G := G) x f (a + 1) 1 1
  rw [dseg_one, show 1 + 2 = 3 by rfl] at e1
  rw [dseg_one, dseg_one, show 1 + 1 = 2 by rfl, show a + 1 + 1 = a + 2 by omega] at e2
  have nx01 := h36 x hxS a (by omega)
  have nx12 := h36 x hxS (a + 1) (by omega)
  rw [show a + 1 + 1 = a + 2 by omega] at nx12
  have hxa : G.Adj x (f a) ∧ G.Adj x (f (a + 2)) := by
    by_cases h1 : G.Adj x (f (a + 1))
    · have h0 : ¬ G.Adj x (f a) := fun h0 => nx01 ⟨h0, h1⟩
      have h2 : ¬ G.Adj x (f (a + 2)) := fun h2 => nx12 ⟨h1, h2⟩
      rw [if_neg h0] at e1
      rw [if_pos h1, if_neg h2] at e2
      omega
    · rw [if_neg h1] at e2
      by_cases h0 : G.Adj x (f a) <;> by_cases h2 : G.Adj x (f (a + 2))
      · exact ⟨h0, h2⟩
      · rw [if_neg h2] at e2; rw [if_pos h0] at e1; omega
      · rw [if_pos h2] at e2; rw [if_neg h0] at e1; omega
      · rw [if_neg h2] at e2; rw [if_neg h0] at e1; omega
  obtain ⟨y, hyS, hxy, hyf⟩ := h35 x hxS (a + 2) (by omega) hxa.2
  obtain ⟨P, hP, hP0, hP1, hPS⟩ := hHam x y hxS hyS hxy
  -- the path `X = f (a+1), f a, f (a+2), P`
  let T : ℕ → V := fun i => f (if i = 0 then a + 1 else if i = 1 then a else a + 2)
  have hT : IsSq G 3 T := hS.1.isSq_comp_close (fun i => if i = 0 then a + 1 else if i = 1 then a else a + 2)
    (fun i hi => by split_ifs <;> omega) (fun i j hi hj hh => by split_ifs at hh <;> omega)
    (fun i j hij hj2 hj => by split_ifs <;> omega)
  have hX : IsSq G (3 + h) (cat 3 T P) := isSq_cat hT hP
    (fun i hi j hj he => hPS j hj _ (show (if i = 0 then a + 1 else if i = 1 then a else a + 2) < s
      by split_ifs <;> omega) he.symm)
    (fun _ _ => by simpa [T, hP0] using hxa.2.symm)
    (fun _ _ => by simpa [T, hP0] using hxa.1.symm)
    (fun _ _ => by simpa [T, hP1] using hyf.symm)
  set X := cat 3 T P with hXdef
  have hX0 : X 0 = f (a + 1) := by simp [hXdef, cat, T]
  have hX1 : X 1 = f a := by simp [hXdef, cat, T]
  have hXS : ∀ j < 3 + h, ∀ k < s, (k < a ∨ a + 3 ≤ k) → X j ≠ f k := by
    intro j hj k hk hka he
    simp only [hXdef, cat] at he
    split_ifs at he with hj3
    · simp only [T] at he
      have := hSinj _ _ (by split_ifs <;> omega) hk he
      split_ifs at this <;> omega
    · exact hPS _ (by omega) k hk he
  -- (3.12): no consecutive pair of `L` is joined to both `f a` and `f (a+1)`
  have hno4 : ∀ i, a + 3 ≤ i → i + 1 < s → ¬ (G.Adj (f a) (f i) ∧ G.Adj (f a) (f (i + 1)) ∧
      G.Adj (f (a + 1)) (f i) ∧ G.Adj (f (a + 1)) (f (i + 1))) := by
    intro i hi1 hi2 ⟨k1, k2, k3, k4⟩
    have hQ1 := hS.1.revSuffix i
    have c1 := isSq_cat hQ1 hX (fun j hj k hk he => hXS k hk (s - 1 - j) (by omega) (Or.inr (by omega))
        he.symm)
      (fun _ _ => by rw [hX0, show s - 1 - (s - i - 1) = i by omega]; exact k3.symm)
      (fun _ _ => by rw [hX0, show s - 1 - (s - i - 2) = i + 1 by omega]; exact k4.symm)
      (fun _ _ => by rw [hX1, show s - 1 - (s - i - 1) = i by omega]; exact k1.symm)
    have l1 := (hS.2 _ _ c1).1
    have hQ2 := (hS.1.shift (a + 3)).take (m := i - a - 1) (by omega)
    have c2 := isSq_cat hQ2 hX (fun j hj k hk he => hXS k hk (a + 3 + j) (by omega)
        (Or.inr (by omega)) he.symm)
      (fun _ _ => by
        rw [hX0, show a + 3 + (i - a - 1 - 1) = i + 1 by omega]; exact k4.symm)
      (fun _ _ => by
        rw [hX0, show a + 3 + (i - a - 1 - 2) = i by omega]; exact k3.symm)
      (fun _ _ => by
        rw [hX1, show a + 3 + (i - a - 1 - 1) = i + 1 by omega]; exact k2.symm)
    have l2 := (hS.2 _ _ c2).1
    omega
  -- Step 3: counting at the edge `e = f a f (a+1)`
  set l := s - a - 3 with hl
  have hcle : ∀ j, cnt2 G (f a) (f (a + 1)) f j ≤ 2 := cnt2_le (f a) (f (a + 1)) f
  have hsumS := dseg_pair_eq_sum (G := G) (f a) (f (a + 1)) f 0 s
  rw [zero_add, ← sum_Ico_consecutive _ (show 0 ≤ a by omega) (show a ≤ s by omega),
    ← sum_Ico_consecutive _ (show a ≤ a + 3 by omega) (show a + 3 ≤ s by omega)] at hsumS
  have hT3 : ∑ j ∈ Ico a (a + 3), cnt2 G (f a) (f (a + 1)) f j ≤ 4 := by
    rw [sum_Ico_eq_sum_range, show a + 3 - a = 3 by omega]
    simp only [sum_range_succ, sum_range_zero, zero_add, add_zero]
    have c0 : cnt2 G (f a) (f (a + 1)) f a ≤ 1 := by
      unfold cnt2; rw [bi_neg (G.irrefl (v := f a))]; have := bi_le_one (G.Adj (f (a + 1)) (f a))
      omega
    have c1 : cnt2 G (f a) (f (a + 1)) f (a + 1) ≤ 1 := by
      unfold cnt2; rw [bi_neg (G.irrefl (v := f (a + 1)))]
      have := bi_le_one (G.Adj (f a) (f (a + 1))); omega
    have c2 := hcle (a + 2)
    omega
  have hL3 : 2 * ∑ j ∈ Ico (a + 3) s, cnt2 G (f a) (f (a + 1)) f j ≤ 3 * l + 1 := by
    have := pair_bound (cnt2 G (f a) (f (a + 1)) f) hcle l (a + 3) (fun i h1 h2 => by
      by_contra hc
      have hi2 : cnt2 G (f a) (f (a + 1)) f i = 2 := by have := hcle i; have := hcle (i + 1); omega
      have hi3 : cnt2 G (f a) (f (a + 1)) f (i + 1) = 2 := by
        have := hcle i; have := hcle (i + 1); omega
      obtain ⟨k1, k3⟩ := cnt2_two hi2
      obtain ⟨k2, k4⟩ := cnt2_two hi3
      exact hno4 i h1 (by omega) ⟨k1, k2, k3, k4⟩)
    rwa [show a + 3 + l = s by omega] at this
  have hHe : ((univ \ Sset).filter (G.Adj (f a))).card +
      ((univ \ Sset).filter (G.Adj (f (a + 1)))).card ≤ h := by
    rw [card_filter_eq_sum_bi, card_filter_eq_sum_bi, ← sum_add_distrib, ← hHc, card_eq_sum_ones]
    apply sum_le_sum
    intro z hz
    have hn36 := h36 z (hnotS_of z hz) a (by omega)
    by_cases h0 : G.Adj (f a) z
    · rw [bi_pos h0, bi_neg (show ¬ G.Adj (f (a + 1)) z from fun h1 => hn36 ⟨h0.symm, h1.symm⟩)]
    · rw [bi_neg h0]; have := bi_le_one (G.Adj (f (a + 1)) z); omega
  have dfa : G.degree (f a) = dseg G (f a) f 0 s + ((univ \ Sset).filter (G.Adj (f a))).card :=
    deg_eq_dseg_add (G := G) hSinj (f a)
  have dfa1 : G.degree (f (a + 1)) =
      dseg G (f (a + 1)) f 0 s + ((univ \ Sset).filter (G.Adj (f (a + 1)))).card :=
    deg_eq_dseg_add (G := G) hSinj (f (a + 1))
  have hδa := hδ (f a)
  have hδa1 := hδ (f (a + 1))
  -- hence a consecutive pair of `M` joined to both `f a` and `f (a+1)`
  obtain ⟨i, hia, hi4⟩ : ∃ i, i + 1 < a ∧
      4 ≤ cnt2 G (f a) (f (a + 1)) f i + cnt2 G (f a) (f (a + 1)) f (i + 1) := by
    by_contra hc
    push Not at hc
    have hM := pair_bound (cnt2 G (f a) (f (a + 1)) f) hcle a 0 (fun i _ h2 => by
      have := hc i (by omega); omega)
    rw [zero_add] at hM
    have hD2 : G.degree (f a) + G.degree (f (a + 1)) ≤
        ∑ i ∈ Ico 0 a, cnt2 G (f a) (f (a + 1)) f i + 4 +
          ∑ i ∈ Ico (a + 3) s, cnt2 G (f a) (f (a + 1)) f i + h := by omega
    have h2a : s + 2 * a + 3 ≤ 2 * h := by omega
    have hl' : l + a + 3 = s := by omega
    have e1 : 4 * (s + h) ≤ 3 * (∑ i ∈ Ico 0 a, cnt2 G (f a) (f (a + 1)) f i + 4 +
          ∑ i ∈ Ico (a + 3) s, cnt2 G (f a) (f (a + 1)) f i + h) := by omega
    clear_value a l
    generalize ∑ i ∈ Ico 0 a, cnt2 G (f a) (f (a + 1)) f i = SM at e1 hM
    generalize ∑ i ∈ Ico (a + 3) s, cnt2 G (f a) (f (a + 1)) f i = SL at e1 hL3
    omega
  have hci : cnt2 G (f a) (f (a + 1)) f i = 2 := by
    have := hcle i; have := hcle (i + 1); omega
  have hci1 : cnt2 G (f a) (f (a + 1)) f (i + 1) = 2 := by
    have := hcle i; have := hcle (i + 1); omega
  obtain ⟨m1, m3⟩ := cnt2_two hci
  obtain ⟨m2, m4⟩ := cnt2_two hci1
  -- Step 4: the paths `W = f i, f (i+1), X` and `W' = f (i+1), f i, X`
  have hW2 : IsSq G 2 (fun k => f (i + k)) := (hS.1.shift i).take (by omega)
  have hW2' : IsSq G 2 (fun k => f (i + 1 - k)) := by
    refine isSq_of_pairs _ (fun k k' hkk hk2 hk => ?_) (fun k k' hk hk' hh => ?_)
    · have : k = 0 ∧ k' = 1 := by omega
      obtain ⟨rfl, rfl⟩ := this
      simpa using (hS.1.adj1 i (by omega)).symm
    · have := hSinj _ _ (by omega) (by omega) hh; omega
  have hW := isSq_cat hW2 hX (fun k hk j hj he => hXS j hj (i + k) (by omega) (Or.inl (by omega)) he.symm)
    (fun _ _ => by rw [hX0, show i + (2 - 1) = i + 1 by omega]; exact m4.symm)
    (fun _ _ => by rw [hX0, show i + (2 - 2) = i by omega]; exact m3.symm)
    (fun _ _ => by rw [hX1, show i + (2 - 1) = i + 1 by omega]; exact m2.symm)
  have hW' := isSq_cat hW2' hX (fun k hk j hj he => hXS j hj (i + 1 - k) (by omega) (Or.inl (by omega))
      he.symm)
    (fun _ _ => by rw [hX0, show i + 1 - (2 - 1) = i by omega]; exact m3.symm)
    (fun _ _ => by rw [hX0, show i + 1 - (2 - 2) = i + 1 by omega]; exact m4.symm)
    (fun _ _ => by rw [hX1, show i + 1 - (2 - 1) = i by omega]; exact m1.symm)
  set W := cat 2 (fun k => f (i + k)) X with hWdef
  set W' := cat 2 (fun k => f (i + 1 - k)) X with hW'def
  have hW0 : W 0 = f i := by simp [hWdef, cat]
  have hW1 : W 1 = f (i + 1) := by simp [hWdef, cat]
  have hW'0 : W' 0 = f (i + 1) := by simp [hW'def, cat]
  have hW'1 : W' 1 = f i := by simp [hW'def, cat]
  have hWS : ∀ j < 2 + (3 + h), ∀ k < s, a + 3 ≤ k → W j ≠ f k := by
    intro j hj k hk hka he
    simp only [hWdef, cat] at he
    split_ifs at he with hj2
    · have := hSinj _ _ (by omega) hk he; omega
    · exact hXS _ (by omega) k hk (Or.inr hka) he
  have hW'S : ∀ j < 2 + (3 + h), ∀ k < s, a + 3 ≤ k → W' j ≠ f k := by
    intro j hj k hk hka he
    simp only [hW'def, cat] at he
    split_ifs at he with hj2
    · have := hSinj _ _ (by omega) hk he; omega
    · exact hXS _ (by omega) k hk (Or.inr hka) he
  -- Lemma 8 for the pair `f i, f (i+1)` along `L`
  have h8 := lemma8_count (cnt2 G (f i) (f (i + 1)) (fun j => f (a + 3 + j)))
    (cnt2_le _ _ _) l
    (fun j hj h2 => by
      obtain ⟨p1, p2⟩ := cnt2_two h2
      have hQ := hS.1.revSuffix (a + 3 + j)
      apply cnt2_zero
      · intro hq
        have c := isSq_cat hQ hW (fun k hk j' hj' he => hWS j' hj' (s - 1 - k) (by omega) (by omega) he.symm)
          (fun _ _ => by rw [hW0, show s - 1 - (s - (a + 3 + j) - 1) = a + 3 + j by omega]; exact p1.symm)
          (fun _ _ => by
            rw [hW0, show s - 1 - (s - (a + 3 + j) - 2) = a + 3 + (j + 1) by omega]; exact hq.symm)
          (fun _ _ => by rw [hW1, show s - 1 - (s - (a + 3 + j) - 1) = a + 3 + j by omega]; exact p2.symm)
        have := (hS.2 _ _ c).1
        clear_value a l
        omega
      · intro hq
        have c := isSq_cat hQ hW' (fun k hk j' hj' he => hW'S j' hj' (s - 1 - k) (by omega) (by omega) he.symm)
          (fun _ _ => by rw [hW'0, show s - 1 - (s - (a + 3 + j) - 1) = a + 3 + j by omega]; exact p2.symm)
          (fun _ _ => by
            rw [hW'0, show s - 1 - (s - (a + 3 + j) - 2) = a + 3 + (j + 1) by omega]; exact hq.symm)
          (fun _ _ => by rw [hW'1, show s - 1 - (s - (a + 3 + j) - 1) = a + 3 + j by omega]; exact p1.symm)
        have := (hS.2 _ _ c).1
        clear_value a l
        omega)
    (fun j hj1 hj2 h2 => by
      obtain ⟨p1, p2⟩ := cnt2_two h2
      have hQ := (hS.1.shift (a + 3)).take (m := j + 1) (by omega)
      apply cnt2_zero
      · intro hq
        have c := isSq_cat hQ hW (fun k hk j' hj' he => hWS j' hj' (a + 3 + k) (by omega) (by omega) he.symm)
          (fun _ _ => by rw [hW0, show j + 1 - 1 = j by omega]; exact p1.symm)
          (fun _ _ => by rw [hW0, show a + 3 + (j + 1 - 2) = a + 3 + (j - 1) by omega]; exact hq.symm)
          (fun _ _ => by rw [hW1, show j + 1 - 1 = j by omega]; exact p2.symm)
        have := (hS.2 _ _ c).1
        clear_value a l
        omega
      · intro hq
        have c := isSq_cat hQ hW' (fun k hk j' hj' he => hW'S j' hj' (a + 3 + k) (by omega) (by omega) he.symm)
          (fun _ _ => by rw [hW'0, show j + 1 - 1 = j by omega]; exact p2.symm)
          (fun _ _ => by rw [hW'0, show a + 3 + (j + 1 - 2) = a + 3 + (j - 1) by omega]; exact hq.symm)
          (fun _ _ => by rw [hW'1, show j + 1 - 1 = j by omega]; exact p1.symm)
        have := (hS.2 _ _ c).1
        clear_value a l
        omega)
  -- Step 5: degree count for `f i, f (i+1)`
  have hsumI := dseg_pair_eq_sum (G := G) (f i) (f (i + 1)) f 0 s
  rw [zero_add, ← sum_Ico_consecutive _ (show 0 ≤ a by omega) (show a ≤ s by omega),
    ← sum_Ico_consecutive _ (show a ≤ a + 3 by omega) (show a + 3 ≤ s by omega)] at hsumI
  have hLI : ∑ j ∈ Ico (a + 3) s, cnt2 G (f i) (f (i + 1)) f j =
      ∑ j ∈ range l, cnt2 G (f i) (f (i + 1)) (fun j => f (a + 3 + j)) j := by
    rw [sum_Ico_eq_sum_range, show s - (a + 3) = l by omega]
    rfl
  have hMI := dseg_pair_eq_sum (G := G) (f i) (f (i + 1)) f 0 a
  rw [zero_add] at hMI
  have hTI := dseg_pair_eq_sum (G := G) (f i) (f (i + 1)) f a 3
  have hMi := dseg_add_card_le (G := G) (f i) f 0 a {i} (by
    intro k hk; rw [mem_singleton] at hk; subst hk; simp only [mem_Ico]; omega)
    (fun k hk => by rw [mem_singleton] at hk; subst hk; exact G.irrefl)
  have hMi1 := dseg_add_card_le (G := G) (f (i + 1)) f 0 a {i + 1} (by
    intro k hk; rw [mem_singleton] at hk; subst hk; simp only [mem_Ico]; omega)
    (fun k hk => by rw [mem_singleton] at hk; subst hk; exact G.irrefl)
  rw [card_singleton] at hMi hMi1
  have hTi := dseg_le (G := G) (f i) f a 3
  have hTi1 := dseg_le (G := G) (f (i + 1)) f a 3
  have hHI : ((univ \ Sset).filter (G.Adj (f i))).card +
      ((univ \ Sset).filter (G.Adj (f (i + 1)))).card ≤ h := by
    rw [card_filter_eq_sum_bi, card_filter_eq_sum_bi, ← sum_add_distrib, ← hHc, card_eq_sum_ones]
    apply sum_le_sum
    intro z hz
    have hn36 := h36 z (hnotS_of z hz) i (by omega)
    by_cases h0 : G.Adj (f i) z
    · rw [bi_pos h0, bi_neg (show ¬ G.Adj (f (i + 1)) z from fun h1 => hn36 ⟨h0.symm, h1.symm⟩)]
    · rw [bi_neg h0]; have := bi_le_one (G.Adj (f (i + 1)) z); omega
  have dfi : G.degree (f i) = dseg G (f i) f 0 s + ((univ \ Sset).filter (G.Adj (f i))).card :=
    deg_eq_dseg_add (G := G) hSinj (f i)
  have dfi1 : G.degree (f (i + 1)) =
      dseg G (f (i + 1)) f 0 s + ((univ \ Sset).filter (G.Adj (f (i + 1)))).card :=
    deg_eq_dseg_add (G := G) hSinj (f (i + 1))
  have hδi := hδ (f i)
  have hδi1 := hδ (f (i + 1))
  have h2a5 : 2 * a + 5 ≤ s := by omega
  rw [hLI] at hsumI
  clear_value a l
  generalize ∑ j ∈ range l, cnt2 G (f i) (f (i + 1)) (fun j => f (a + 3 + j)) j = SL at hsumI h8
  generalize ∑ x ∈ Ico 0 a, cnt2 G (f i) (f (i + 1)) f x = SM at hsumI hMI
  generalize ∑ x ∈ Ico a (a + 3), cnt2 G (f i) (f (i + 1)) f x = ST at hsumI hTI
  omega

end EndGame

/- ### Supporting lemmas for the main induction -/

section MainSupport

omit [DecidableEq V] in
lemma Opt.rev {s : ℕ} {f : ℕ → V} (h : Opt G s f) : Opt G s (rev s f) := by
  refine ⟨h.1.rev, fun m g hg => ?_⟩
  obtain ⟨hle, hc⟩ := h.2 m g hg
  refine ⟨hle, fun hm => ?_⟩
  rw [chords_rev, chords_rev]
  exact hc hm

omit [DecidableEq V] in
lemma good_rev {s : ℕ} {f : ℕ → V} {j : ℕ} (hj : j + 3 ≤ s) :
    Good G s (rev s f) j ↔ Good G s f (s - 3 - j) := by
  have hnot : ∀ x, (∀ i < s, rev s f i ≠ x) ↔ (∀ i < s, f i ≠ x) := by
    intro x
    constructor
    · intro hx i hi he
      exact hx (s - 1 - i) (by omega) (by simp only [rev]; rw [show s - 1 - (s - 1 - i) = i by omega]; exact he)
    · intro hx i hi he
      exact hx (s - 1 - i) (by omega) he
  unfold Good
  constructor
  · intro H x hx
    have := H x ((hnot x).2 hx)
    have e := dseg_rev (G := G) (n := s) x f (a := s - 3 - j) (q := 3) (by omega)
    rw [show s - (s - 3 - j + 3) = j by omega] at e
    omega
  · intro H x hx
    have := H x ((hnot x).1 hx)
    have e := dseg_rev (G := G) (n := s) x f (a := s - 3 - j) (q := 3) (by omega)
    rw [show s - (s - 3 - j + 3) = j by omega] at e
    omega

variable [Fintype V]

omit [DecidableEq V] in
lemma degree_induce (W : Set V) [DecidablePred (· ∈ W)] (w : W) :
    (G.induce W).degree w = (univ.filter (fun u => u ∈ W ∧ G.Adj w.1 u)).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  rw [← card_map (Function.Embedding.subtype (· ∈ W))]
  congr 1
  ext u
  simp only [mem_map, SimpleGraph.mem_neighborFinset, Function.Embedding.coe_subtype, mem_filter,
    mem_univ, true_and]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, hv⟩
  · rintro ⟨hu, hadj⟩
    exact ⟨⟨u, hu⟩, hadj, rfl⟩

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
lemma IsSq.lift_induce {W : Set V} {m : ℕ} {g : ℕ → W} (hg : IsSq (G.induce W) m g) :
    IsSq G m (fun i => (g i).1) :=
  ⟨fun i hi => hg.adj1 i hi, fun i hi => hg.adj2 i hi,
    fun i j hi hj h => hg.inj i j hi hj (Subtype.ext h)⟩

end MainSupport

/- ### The main induction step -/

section MainStep

variable [Fintype V]

theorem main_step (hδ : ∀ v, 2 * Fintype.card V ≤ 3 * G.degree v) (v0 : V)
    (ih : ∀ (W : Set V) [DecidablePred (· ∈ W)] [DecidableRel (G.induce W).Adj],
      Fintype.card W < Fintype.card V → 1 ≤ Fintype.card W →
      (∀ w : W, 2 * Fintype.card W ≤ 3 * (G.induce W).degree w) →
      ∃ g : ℕ → W, IsSq (G.induce W) (Fintype.card W) g) :
    ∃ f, IsSq G (Fintype.card V) f := by
  classical
  set n := Fintype.card V with hn
  obtain ⟨s, f, hS⟩ := exists_opt (G := G) v0
  have hsn : s ≤ n := hS.1.le_card
  by_cases hs : s = n
  · exact ⟨f, hs ▸ hS.1⟩
  set h := n - s with hhdef
  have hh : 1 ≤ h := by omega
  have hs1 : 1 ≤ s := (hS.2 1 _ (isSq_one v0)).1
  have hSinj := hS.1.inj
  set Sset := (range s).image f with hSset
  have hSc : Sset.card = s := card_image_range hSinj
  have hHc : (univ \ Sset).card = h := by rw [card_univ_sdiff, hSc]
  have memS : ∀ v, v ∈ Sset ↔ ∃ i < s, f i = v := by
    intro v; simp only [hSset, mem_image, mem_range]
  have notS_iff : ∀ v, v ∉ Sset ↔ ∀ i < s, f i ≠ v := by
    intro v; rw [memS]; push Not; rfl
  -- degrees split between `S` and `H`
  have hsplit : ∀ v, G.degree v = dseg G v f 0 s + ((univ \ Sset).filter (G.Adj v)).card :=
    fun v => deg_eq_dseg_add (G := G) hSinj v
  have hHself : ∀ v, v ∉ Sset → ((univ \ Sset).filter (G.Adj v)).card + 1 ≤ h := by
    intro v hv
    have := card_filter_adj_self_le (G := G) (A := univ \ Sset) (v := v) (by simp [hv])
    rwa [hHc] at this
  -- (3.1)
  have h31 : ∀ v, v ∉ Sset → 2 * h + 1 ≤ 3 * ((univ \ Sset).filter (G.Adj v)).card := by
    intro v hv
    have := lemma4 hS ((notS_iff v).1 hv)
    have := hsplit v
    have := hδ v
    omega
  -- the graph `H = G - S`
  set W : Set V := {v | v ∉ Sset} with hW
  have hWc : Fintype.card W = h := by
    rw [← hHc, Fintype.card_subtype]; congr 1; ext v; simp [hW]
  have hdegW : ∀ w : W, (G.induce W).degree w = ((univ \ Sset).filter (G.Adj w.1)).card := by
    intro w
    rw [degree_induce]
    congr 1
    ext u
    simp [hW]
  -- the induction hypothesis: `h ≤ s`
  obtain ⟨g, hg⟩ := ih W (by omega) (by omega) (fun w => by
    rw [hdegW, hWc]; have := h31 w.1 w.2; omega)
  rw [hWc] at hg
  have hhs : h ≤ s := (hS.2 h _ hg.lift_induce).1
  -- Lemma 10
  have hL10 : ∀ x y, x ∉ Sset → y ∉ Sset → G.Adj x y → dseg G x f 0 s + dseg G y f 0 s ≤ s + 1 :=
    fun x y hx hy hxy => lemma10 hS (fun v hv => hδ v) ((notS_iff x).1 hx) ((notS_iff y).1 hy) hxy
  -- (3.2) and Lemma 11 on `H`
  have h32 : ∀ x y, x ∉ Sset → y ∉ Sset → G.Adj x y →
      5 * (h - 1) ≤ 3 * (((univ \ Sset).filter (G.Adj x)).card +
        ((univ \ Sset).filter (G.Adj y)).card) := by
    intro x y hx hy hxy
    have := hL10 x y hx hy hxy
    have := hsplit x
    have := hsplit y
    have := hδ x
    have := hδ y
    omega
  have hHam : ∀ x y, (∀ i < s, f i ≠ x) → (∀ i < s, f i ≠ y) → G.Adj x y →
      ∃ P, IsSq G h P ∧ P 0 = x ∧ P 1 = y ∧ ∀ i < h, ∀ j < s, P i ≠ f j := by
    intro x y hx hy hxy
    have hx' := (notS_iff x).2 hx
    have hy' := (notS_iff y).2 hy
    obtain ⟨Q, hQ, hQ0, hQ1⟩ := lemma11 (G := G.induce W)
      (fun w => by rw [hdegW, hWc]; have := h31 w.1 w.2; omega)
      (fun a b hab => by rw [hdegW, hdegW, hWc]; exact h32 a.1 b.1 a.2 b.2 hab)
      (a := ⟨x, hx'⟩) (b := ⟨y, hy'⟩) hxy
    rw [hWc] at hQ
    refine ⟨fun i => (Q i).1, hQ.lift_induce, by simp [hQ0], by simp [hQ1], fun i hi j hj he => ?_⟩
    have he' : (Q i).1 = f j := he
    have := (Q i).2
    simp only [hW, Set.mem_ofPred_eq] at this
    exact this (by rw [he']; exact mem_image_of_mem f (mem_range.2 hj))
  -- a neighbour outside `S` for every vertex outside `S`
  have hnbrH : ∀ v, v ∉ Sset → ∃ y, y ∉ Sset ∧ G.Adj v y := by
    intro v hv
    have := h31 v hv
    obtain ⟨y, hy⟩ : ((univ \ Sset).filter (G.Adj v)).Nonempty := by
      rw [← card_pos]; omega
    simp only [mem_filter, mem_sdiff, mem_univ, true_and] at hy
    exact ⟨y, hy.1, hy.2⟩
  obtain ⟨v1, hv1⟩ : ∃ v, v ∉ Sset := by
    by_contra hc
    push Not at hc
    have : univ \ Sset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]; intro v hv; simp [hc v] at hv
    rw [this, card_empty] at hHc
    omega
  -- (3.4)
  have h34 : 3 * s + 3 ≤ 2 * (s + h) := by
    obtain ⟨y, hy, hvy⟩ := hnbrH v1 hv1
    have := hL10 v1 y hv1 hy hvy
    have := hsplit v1
    have := hsplit y
    have := hδ v1
    have := hδ y
    have := hHself v1 hv1
    have := hHself y hy
    omega
  -- (3.5)
  have h35 : ∀ x, (∀ i < s, f i ≠ x) → ∀ i < s, G.Adj x (f i) →
      ∃ y, (∀ i < s, f i ≠ y) ∧ G.Adj x y ∧ G.Adj y (f i) := by
    intro x hx i hi hxi
    have hx' := (notS_iff x).2 hx
    by_contra hcon
    push Not at hcon
    have hsub : G.neighborFinset x ∩ G.neighborFinset (f i) ⊆ (Sset.filter (G.Adj x)).erase (f i) := by
      intro z hz
      simp only [mem_inter, SimpleGraph.mem_neighborFinset] at hz
      refine mem_erase.2 ⟨fun he => G.irrefl (he ▸ hz.2), mem_filter.2 ⟨?_, hz.1⟩⟩
      by_contra hzS
      exact hcon z ((notS_iff z).1 hzS) hz.1 hz.2.symm
    have hcs := card_le_card hsub
    rw [card_erase_of_mem (mem_filter.2 ⟨mem_image_of_mem f (mem_range.2 hi), hxi⟩),
      ← dseg_eq_card_image hSinj] at hcs
    have hun := card_union_add_card_inter (G.neighborFinset x) (G.neighborFinset (f i))
    have hu : (G.neighborFinset x ∪ G.neighborFinset (f i)).card ≤ n := card_le_univ _
    rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hun
    obtain ⟨y, hy, hxy⟩ := hnbrH x hx'
    have := hL10 x y hx' hy hxy
    have := hsplit y
    have := hHself y hy
    have := hδ x
    have := hδ (f i)
    have := hδ y
    omega
  -- (3.6)
  have h36 : ∀ x, (∀ i < s, f i ≠ x) → ∀ i, i + 1 < s → ¬ (G.Adj x (f i) ∧ G.Adj x (f (i + 1))) := by
    intro x hx i hi ⟨a1, a2⟩
    by_cases hi2 : 2 * i < s
    · obtain ⟨y, hy, hxy, hyf⟩ := h35 x hx i (by omega) a1
      obtain ⟨P, hP, hP0, hP1, hPS⟩ := hHam x y hx hy hxy
      have c := isSq_cat (hS.1.revSuffix i) hP (fun j hj k hk he => hPS k hk _ (by omega) he.symm)
        (fun _ _ => by rw [hP0, show s - 1 - (s - i - 1) = i by omega]; exact a1.symm)
        (fun _ _ => by rw [hP0, show s - 1 - (s - i - 2) = i + 1 by omega]; exact a2.symm)
        (fun _ _ => by rw [hP1, show s - 1 - (s - i - 1) = i by omega]; exact hyf.symm)
      have := (hS.2 _ _ c).1
      omega
    · obtain ⟨y, hy, hxy, hyf⟩ := h35 x hx (i + 1) (by omega) a2
      obtain ⟨P, hP, hP0, hP1, hPS⟩ := hHam x y hx hy hxy
      have c := isSq_cat (hS.1.take (m := i + 2) (by omega)) hP
        (fun j hj k hk he => hPS k hk j (by omega) he.symm)
        (fun _ _ => by rw [hP0, show i + 2 - 1 = i + 1 by omega]; exact a2.symm)
        (fun _ _ => by rw [hP0, show i + 2 - 2 = i by omega]; exact a1.symm)
        (fun _ _ => by rw [hP1, show i + 2 - 1 = i + 1 by omega]; exact hyf.symm)
      have := (hS.2 _ _ c).1
      omega
  -- (3.7)
  have h37 : h + 1 ≤ s := by
    have hv1' := (notS_iff v1).1 hv1
    obtain ⟨i, hi, hxi⟩ : ∃ i < s, G.Adj v1 (f i) := by
      by_contra hc
      push Not at hc
      have : dseg G v1 f 0 s = 0 := by
        unfold dseg
        rw [card_eq_zero, filter_eq_empty_iff]
        intro i hi; simp only [mem_Ico] at hi; exact hc i (by omega)
      have := hsplit v1
      have := hδ v1
      have := hHself v1 hv1
      omega
    obtain ⟨y, hy, hxy, hyf⟩ := h35 v1 hv1' i hi hxi
    obtain ⟨P, hP, hP0, hP1, hPS⟩ := hHam v1 y hv1' hy hxy
    have c := isSq_cat (isSq_one (f i)) hP (fun j hj k hk he => hPS k hk i hi he.symm)
      (fun _ _ => by rw [hP0]; exact hxi.symm) (fun h2 _ => by omega)
      (fun _ _ => by rw [hP1]; exact hyf.symm)
    have := (hS.2 _ _ c).1
    omega
  -- the maximal configuration of good triples
  let Cfg : ℕ → ℕ → Prop := fun t t' => 3 * t + 3 * t' ≤ s ∧ (∀ i < t, Good G s f (3 * i)) ∧
    (∀ i < t', Good G s f (s - 3 - 3 * i))
  have hCfg0 : Cfg 0 0 := ⟨by omega, fun i hi => by omega, fun i hi => by omega⟩
  set K := Nat.findGreatest (fun k => ∃ t t', t + t' = k ∧ Cfg t t') s with hK
  obtain ⟨t, t', htK, hCfg⟩ : ∃ t t', t + t' = K ∧ Cfg t t' :=
    Nat.findGreatest_spec (P := fun k => ∃ t t', t + t' = k ∧ Cfg t t') (Nat.zero_le s) ⟨0, 0, rfl, hCfg0⟩
  have hKmax : ∀ t1 t1', Cfg t1 t1' → t1 + t1' ≤ K := fun t1 t1' hc =>
    Nat.le_findGreatest (P := fun k => ∃ t t', t + t' = k ∧ Cfg t t') (by have := hc.1; omega)
      ⟨t1, t1', rfl, hc⟩
  have hsn' : n = s + h := by omega
  obtain ⟨hsum, hg1, hg2⟩ := hCfg
  by_cases htt : t ≤ t'
  · exfalso
    exact endgame hS (by omega) hh (fun v => by rw [← hsn']; exact hδ v) hHam h35 h36 h34 h37 htt
      hsum hg1 hg2 (fun h3 hgood => by
        have := hKmax (t + 1) t' ⟨by omega, fun i hi => by
          rcases Nat.lt_or_ge i t with h' | h'
          · exact hg1 i h'
          · rw [show i = t by omega]; exact hgood, hg2⟩
        omega)
  · exfalso
    -- apply the end game to the reversed path
    have hnot : ∀ x, (∀ i < s, rev s f i ≠ x) ↔ (∀ i < s, f i ≠ x) := by
      intro x
      constructor
      · intro hx i hi he
        exact hx (s - 1 - i) (by omega) (by simp only [rev]; rw [show s - 1 - (s - 1 - i) = i by omega]; exact he)
      · intro hx i hi he
        exact hx (s - 1 - i) (by omega) he
    refine endgame (f := rev s f) (t := t') (t' := t) hS.rev (by omega) hh
      (fun v => by rw [← hsn']; exact hδ v) ?_ ?_ ?_ h34 h37 (by omega) (by omega) ?_ ?_ ?_
    · intro x y hx hy hxy
      obtain ⟨P, hP, hP0, hP1, hPS⟩ := hHam x y ((hnot x).1 hx) ((hnot y).1 hy) hxy
      exact ⟨P, hP, hP0, hP1, fun i hi j hj => hPS i hi (s - 1 - j) (by omega)⟩
    · intro x hx i hi hxi
      obtain ⟨y, hy, hxy, hyf⟩ := h35 x ((hnot x).1 hx) (s - 1 - i) (by omega) hxi
      exact ⟨y, (hnot y).2 hy, hxy, hyf⟩
    · intro x hx i hi ⟨a1, a2⟩
      have := h36 x ((hnot x).1 hx) (s - 1 - (i + 1)) (by omega)
      simp only [rev] at a1 a2
      rw [show s - 1 - (i + 1) + 1 = s - 1 - i by omega] at this
      exact this ⟨a2, a1⟩
    · intro i hi
      rw [good_rev (by omega)]
      exact hg2 i hi
    · intro i hi
      rw [good_rev (by omega), show s - 3 - (s - 3 - 3 * i) = 3 * i by omega]
      exact hg1 i hi
    · intro h3 hgood
      rw [good_rev (by omega)] at hgood
      have := hKmax t (t' + 1) ⟨by omega, hg1, fun i hi => by
        rcases Nat.lt_or_ge i t' with h' | h'
        · exact hg2 i h'
        · rw [show i = t' by omega]; exact hgood⟩
      omega

end MainStep

/- ### The theorem -/

section Final

/-- Fan–Kierstead, non-extremal case, for square paths given by index functions. -/
theorem fk_nat : ∀ n, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], Fintype.card V = n → 1 ≤ n → (∀ v, 2 * n ≤ 3 * G.degree v) →
    ∃ f, IsSq G n f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ G _ hn h1 hδ
  obtain ⟨v0⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  subst hn
  exact main_step (G := G) hδ v0 (fun W _ _ hlt hW1 hδW =>
    ih (Fintype.card W) hlt W (G.induce W) rfl hW1 hδW)

/-- **Fan–Kierstead** (non-extremal case): a graph on `n` vertices with minimum degree at least
`2n/3` has a hamiltonian square path. -/
theorem fk_H1 {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hδ : ∀ v, 2 * Fintype.card V ≤ 3 * G.degree v) :
    ∃ f : Fin (Fintype.card V) ≃ V, ∀ i j : Fin (Fintype.card V),
      i.val < j.val → j.val ≤ i.val + 2 → G.Adj (f i) (f j) := by
  classical
  by_cases h0 : Fintype.card V = 0
  · refine ⟨(Fintype.equivFin V).symm, fun i j _ _ => ?_⟩
    exact absurd i.2 (by omega)
  obtain ⟨f, hf⟩ := fk_nat (Fintype.card V) V G rfl (by omega) hδ
  let e : Fin (Fintype.card V) → V := fun i => f i
  have he : Function.Injective e := fun i j h => Fin.ext (hf.inj i j i.2 j.2 h)
  have hb : Function.Bijective e := (Fintype.bijective_iff_injective_and_card e).2 ⟨he, by simp⟩
  refine ⟨Equiv.ofBijective e hb, fun i j hij hj2 => ?_⟩
  exact hf.adj_close i.2 j.2 hij hj2

end Final

/- ## The extremal case -/

/- ### Lemma 8, equality case -/

lemma lemma8_count_eq (c : ℕ → ℕ) (hc : ∀ i, c i ≤ 2) (s : ℕ)
    (h1 : ∀ i, i < s / 2 → c i = 2 → c (i + 1) = 0)
    (h2 : ∀ i, s / 2 < i → i < s → c i = 2 → c (i - 1) = 0)
    (heq : ∑ i ∈ range s, c i = s + 1) : c (s / 2) ≠ 1 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp at heq
  set M := s / 2 with hM
  have L1 := one_sided c hc M (fun i hi h => h1 i hi h)
  let c' : ℕ → ℕ := fun j => c (s - 1 - j)
  have L2 := one_sided c' (fun i => hc _) (s - 1 - M) (fun j hj h => by
    have := h2 (s - 1 - j) (by omega) (by omega) h
    simp only [c']
    rwa [show s - 1 - (j + 1) = s - 1 - j - 1 by omega])
  have hsplit : ∑ i ∈ range s, c i + c M = ∑ i ∈ range (M + 1), c i + ∑ j ∈ range (s - 1 - M + 1), c' j := by
    have e1 : ∑ i ∈ range s, c i = ∑ i ∈ range (M + 1), c i + ∑ i ∈ Ico (M + 1) s, c i := by
      rw [sum_range_add_sum_Ico _ (by omega)]
    have e2 : ∑ j ∈ range (s - 1 - M + 1), c' j = ∑ i ∈ Ico M s, c i := by
      rw [sum_bij (fun j _ => s - 1 - j)]
      · intro j hj; simp only [mem_range] at hj; simp only [mem_Ico]; omega
      · intro j hj j' hj' h; simp only [mem_range] at hj hj'; omega
      · intro i hi; simp only [mem_Ico] at hi
        exact ⟨s - 1 - i, by simp only [mem_range]; omega, by omega⟩
      · intro j hj; rfl
    have e3 : ∑ i ∈ Ico M s, c i = c M + ∑ i ∈ Ico (M + 1) s, c i := by
      rw [sum_eq_sum_Ico_succ_bot (by omega)]
    rw [e1, e2, e3]; ring
  have hcM : c' (s - 1 - M) = c M := by simp only [c']; congr 1; omega
  rw [hcM] at L2
  intro h1'
  rw [if_neg (by omega)] at L1 L2
  omega

/- ### Triangles as cube paths; longer paths contradict optimality -/

/-- The triangle `x, y, z` as a sequence. -/
def tri (x y z : V) : ℕ → V := fun i => if i = 0 then x else if i = 1 then y else z

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma isCube_tri {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    IsCube G 3 (tri x y z) := by
  constructor
  · intro i j hij hj3 hj
    have : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simpa [tri]
  · intro i j hi hj h
    by_contra hne
    have : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 0) ∨
      (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [tri] at h
    · exact hxy.ne h
    · exact hxz.ne h
    · exact hyz.ne h
    · exact hxy.ne h.symm
    · exact hxz.ne h.symm
    · exact hyz.ne h.symm

omit [DecidableEq V] in
lemma OptFix.no_longer' {n m : ℕ} {f g : ℕ → V} (hS : OptFix G n f) (hg : IsSq G m g)
    (hm : n < m) (e0 : g 0 = f 0) (e1 : g 1 = f 1) (e2 : g (m - 2) = f (n - 2))
    (e3 : g (m - 1) = f (n - 1)) : False := by
  have := (hS.2 m g hg ⟨e0, e1, e2, e3⟩).1
  omega

section Lemma5

variable [Fintype V] {n : ℕ} {f : ℕ → V}

omit [Fintype V] in
omit [DecidableEq V] in
/-- Replacing `f (a+2), f (a+3)` by the triangle `u1 u2 u3` gives a longer path. -/
lemma lemma5_P0 (hS : OptFix G n f) {u1 u2 u3 : V} (h12 : G.Adj u1 u2) (h13 : G.Adj u1 u3)
    (h23 : G.Adj u2 u3) (hu : ∀ i < 3, ∀ j < n, tri u1 u2 u3 i ≠ f j) {a : ℕ} (han : a + 6 ≤ n)
    (k1 : G.Adj u1 (f a)) (k2 : G.Adj u1 (f (a + 1))) (k3 : G.Adj u2 (f (a + 1)))
    (k4 : G.Adj u2 (f (a + 4))) (k5 : G.Adj u3 (f (a + 4))) (k6 : G.Adj u3 (f (a + 5))) : False := by
  set g := two (fun i => a + 2 ≤ i ∧ i ≤ a + 4) (tri u1 u2 u3) f (fun i => i - (a + 2))
    (fun i => if i ≤ a + 1 then i else i - 1) with hgdef
  have v : ∀ i, g i = if a + 2 ≤ i ∧ i ≤ a + 4 then tri u1 u2 u3 (i - (a + 2))
      else f (if i ≤ a + 1 then i else i - 1) := fun i => rfl
  have Pc : ∀ i, a + 2 ≤ i → i ≤ a + 4 → g i = tri u1 u2 u3 (i - (a + 2)) := fun i h1 h2 => by
    rw [v, if_pos ⟨h1, h2⟩]
  have Pl : ∀ i, i ≤ a + 1 → g i = f i := fun i h1 => by
    rw [v, if_neg (by omega), if_pos h1]
  have Pr : ∀ i, a + 5 ≤ i → g i = f (i - 1) := fun i h1 => by
    rw [v, if_neg (show ¬ (a + 2 ≤ i ∧ i ≤ a + 4) by omega), if_neg (show ¬ (i ≤ a + 1) by omega)]
  have g0 : g a = f a := Pl a (by omega)
  have g1 : g (a + 1) = f (a + 1) := Pl _ (by omega)
  have g2 : g (a + 2) = u1 := by rw [Pc _ (by omega) (by omega), show a + 2 - (a + 2) = 0 by omega]; rfl
  have g3 : g (a + 3) = u2 := by rw [Pc _ (by omega) (by omega), show a + 3 - (a + 2) = 1 by omega]; rfl
  have g4 : g (a + 4) = u3 := by rw [Pc _ (by omega) (by omega), show a + 4 - (a + 2) = 2 by omega]; rfl
  have g5 : g (a + 5) = f (a + 4) := by rw [Pr _ (by omega)]; all_goals (congr 1)
  have g6 : g (a + 6) = f (a + 5) := by rw [Pr _ (by omega)]; all_goals (congr 1)
  have hg := isSq_two (m := n + 1) (isCube_tri h12 h13 h23) hS.1 hu
    (fun i => a + 2 ≤ i ∧ i ≤ a + 4) (fun i => i - (a + 2)) (fun i => if i ≤ a + 1 then i else i - 1)
    (fun i hi hP => by omega) (fun i hi hP => by split_ifs <;> omega)
    (fun i j hi hj hPi hPj h => by omega) (fun i j hi hj hPi hPj h => by split_ifs at h <;> omega)
    (fun i j hij hj2 hj hPi hPj => by omega) (fun i j hij hj2 hj hPi hPj => by split_ifs <;> omega)
    (fun i j hij hj2 hj hcase => by
      rw [← hgdef]
      have : (i = a ∧ j = a + 2) ∨ (i = a + 1 ∧ j = a + 2) ∨ (i = a + 1 ∧ j = a + 3) ∨
          (i = a + 3 ∧ j = a + 5) ∨ (i = a + 4 ∧ j = a + 5) ∨ (i = a + 4 ∧ j = a + 6) := by omega
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rw [h1, h2]
      · rw [g0, g2]; exact k1.symm
      · rw [g1, g2]; exact k2.symm
      · rw [g1, g3]; exact k3.symm
      · rw [g3, g5]; exact k4
      · rw [g4, g5]; exact k5
      · rw [g4, g6]; exact k6)
  rw [← hgdef] at hg
  exact hS.no_longer' hg (by omega) (Pl 0 (by omega)) (Pl 1 (by omega))
    (by rw [Pr _ (by omega)]; all_goals (congr 1))
    (by rw [Pr _ (by omega)]; all_goals (congr 1))

omit [Fintype V] in
omit [DecidableEq V] in
/-- Replacing `f (a+5)` by the triangle `u1 u2 u3` gives a path two longer. -/
lemma lemma5_P2 (hS : OptFix G n f) {u1 u2 u3 : V} (h12 : G.Adj u1 u2) (h13 : G.Adj u1 u3)
    (h23 : G.Adj u2 u3) (hu : ∀ i < 3, ∀ j < n, tri u1 u2 u3 i ≠ f j) {a : ℕ} (han : a + 8 ≤ n)
    (k1 : G.Adj u1 (f (a + 3))) (k2 : G.Adj u1 (f (a + 4))) (k3 : G.Adj u2 (f (a + 4)))
    (k4 : G.Adj u2 (f (a + 6))) (k5 : G.Adj u3 (f (a + 6))) (k6 : G.Adj u3 (f (a + 7))) : False := by
  set g := two (fun i => a + 5 ≤ i ∧ i ≤ a + 7) (tri u1 u2 u3) f (fun i => i - (a + 5))
    (fun i => if i ≤ a + 4 then i else i - 2) with hgdef
  have v : ∀ i, g i = if a + 5 ≤ i ∧ i ≤ a + 7 then tri u1 u2 u3 (i - (a + 5))
      else f (if i ≤ a + 4 then i else i - 2) := fun i => rfl
  have Pc : ∀ i, a + 5 ≤ i → i ≤ a + 7 → g i = tri u1 u2 u3 (i - (a + 5)) := fun i h1 h2 => by
    rw [v, if_pos ⟨h1, h2⟩]
  have Pl : ∀ i, i ≤ a + 4 → g i = f i := fun i h1 => by
    rw [v, if_neg (by omega), if_pos h1]
  have Pr : ∀ i, a + 8 ≤ i → g i = f (i - 2) := fun i h1 => by
    rw [v, if_neg (show ¬ (a + 5 ≤ i ∧ i ≤ a + 7) by omega), if_neg (show ¬ (i ≤ a + 4) by omega)]
  have g3 : g (a + 3) = f (a + 3) := Pl _ (by omega)
  have g4 : g (a + 4) = f (a + 4) := Pl _ (by omega)
  have g5 : g (a + 5) = u1 := by rw [Pc _ (by omega) (by omega), show a + 5 - (a + 5) = 0 by omega]; rfl
  have g6 : g (a + 6) = u2 := by rw [Pc _ (by omega) (by omega), show a + 6 - (a + 5) = 1 by omega]; rfl
  have g7 : g (a + 7) = u3 := by rw [Pc _ (by omega) (by omega), show a + 7 - (a + 5) = 2 by omega]; rfl
  have g8 : g (a + 8) = f (a + 6) := by rw [Pr _ (by omega)]; all_goals (congr 1)
  have g9 : g (a + 9) = f (a + 7) := by rw [Pr _ (by omega)]; all_goals (congr 1)
  have hg := isSq_two (m := n + 2) (isCube_tri h12 h13 h23) hS.1 hu
    (fun i => a + 5 ≤ i ∧ i ≤ a + 7) (fun i => i - (a + 5)) (fun i => if i ≤ a + 4 then i else i - 2)
    (fun i hi hP => by omega) (fun i hi hP => by split_ifs <;> omega)
    (fun i j hi hj hPi hPj h => by omega) (fun i j hi hj hPi hPj h => by split_ifs at h <;> omega)
    (fun i j hij hj2 hj hPi hPj => by omega) (fun i j hij hj2 hj hPi hPj => by split_ifs <;> omega)
    (fun i j hij hj2 hj hcase => by
      rw [← hgdef]
      have : (i = a + 3 ∧ j = a + 5) ∨ (i = a + 4 ∧ j = a + 5) ∨ (i = a + 4 ∧ j = a + 6) ∨
          (i = a + 6 ∧ j = a + 8) ∨ (i = a + 7 ∧ j = a + 8) ∨ (i = a + 7 ∧ j = a + 9) := by omega
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rw [h1, h2]
      · rw [g3, g5]; exact k1.symm
      · rw [g4, g5]; exact k2.symm
      · rw [g4, g6]; exact k3.symm
      · rw [g6, g8]; exact k4
      · rw [g7, g8]; exact k5
      · rw [g7, g9]; exact k6)
  rw [← hgdef] at hg
  exact hS.no_longer' hg (by omega) (Pl 0 (by omega)) (Pl 1 (by omega))
    (by rw [Pr _ (by omega)]; all_goals (congr 1))
    (by rw [Pr _ (by omega)]; all_goals (congr 1))

omit [Fintype V] in
omit [DecidableEq V] in
/-- The path `… f (a+1), f (a+2), u1, f (a+4), u2, u3, f (a+6), …` is longer. -/
lemma lemma5_P3 (hS : OptFix G n f) {u1 u2 u3 : V} (h12 : G.Adj u1 u2) (h13 : G.Adj u1 u3)
    (h23 : G.Adj u2 u3) (hu : ∀ i < 3, ∀ j < n, tri u1 u2 u3 i ≠ f j) {a : ℕ} (han : a + 8 ≤ n)
    (k1 : G.Adj u1 (f (a + 1))) (k2 : G.Adj u1 (f (a + 2))) (k3 : G.Adj u1 (f (a + 4)))
    (k4 : G.Adj u2 (f (a + 4))) (k5 : G.Adj u3 (f (a + 4))) (k6 : G.Adj u2 (f (a + 6)))
    (k7 : G.Adj u3 (f (a + 6))) (k8 : G.Adj u3 (f (a + 7))) : False := by
  set g := two (fun i => i = a + 3 ∨ i = a + 5 ∨ i = a + 6) (tri u1 u2 u3) f
    (fun i => if i = a + 3 then 0 else if i = a + 5 then 1 else 2)
    (fun i => if i ≤ a + 4 then i else i - 1) with hgdef
  have v : ∀ i, g i = if (i = a + 3 ∨ i = a + 5 ∨ i = a + 6) then
      tri u1 u2 u3 (if i = a + 3 then 0 else if i = a + 5 then 1 else 2)
      else f (if i ≤ a + 4 then i else i - 1) := fun i => rfl
  have Pl : ∀ i, i ≤ a + 2 → g i = f i := fun i h1 => by
    rw [v, if_neg (show ¬ (i = a + 3 ∨ i = a + 5 ∨ i = a + 6) by omega), if_pos (show i ≤ a + 4 by omega)]
  have Pr : ∀ i, a + 7 ≤ i → g i = f (i - 1) := fun i h1 => by
    rw [v, if_neg (show ¬ (i = a + 3 ∨ i = a + 5 ∨ i = a + 6) by omega),
      if_neg (show ¬ (i ≤ a + 4) by omega)]
  have g1 : g (a + 1) = f (a + 1) := Pl _ (by omega)
  have g2 : g (a + 2) = f (a + 2) := Pl _ (by omega)
  have g3 : g (a + 3) = u1 := by
    rw [v, if_pos (Or.inl rfl), if_pos rfl]; rfl
  have g4 : g (a + 4) = f (a + 4) := by
    rw [v, if_neg (show ¬ (a + 4 = a + 3 ∨ a + 4 = a + 5 ∨ a + 4 = a + 6) by omega),
      if_pos (show a + 4 ≤ a + 4 by omega)]
  have g5 : g (a + 5) = u2 := by
    rw [v, if_pos (Or.inr (Or.inl rfl)), if_neg (show ¬ (a + 5 = a + 3) by omega), if_pos rfl]; rfl
  have g6 : g (a + 6) = u3 := by
    rw [v, if_pos (Or.inr (Or.inr rfl)), if_neg (show ¬ (a + 6 = a + 3) by omega),
      if_neg (show ¬ (a + 6 = a + 5) by omega)]; rfl
  have g7 : g (a + 7) = f (a + 6) := by rw [Pr _ (by omega)]; all_goals (congr 1)
  have g8 : g (a + 8) = f (a + 7) := by rw [Pr _ (by omega)]; all_goals (congr 1)
  have hg := isSq_two (m := n + 1) (isCube_tri h12 h13 h23) hS.1 hu
    (fun i => i = a + 3 ∨ i = a + 5 ∨ i = a + 6)
    (fun i => if i = a + 3 then 0 else if i = a + 5 then 1 else 2)
    (fun i => if i ≤ a + 4 then i else i - 1)
    (fun i hi hP => by split_ifs <;> omega) (fun i hi hP => by split_ifs <;> omega)
    (fun i j hi hj hPi hPj h => by split_ifs at h <;> omega)
    (fun i j hi hj hPi hPj h => by split_ifs at h <;> omega)
    (fun i j hij hj2 hj hPi hPj => by split_ifs <;> omega)
    (fun i j hij hj2 hj hPi hPj => by split_ifs <;> omega)
    (fun i j hij hj2 hj hcase => by
      rw [← hgdef]
      have : (i = a + 1 ∧ j = a + 3) ∨ (i = a + 2 ∧ j = a + 3) ∨ (i = a + 3 ∧ j = a + 4) ∨
          (i = a + 4 ∧ j = a + 5) ∨ (i = a + 4 ∧ j = a + 6) ∨ (i = a + 5 ∧ j = a + 7) ∨
          (i = a + 6 ∧ j = a + 7) ∨ (i = a + 6 ∧ j = a + 8) := by omega
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · rw [g1, g3]; exact k1.symm
      · rw [g2, g3]; exact k2.symm
      · rw [g3, g4]; exact k3
      · rw [g4, g5]; exact k4.symm
      · rw [g4, g6]; exact k5.symm
      · rw [g5, g7]; exact k6
      · rw [g6, g7]; exact k7
      · rw [g6, g8]; exact k8)
  rw [← hgdef] at hg
  exact hS.no_longer' hg (by omega) (Pl 0 (by omega)) (Pl 1 (by omega))
    (by rw [Pr _ (by omega)]; all_goals (congr 1))
    (by rw [Pr _ (by omega)]; all_goals (congr 1))

omit [DecidableEq V] [Fintype V] in
lemma tri_notS {n : ℕ} {f : ℕ → V} {u1 u2 u3 : V} (h1 : ∀ j < n, f j ≠ u1) (h2 : ∀ j < n, f j ≠ u2)
    (h3 : ∀ j < n, f j ≠ u3) : ∀ i < 3, ∀ j < n, tri u1 u2 u3 i ≠ f j := by
  intro i hi j hj he
  simp only [tri] at he
  split_ifs at he
  · exact h1 j hj he.symm
  · exact h2 j hj he.symm
  · exact h3 j hj he.symm

omit [Fintype V] in
omit [DecidableEq V] in
/-- The adjacencies forced on a vertex attaining equality in Lemma 1 on a segment of length `3k`. -/
lemma lemma5_vertex {n : ℕ} {f : ℕ → V} (hS : OptFix G n f) {x : V} (hx : ∀ j < n, f j ≠ x)
    {a k : ℕ} (hk : 2 ≤ k) (haq : a + 3 * k ≤ n) (hd : 3 * dseg G x f a (3 * k) = 2 * (3 * k) + 3) :
    (∀ j, 2 ≤ j → j ≤ k → G.Adj x (f (a + 3 * j - 2))) ∧
    (∀ j, 1 ≤ j → j + 1 ≤ k → G.Adj x (f (a + 3 * j - 1)) ∨ G.Adj x (f (a + 3 * j))) ∧
    G.Adj x (f a) ∧ G.Adj x (f (a + 1)) ∧ G.Adj x (f (a + 3 * k - 2)) ∧ G.Adj x (f (a + 3 * k - 1)) := by
  have hx' : ∀ i < n, f i ≠ x := hx
  refine ⟨fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_, ?_⟩
  · have e1 := dseg_add (G := G) x f a (3 * j - 2) (1 + (3 * k - 3 * j + 1))
    have e2 := dseg_add (G := G) x f (a + (3 * j - 2)) 1 (3 * k - 3 * j + 1)
    rw [show 3 * j - 2 + (1 + (3 * k - 3 * j + 1)) = 3 * k by omega] at e1
    rw [dseg_one, show a + (3 * j - 2) + 1 = a + 3 * j - 1 by omega,
      show a + (3 * j - 2) = a + 3 * j - 2 by omega] at e2
    rw [show a + (3 * j - 2) = a + 3 * j - 2 by omega] at e1
    have b1 := lemma1 hS hx' (a := a) (q := 3 * j - 2) (by omega)
    have b2 := lemma1 hS hx' (a := a + 3 * j - 1) (q := 3 * k - 3 * j + 1) (by omega)
    by_contra hna
    rw [if_neg hna] at e2
    omega
  · have e1 := dseg_add (G := G) x f a (3 * j - 1) (2 + (3 * k - 3 * j - 1))
    have e2 := dseg_add (G := G) x f (a + (3 * j - 1)) 2 (3 * k - 3 * j - 1)
    have e3 := dseg_add (G := G) x f (a + (3 * j - 1)) 1 1
    rw [show 3 * j - 1 + (2 + (3 * k - 3 * j - 1)) = 3 * k by omega] at e1
    rw [show a + (3 * j - 1) + 2 = a + 3 * j + 1 by omega] at e2
    rw [dseg_one, dseg_one, show a + (3 * j - 1) + 1 = a + 3 * j by omega,
      show (1 : ℕ) + 1 = 2 from rfl] at e3
    rw [show a + (3 * j - 1) = a + 3 * j - 1 by omega] at e1 e2 e3
    have b1 := lemma1 hS hx' (a := a) (q := 3 * j - 1) (by omega)
    have b2 := lemma1 hS hx' (a := a + 3 * j + 1) (q := 3 * k - 3 * j - 1) (by omega)
    by_contra hna
    push Not at hna
    rw [if_neg hna.1, if_neg hna.2] at e3
    omega
  · obtain ⟨l0, l1, -⟩ := lemma2 hS hx' (a := a) (q := 3 * k) haq hd
    have hn2 : 2 ≤ n := by omega
    have hd' : 3 * dseg G x (rev n f) (n - (a + 3 * k)) (3 * k) = 2 * (3 * k) + 3 := by
      rw [dseg_rev (G := G) x f haq]; exact hd
    obtain ⟨r0, r1, -⟩ := lemma2 (hS.rev hn2) (fun i hi h => hx' (n - 1 - i) (by omega) h)
      (a := n - (a + 3 * k)) (q := 3 * k) (by omega) hd'
    simp only [rev] at r0 r1
    rw [show n - 1 - (n - (a + 3 * k)) = a + 3 * k - 1 by omega] at r0
    rw [show n - 1 - (n - (a + 3 * k) + 1) = a + 3 * k - 2 by omega] at r1
    exact ⟨l0, l1, r1, r0⟩

omit [Fintype V] in
omit [DecidableEq V] in
/-- **Lemma 5** (Fan–Kierstead). A triangle `T` outside an end-optimal square path `S` satisfies
`d(T, Q) ≤ 2|Q| + 2` for every segment `Q` of `S` with `|Q| ≠ 3`. -/
theorem lemma5 {n : ℕ} {f : ℕ → V} (hS : OptFix G n f) {x1 x2 x3 : V} (h12 : G.Adj x1 x2)
    (h13 : G.Adj x1 x3) (h23 : G.Adj x2 x3) (hx1 : ∀ j < n, f j ≠ x1) (hx2 : ∀ j < n, f j ≠ x2)
    (hx3 : ∀ j < n, f j ≠ x3) {a q : ℕ} (haq : a + q ≤ n) (hq3 : q ≠ 3) :
    dseg G x1 f a q + dseg G x2 f a q + dseg G x3 f a q ≤ 2 * q + 2 := by
  have b1 := lemma1 hS hx1 haq
  have b2 := lemma1 hS hx2 haq
  have b3 := lemma1 hS hx3 haq
  by_contra hcon
  have e1 : 3 * dseg G x1 f a q = 2 * q + 3 := by omega
  have e2 : 3 * dseg G x2 f a q = 2 * q + 3 := by omega
  have e3 : 3 * dseg G x3 f a q = 2 * q + 3 := by omega
  have hle := dseg_le (G := G) x1 f a q
  obtain ⟨k, rfl⟩ : ∃ k, q = 3 * k := ⟨q / 3, by omega⟩
  have hk : 2 ≤ k := by omega
  obtain ⟨A1, B1, s1, t1, u1, v1⟩ := lemma5_vertex hS hx1 hk haq e1
  obtain ⟨A2, B2, s2, t2, u2, v2⟩ := lemma5_vertex hS hx2 hk haq e2
  obtain ⟨A3, B3, s3, t3, u3, v3⟩ := lemma5_vertex hS hx3 hk haq e3
  by_cases hk2 : k = 2
  · subst hk2
    rw [show a + 3 * 2 - 2 = a + 4 by omega] at u1 u2 u3
    rw [show a + 3 * 2 - 1 = a + 5 by omega] at v1 v2 v3
    exact lemma5_P0 hS h12 h13 h23 (tri_notS hx1 hx2 hx3) (by omega) s1 t1 t2 u2 u3 v3
  -- `k ≥ 3`
  have a5 : ∀ x, x = x1 ∨ x = x2 ∨ x = x3 → G.Adj x (f (a + 4)) := by
    rintro x (rfl | rfl | rfl)
    · simpa using A1 2 le_rfl hk
    · simpa using A2 2 le_rfl hk
    · simpa using A3 2 le_rfl hk
  have a8 : ∀ x, x = x1 ∨ x = x2 ∨ x = x3 → G.Adj x (f (a + 7)) := by
    rintro x (rfl | rfl | rfl)
    · simpa using A1 3 (by omega) (by omega)
    · simpa using A2 3 (by omega) (by omega)
    · simpa using A3 3 (by omega) (by omega)
  -- no vertex of `T` is adjacent to `f (a+5)`
  have n6 : ∀ x, x = x1 ∨ x = x2 ∨ x = x3 → ¬ G.Adj x (f (a + 5)) := by
    rintro x (rfl | rfl | rfl) hadj
    · exact lemma5_P0 hS h23 h12.symm h13.symm (tri_notS hx2 hx3 hx1) (by omega) s2 t2 t3
        (a5 _ (Or.inr (Or.inr rfl))) (a5 _ (Or.inl rfl)) hadj
    · exact lemma5_P0 hS h13 h12 h23.symm (tri_notS hx1 hx3 hx2) (by omega) s1 t1 t3
        (a5 _ (Or.inr (Or.inr rfl))) (a5 _ (Or.inr (Or.inl rfl))) hadj
    · exact lemma5_P0 hS h12 h13 h23 (tri_notS hx1 hx2 hx3) (by omega) s1 t1 t2
        (a5 _ (Or.inr (Or.inl rfl))) (a5 _ (Or.inr (Or.inr rfl))) hadj
  have a7 : ∀ x, x = x1 ∨ x = x2 ∨ x = x3 → G.Adj x (f (a + 6)) := by
    rintro x hxm
    have hB : G.Adj x (f (a + 3 * 2 - 1)) ∨ G.Adj x (f (a + 3 * 2)) := by
      rcases hxm with rfl | rfl | rfl
      · exact B1 2 (by omega) (by omega)
      · exact B2 2 (by omega) (by omega)
      · exact B3 2 (by omega) (by omega)
    rw [show a + 3 * 2 - 1 = a + 5 by omega, show a + 3 * 2 = a + 6 by omega] at hB
    exact hB.resolve_left (n6 x hxm)
  -- no vertex of `T` is adjacent to `f (a+3)`
  have n4 : ∀ x, x = x1 ∨ x = x2 ∨ x = x3 → ¬ G.Adj x (f (a + 3)) := by
    rintro x (rfl | rfl | rfl) hadj
    · exact lemma5_P2 hS h12 h13 h23 (tri_notS hx1 hx2 hx3) (by omega) hadj
        (a5 _ (Or.inl rfl)) (a5 _ (Or.inr (Or.inl rfl))) (a7 _ (Or.inr (Or.inl rfl)))
        (a7 _ (Or.inr (Or.inr rfl))) (a8 _ (Or.inr (Or.inr rfl)))
    · exact lemma5_P2 hS h12.symm h23 h13 (tri_notS hx2 hx1 hx3) (by omega) hadj
        (a5 _ (Or.inr (Or.inl rfl))) (a5 _ (Or.inl rfl)) (a7 _ (Or.inl rfl))
        (a7 _ (Or.inr (Or.inr rfl))) (a8 _ (Or.inr (Or.inr rfl)))
    · exact lemma5_P2 hS h13.symm h23.symm h12 (tri_notS hx3 hx1 hx2) (by omega) hadj
        (a5 _ (Or.inr (Or.inr rfl))) (a5 _ (Or.inl rfl)) (a7 _ (Or.inl rfl))
        (a7 _ (Or.inr (Or.inl rfl))) (a8 _ (Or.inr (Or.inl rfl)))
  have a3 : ∀ x, x = x1 ∨ x = x2 ∨ x = x3 → G.Adj x (f (a + 2)) := by
    rintro x hxm
    have hB : G.Adj x (f (a + 3 * 1 - 1)) ∨ G.Adj x (f (a + 3 * 1)) := by
      rcases hxm with rfl | rfl | rfl
      · exact B1 1 le_rfl (by omega)
      · exact B2 1 le_rfl (by omega)
      · exact B3 1 le_rfl (by omega)
    rw [show a + 3 * 1 - 1 = a + 2 by omega, show a + 3 * 1 = a + 3 by omega] at hB
    exact hB.resolve_right (n4 x hxm)
  exact lemma5_P3 hS h12 h13 h23 (tri_notS hx1 hx2 hx3) (by omega) t1 (a3 _ (Or.inl rfl))
    (a5 _ (Or.inl rfl)) (a5 _ (Or.inr (Or.inl rfl))) (a5 _ (Or.inr (Or.inr rfl)))
    (a7 _ (Or.inr (Or.inl rfl))) (a7 _ (Or.inr (Or.inr rfl))) (a8 _ (Or.inr (Or.inr rfl)))

end Lemma5

section Lemma6

variable [Fintype V]

omit [DecidableEq V] [Fintype V] in
lemma pad4_notS {s : ℕ} {f : ℕ → V} {x : V} (hx : ∀ i < s, f i ≠ x) :
    ∀ i < s + 4, pad4 s f i ≠ Sum.inl x := by
  intro i hi
  unfold pad4
  split_ifs <;> simp only [ne_eq, Sum.inl.injEq, reduceCtorEq, not_false_eq_true]
  exact hx _ (by omega)

omit [Fintype V] in
/-- **Lemma 6** (Fan–Kierstead). A triangle outside an optimal square path `S` has at most
`2s - 2` edges to `S`. -/
theorem lemma6 {s : ℕ} {f : ℕ → V} (hS : Opt G s f) {x1 x2 x3 : V} (h12 : G.Adj x1 x2)
    (h13 : G.Adj x1 x3) (h23 : G.Adj x2 x3) (hx1 : ∀ j < s, f j ≠ x1) (hx2 : ∀ j < s, f j ≠ x2)
    (hx3 : ∀ j < s, f j ≠ x3) :
    dseg G x1 f 0 s + dseg G x2 f 0 s + dseg G x3 f 0 s + 2 ≤ 2 * s := by
  classical
  set T : Finset V := insert x1 (insert x2 (insert x3 ((range s).image f))) with hT
  have hfT : ∀ i < s, f i ∈ T := fun i hi => by
    rw [hT]; simp only [mem_insert, mem_image, mem_range]; exact Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩))
  have h1T : x1 ∈ T := by rw [hT]; simp
  have h2T : x2 ∈ T := by rw [hT]; simp
  have h3T : x3 ∈ T := by rw [hT]; simp
  have hopt := pad4_optFix hS x1 T hfT
  have L5 := lemma5 hopt (x1 := Sum.inl x1) (x2 := Sum.inl x2) (x3 := Sum.inl x3)
    (ext_inl_inl.2 h12) (ext_inl_inl.2 h13) (ext_inl_inl.2 h23)
    (fun j hj h => pad4_notS hx1 j hj h) (fun j hj h => pad4_notS hx2 j hj h)
    (fun j hj h => pad4_notS hx3 j hj h) (a := 0) (q := s + 4) (by omega) (by omega)
  rw [pad4_dseg T h1T, pad4_dseg T h2T, pad4_dseg T h3T] at L5
  omega

end Lemma6

end FK


/-
# Fan–Kierstead, part 2: the extremal case of Lemma 10
-/

open Finset

namespace FK

variable {V : Type} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

section L28

variable [Fintype V] {s : ℕ} {f : ℕ → V}

/-- Equality structure in (2.8) when `δ ≥ (2n-1)/3` outside `S`, for a non-extendable cube path
with `s ≥ 2p+2`. -/
lemma lemma28x (hS : Opt G s f)
    (hdeg : ∀ v, (∀ j < s, f j ≠ v) → 2 * Fintype.card V ≤ 3 * G.degree v + 1)
    {p : ℕ} {c : ℕ → V} (hc : IsCube G p c) (hp3 : 3 ≤ p)
    (hcS : ∀ i < p, ∀ j < s, c i ≠ f j) (hsp : 2 * p + 2 ≤ s)
    (hmax : ∀ z, (∀ j < s, f j ≠ z) → (∀ i < p, c i ≠ z) →
      ¬ (G.Adj (c (p - 1)) z ∧ G.Adj (c (p - 2)) z ∧ (3 ≤ p → G.Adj (c (p - 3)) z))) :
    dseg G (c (p - 3)) f 0 s + dseg G (c (p - 2)) f 0 s + dseg G (c (p - 1)) f 0 s =
      2 * s - p + 2 ∧
    (∀ t, p - 3 ≤ t → t < p → 3 * G.degree (c t) + 1 = 2 * Fintype.card V) ∧
    (∀ t, p - 3 ≤ t → t < p → ∀ i < p, i ≠ t → G.Adj (c t) (c i)) ∧
    (∀ z, (∀ j < s, f j ≠ z) → (∀ i < p, c i ≠ z) →
      bi (G.Adj (c (p - 3)) z) + bi (G.Adj (c (p - 2)) z) + bi (G.Adj (c (p - 1)) z) = 2) := by
  classical
  have h25 := lemma25 hS hdeg hc hp3 hcS hsp
  set n := Fintype.card V with hn
  set Sf := (range s).image f with hSf
  set Pc := (range p).image c with hPc
  have hSinj := hS.1.inj
  have hSc : Sf.card = s := card_image_range hSinj
  have hPcc : Pc.card = p := card_image_range hc.inj
  have hdisj : Disjoint Sf Pc := by
    rw [disjoint_left]
    intro w hw hw'
    simp only [hSf, hPc, mem_image, mem_range] at hw hw'
    obtain ⟨j, hj, rfl⟩ := hw
    obtain ⟨i, hi, hci⟩ := hw'
    exact hcS i hi j hj hci
  have hcard : s + p ≤ n := by
    have := card_le_univ (Sf ∪ Pc)
    rw [card_union_of_disjoint hdisj, hSc, hPcc] at this
    exact this
  have hnotS : ∀ i < p, ∀ j < s, f j ≠ c i := fun i hi j hj h => hcS i hi j hj h.symm
  have hmemP : ∀ i < p, c i ∈ Pc := fun i hi => mem_image_of_mem c (mem_range.2 hi)
  set Rest := univ \ (Sf ∪ Pc) with hRestdef
  have hdeg_split : ∀ t, G.degree (c t) = dseg G (c t) f 0 s + (Pc.filter (G.Adj (c t))).card +
      (Rest.filter (G.Adj (c t))).card := fun t => by
    have := deg_split (G := G) (c t) Sf Pc hdisj
    rw [← dseg_eq_card_image hSinj] at this
    exact this
  have hPle : ∀ t < p, (Pc.filter (G.Adj (c t))).card + 1 ≤ p := fun t ht => by
    have := card_filter_adj_self_le (G := G) (hmemP t ht); rw [hPcc] at this; exact this
  have hRest : ∀ z ∈ Rest, (∀ j < s, f j ≠ z) ∧ (∀ i < p, c i ≠ z) := by
    intro z hz
    simp only [hRestdef, mem_sdiff, mem_univ, true_and, mem_union, not_or] at hz
    exact ⟨fun j hj h => hz.1 (h ▸ mem_image_of_mem f (mem_range.2 hj)),
      fun i hi h => hz.2 (h ▸ hmemP i hi)⟩
  set F : V → ℕ := fun z => bi (G.Adj (c (p - 3)) z) + bi (G.Adj (c (p - 2)) z) +
    bi (G.Adj (c (p - 1)) z) with hFdef
  have hFle : ∀ z ∈ Rest, F z ≤ 2 := by
    intro z hz
    obtain ⟨hzS, hzc⟩ := hRest z hz
    have hm := hmax z hzS hzc
    have := bi_le_one (G.Adj (c (p - 3)) z)
    have := bi_le_one (G.Adj (c (p - 2)) z)
    have := bi_le_one (G.Adj (c (p - 1)) z)
    simp only [hFdef]
    by_cases h1 : G.Adj (c (p - 1)) z <;> by_cases h2 : G.Adj (c (p - 2)) z <;>
      by_cases h3 : G.Adj (c (p - 3)) z
    · exact absurd ⟨h1, h2, fun _ => h3⟩ hm
    all_goals first
      | (rw [bi_neg h3]; omega)
      | (rw [bi_neg h2]; omega)
      | (rw [bi_neg h1]; omega)
  have hRsum : (Rest.filter (G.Adj (c (p - 3)))).card + (Rest.filter (G.Adj (c (p - 2)))).card +
      (Rest.filter (G.Adj (c (p - 1)))).card = ∑ z ∈ Rest, F z := by
    rw [card_filter_eq_sum_bi, card_filter_eq_sum_bi, card_filter_eq_sum_bi, ← sum_add_distrib,
      ← sum_add_distrib]
  have hR : ∑ z ∈ Rest, F z ≤ 2 * Rest.card := by
    calc _ ≤ Rest.card • 2 := sum_le_card_nsmul _ _ 2 hFle
      _ = 2 * Rest.card := by rw [smul_eq_mul, mul_comm]
  have hRc : Rest.card = n - (s + p) := by
    rw [hRestdef, card_univ_sdiff, card_union_of_disjoint hdisj, hSc, hPcc]
  have du := hdeg_split (p - 3)
  have dv := hdeg_split (p - 2)
  have dw := hdeg_split (p - 1)
  have pu := hPle (p - 3) (by omega)
  have pv := hPle (p - 2) (by omega)
  have pw := hPle (p - 1) (by omega)
  have eu := hdeg (c (p - 3)) (hnotS _ (by omega))
  have ev := hdeg (c (p - 2)) (hnotS _ (by omega))
  have ew := hdeg (c (p - 1)) (hnotS _ (by omega))
  -- everything is tight
  have tP : ∀ t, p - 3 ≤ t → t < p → (Pc.filter (G.Adj (c t))).card + 1 = p := by
    intro t ht1 ht2
    have : t = p - 3 ∨ t = p - 2 ∨ t = p - 1 := by omega
    rcases this with rfl | rfl | rfl <;> omega
  have htot : ∑ z ∈ Rest, F z = 2 * Rest.card := by omega
  refine ⟨by omega, fun t ht1 ht2 => ?_, fun t ht1 ht2 i hi hit => ?_, fun z hzS hzc => ?_⟩
  · have : t = p - 3 ∨ t = p - 2 ∨ t = p - 1 := by omega
    rcases this with rfl | rfl | rfl <;> omega
  · by_contra hna
    have hsub : Pc.filter (G.Adj (c t)) ⊆ (Pc.erase (c t)).erase (c i) := by
      intro w hw
      simp only [mem_filter] at hw
      refine mem_erase.2 ⟨fun h => hna (h ▸ hw.2), mem_erase.2 ⟨fun h => G.irrefl (h ▸ hw.2), hw.1⟩⟩
    have := card_le_card hsub
    have hne : c i ≠ c t := fun h => hit (hc.inj i t hi ht2 h)
    rw [card_erase_of_mem (mem_erase.2 ⟨hne, hmemP i hi⟩), card_erase_of_mem (hmemP t ht2),
      hPcc] at this
    have := tP t ht1 ht2
    omega
  · have hz : z ∈ Rest := by
      simp only [hRestdef, mem_sdiff, mem_univ, true_and, mem_union, not_or, hSf, hPc, mem_image,
        mem_range, not_exists, not_and]
      exact ⟨fun j hj h => hzS j hj h, fun i hi h => hzc i hi h⟩
    by_contra hne
    have hFz : F z ≤ 1 := by have := hFle z hz; simp only [hFdef] at this hne ⊢; omega
    have h1 := add_sum_erase Rest F hz
    have h2 : ∑ w ∈ Rest.erase z, F w ≤ 2 * (Rest.erase z).card := by
      calc _ ≤ (Rest.erase z).card • 2 :=
            sum_le_card_nsmul _ _ 2 (fun w hw => hFle w (mem_of_mem_erase hw))
        _ = 2 * (Rest.erase z).card := by rw [smul_eq_mul, mul_comm]
    rw [card_erase_of_mem hz] at h2
    have := card_pos.2 ⟨z, hz⟩
    omega

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
lemma IsCube.adj' {p : ℕ} {c : ℕ → V} (hc : IsCube G p c) {i j : ℕ} (hi : i < p) (hj : j < p)
    (hij : i ≠ j) (h1 : i ≤ j + 3) (h2 : j ≤ i + 3) : G.Adj (c i) (c j) := by
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hc.adj i j h (by omega) hj
  · exact (hc.adj j i h (by omega) hi).symm

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- A cube path read through an index permutation is a cube path, provided the new consecutive
triples are adjacent. -/
lemma IsCube.comp {p : ℕ} {c : ℕ → V} (hc : IsCube G p c) (σ : ℕ → ℕ) (hσ : ∀ j < p, σ j < p)
    (hσinj : ∀ j k, j < p → k < p → σ j = σ k → j = k)
    (hadj : ∀ j k, j < k → k ≤ j + 3 → k < p → G.Adj (c (σ j)) (c (σ k))) :
    IsCube G p (fun j => c (σ j)) :=
  ⟨hadj, fun j k hj hk h => hσinj j k hj hk (hc.inj _ _ (hσ j hj) (hσ k hk) h)⟩

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- A cube path whose vertices are pairwise adjacent can be read in any order. -/
lemma IsCube.comp_complete {p : ℕ} {c : ℕ → V} (hc : IsCube G p c)
    (hcomp : ∀ i < p, ∀ j < p, i ≠ j → G.Adj (c i) (c j)) (σ : ℕ → ℕ) (hσ : ∀ j < p, σ j < p)
    (hσinj : ∀ j k, j < p → k < p → σ j = σ k → j = k) :
    IsCube G p (fun j => c (σ j)) :=
  hc.comp σ hσ hσinj (fun j k hjk _ hk => hcomp _ (hσ j (by omega)) _ (hσ k hk)
    (fun h => by have := hσinj j k (by omega) hk h; omega))

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- A non-extendable version of maximality, in the form used by `lemma28x`. -/
lemma nonext_of_max {p : ℕ} {c : ℕ → V} (hc : IsCube G p c) (hp2 : 2 ≤ p)
    (hcS : ∀ i < p, ∀ j < s, c i ≠ f j)
    (hmax : ∀ c' : ℕ → V, IsCube G (p + 1) c' → (∀ i < p + 1, ∀ j < s, c' i ≠ f j) →
      c' 0 = c 0 → c' 1 = c 1 → False) :
    ∀ z, (∀ j < s, f j ≠ z) → (∀ i < p, c i ≠ z) →
      ¬ (G.Adj (c (p - 1)) z ∧ G.Adj (c (p - 2)) z ∧ (3 ≤ p → G.Adj (c (p - 3)) z)) := by
  intro z hzS hzc ⟨h1, h2, h3⟩
  have hext := hc.extend hzc (fun _ => h1) (fun _ => h2) h3
  refine hmax _ hext (fun i hi j hj => ?_) (by simp [show (0 : ℕ) < p by omega])
    (by simp [show (1 : ℕ) < p by omega])
  show (if i < p then c i else z) ≠ f j
  split_ifs with hip
  · exact hcS i hip j hj
  · exact fun h => hzS j hj h.symm

/-- **(E4)** In the extremal situation, a longest cube path (from its first ordered edge) is
complete. -/
lemma complete_of_max (hS : Opt G s f)
    (hdeg : ∀ v, (∀ j < s, f j ≠ v) → 2 * Fintype.card V ≤ 3 * G.degree v + 1)
    {p : ℕ} {c : ℕ → V} (hc : IsCube G p c) (hp4 : 4 ≤ p)
    (hcS : ∀ i < p, ∀ j < s, c i ≠ f j) (hsp : 2 * p + 2 ≤ s)
    (hmax : ∀ c' : ℕ → V, IsCube G (p + 1) c' → (∀ i < p + 1, ∀ j < s, c' i ≠ f j) →
      c' 0 = c 0 → c' 1 = c 1 → False) :
    ∀ i < p, ∀ j < p, i ≠ j → G.Adj (c i) (c j) := by
  obtain ⟨-, -, hT, -⟩ := lemma28x hS hdeg hc (by omega) hcS hsp
    (nonext_of_max hc (by omega) hcS hmax)
  -- `c i` is complete to the path for every `i ≥ 2`
  have key : ∀ i, 2 ≤ i → i < p → ∀ j < p, j ≠ i → G.Adj (c i) (c j) := by
    intro i hi2 hip
    set σ : ℕ → ℕ := fun j => if j < i then j else p - 1 + i - j with hσ
    have hσp : ∀ j < p, σ j < p := fun j hj => by simp only [hσ]; split_ifs <;> omega
    have hσinj : ∀ j k, j < p → k < p → σ j = σ k → j = k := by
      intro j k hj hk h; simp only [hσ] at h; split_ifs at h <;> omega
    have hd : IsCube G p (fun j => c (σ j)) := by
      refine hc.comp σ hσp hσinj (fun j k hjk hk3 hk => ?_)
      simp only [hσ]
      by_cases hj : j < i <;> by_cases hk' : k < i
      · rw [if_pos hj, if_pos hk']; exact hc.adj j k hjk hk3 hk
      · rw [if_pos hj, if_neg hk']
        exact (hT (p - 1 + i - k) (by omega) (by omega) j (by omega) (by omega)).symm
      · omega
      · rw [if_neg hj, if_neg hk']
        exact hc.adj' (by omega) (by omega) (by omega) (by omega) (by omega)
    have hdS : ∀ j < p, ∀ k < s, c (σ j) ≠ f k := fun j hj k hk => hcS _ (hσp j hj) k hk
    have hd0 : c (σ 0) = c 0 := by simp only [hσ]; rw [if_pos (by omega)]
    have hd1 : c (σ 1) = c 1 := by simp only [hσ]; rw [if_pos (by omega)]
    have hdmax : ∀ c' : ℕ → V, IsCube G (p + 1) c' → (∀ i < p + 1, ∀ j < s, c' i ≠ f j) →
        c' 0 = c (σ 0) → c' 1 = c (σ 1) → False := fun c' h1 h2 h3 h4 =>
      hmax c' h1 h2 (h3.trans hd0) (h4.trans hd1)
    obtain ⟨-, -, hT', -⟩ := lemma28x hS hdeg hd (by omega) hdS hsp
      (nonext_of_max hd (by omega) hdS hdmax)
    have hlast : c (σ (p - 1)) = c i := by
      simp only [hσ]; rw [if_neg (by omega)]; congr 1; omega
    intro j hj hji
    by_cases hjl : j < i
    · have := hT' (p - 1) (by omega) (by omega) j hj (by omega)
      rw [hlast] at this
      simpa [hσ, hjl] using this
    · have := hT' (p - 1) (by omega) (by omega) (p - 1 + i - j) (by omega) (by omega)
      rw [hlast] at this
      have e : σ (p - 1 + i - j) = j := by simp only [hσ]; rw [if_neg (by omega)]; omega
      rw [e] at this
      exact this
  intro i hi j hj hij
  by_cases hi2 : 2 ≤ i
  · exact key i hi2 hi j hj (Ne.symm hij)
  · by_cases hj2 : 2 ≤ j
    · exact (key j hj2 hj i hi hij).symm
    · exact hc.adj' hi hj hij (by omega) (by omega)

/- ### Index readings -/

/-- Reading indices from a list. -/
def pv (l : List ℕ) : ℕ → ℕ := fun j => l.getD j 0

lemma pv_lt {l : List ℕ} {p : ℕ} (hl : ∀ x ∈ l, x < p) : ∀ j < l.length, pv l j < p := by
  intro j hj
  unfold pv
  rw [List.getD_eq_getElem _ _ hj]
  exact hl _ (List.getElem_mem hj)

lemma pv_inj {l : List ℕ} (hl : l.Nodup) :
    ∀ j k, j < l.length → k < l.length → pv l j = pv l k → j = k := by
  intro j k hj hk h
  unfold pv at h
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hk] at h
  exact (hl.getElem_inj_iff).1 h

/-- The transposition of two indices. -/
def sw (a b : ℕ) : ℕ → ℕ := fun j => if j = a then b else if j = b then a else j

lemma sw_lt {a b p : ℕ} (ha : a < p) (hb : b < p) : ∀ j < p, sw a b j < p := by
  intro j hj; unfold sw; split_ifs <;> omega

lemma sw_inj {a b : ℕ} : ∀ j k, sw a b j = sw a b k → j = k := by
  intro j k h; unfold sw at h; split_ifs at h <;> omega

lemma sw_left (a b : ℕ) : sw a b a = b := by unfold sw; rw [if_pos rfl]

lemma sw_right {a b : ℕ} (h : a ≠ b) : sw a b b = a := by
  unfold sw; rw [if_neg (Ne.symm h), if_pos rfl]

lemma sw_other {a b j : ℕ} (ha : j ≠ a) (hb : j ≠ b) : sw a b j = j := by
  unfold sw; rw [if_neg ha, if_neg hb]

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
lemma IsCube.comp_complete' {p : ℕ} {c : ℕ → V} (hc : IsCube G p c)
    (hcomp : ∀ i < p, ∀ j < p, i ≠ j → G.Adj (c i) (c j)) {m : ℕ} (σ : ℕ → ℕ)
    (hσ : ∀ j < m, σ j < p) (hσinj : ∀ j k, j < m → k < m → σ j = σ k → j = k) :
    IsCube G m (fun j => c (σ j)) :=
  ⟨fun j k hjk _ hk => hcomp _ (hσ j (by omega)) _ (hσ k hk)
    (fun h => by have := hσinj j k (by omega) hk h; omega),
   fun j k hj hk h => hσinj j k hj hk (hc.inj _ _ (hσ j hj) (hσ k hk) h)⟩

omit [Fintype V] in
lemma card_filter_complete {p : ℕ} {c : ℕ → V} (hinj : ∀ i j, i < p → j < p → c i = c j → i = j)
    (hcomp : ∀ i < p, ∀ j < p, i ≠ j → G.Adj (c i) (c j)) {t : ℕ} (ht : t < p) :
    (((range p).image c).filter (G.Adj (c t))).card + 1 = p := by
  have : ((range p).image c).filter (G.Adj (c t)) = ((range p).image c).erase (c t) := by
    ext w
    simp only [mem_filter, mem_erase, mem_image, mem_range]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, ha⟩
      exact ⟨fun h => G.irrefl (h ▸ ha), ⟨i, hi, rfl⟩⟩
    · rintro ⟨hne, ⟨i, hi, rfl⟩⟩
      exact ⟨⟨i, hi, rfl⟩, hcomp t ht i hi (fun h => hne (h ▸ rfl))⟩
  rw [this, card_erase_of_mem (mem_image_of_mem c (mem_range.2 ht)), card_image_range hinj]
  omega

/-- **(2.9)** In the extremal situation, a longest cube path from a `B`-edge maximizing the cube
length, once complete, covers everything outside `S`. -/
lemma lemma29x (hS : Opt G s f)
    (hdeg : ∀ v, (∀ j < s, f j ≠ v) → 2 * Fintype.card V ≤ 3 * G.degree v + 1)
    {p : ℕ} {c : ℕ → V} (hc : IsCube G p c) (hp4 : 4 ≤ p)
    (hcS : ∀ i < p, ∀ j < s, c i ≠ f j) (hsp : 2 * p + 2 ≤ s)
    (hcomp : ∀ i < p, ∀ j < p, i ≠ j → G.Adj (c i) (c j))
    (hB0 : s + 2 ≤ dseg G (c 0) f 0 s + dseg G (c 1) f 0 s)
    (hmaxB : ∀ c' : ℕ → V, IsCube G (p + 1) c' → (∀ i < p + 1, ∀ j < s, c' i ≠ f j) →
      s + 2 ≤ dseg G (c' 0) f 0 s + dseg G (c' 1) f 0 s → False) :
    ∀ y, (∀ j < s, f j ≠ y) → ∃ i < p, c i = y := by
  classical
  intro y hyS
  by_contra hyP
  push Not at hyP
  have hSinj := hS.1.inj
  set Sf := (range s).image f with hSf
  set Pc := (range p).image c with hPc
  have hdisj : Disjoint Sf Pc := by
    rw [disjoint_left]
    intro w hw hw'
    simp only [hSf, hPc, mem_image, mem_range] at hw hw'
    obtain ⟨j, hj, rfl⟩ := hw
    obtain ⟨i, hi, hci⟩ := hw'
    exact hcS i hi j hj hci
  have hnotS : ∀ i < p, ∀ j < s, f j ≠ c i := fun i hi j hj h => hcS i hi j hj h.symm
  have memRest : ∀ z, (∀ j < s, f j ≠ z) → (∀ i < p, c i ≠ z) → z ∈ univ \ (Sf ∪ Pc) := by
    intro z hzS hzc
    simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or, hSf, hPc, mem_image,
      mem_range, not_exists, not_and]
    exact ⟨fun j hj h => hzS j hj h, fun i hi h => hzc i hi h⟩
  have ofRest : ∀ z ∈ univ \ (Sf ∪ Pc), (∀ j < s, f j ≠ z) ∧ (∀ i < p, c i ≠ z) := by
    intro z hz
    simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or] at hz
    exact ⟨fun j hj h => hz.1 (h ▸ mem_image_of_mem f (mem_range.2 hj)),
      fun i hi h => hz.2 (h ▸ mem_image_of_mem c (mem_range.2 hi))⟩
  -- readings of the complete path
  have hcube : ∀ (m : ℕ) (σ : ℕ → ℕ), (∀ j < m, σ j < p) →
      (∀ j k, j < m → k < m → σ j = σ k → j = k) → IsCube G m (fun j => c (σ j)) :=
    fun m σ h1 h2 => hc.comp_complete' hcomp σ h1 h2
  have hout : ∀ (m : ℕ) (σ : ℕ → ℕ), (∀ j < m, σ j < p) → ∀ j < m, ∀ k < s, c (σ j) ≠ f k :=
    fun m σ h1 j hj k hk => hcS _ (h1 j hj) k hk
  -- an extension to `p + 1` vertices means the starting edge is not in `B`
  have hext : ∀ (σ : ℕ → ℕ), (∀ j < p, σ j < p) → (∀ j k, j < p → k < p → σ j = σ k → j = k) →
      ∀ z, (∀ j < s, f j ≠ z) → (∀ i < p, c i ≠ z) → G.Adj (c (σ (p - 1))) z →
      G.Adj (c (σ (p - 2))) z → G.Adj (c (σ (p - 3))) z →
      dseg G (c (σ 0)) f 0 s + dseg G (c (σ 1)) f 0 s ≤ s + 1 := by
    intro σ h1 h2 z hzS hzc a1 a2 a3
    by_contra hcon
    push Not at hcon
    have he := (hcube p σ h1 h2).extend (z := z) (fun i hi h => hzc _ (h1 i hi) h)
      (fun _ => a1) (fun _ => a2) (fun _ => a3)
    refine hmaxB _ he (fun i hi j hj => ?_) ?_
    · show (if i < p then c (σ i) else z) ≠ f j
      split_ifs with hip
      · exact hcS _ (h1 i hip) j hj
      · exact fun h => hzS j hj h.symm
    · simp only [show (0 : ℕ) < p by omega, show (1 : ℕ) < p by omega, if_true]; omega
  -- readings starting at the first edge are longest: `lemma28x` applies
  have ORD : ∀ (σ : ℕ → ℕ), (∀ j < p, σ j < p) → (∀ j k, j < p → k < p → σ j = σ k → j = k) →
      ((σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)) →
      dseg G (c (σ (p - 3))) f 0 s + dseg G (c (σ (p - 2))) f 0 s + dseg G (c (σ (p - 1))) f 0 s =
        2 * s - p + 2 ∧
      (∀ t, p - 3 ≤ t → t < p → 3 * G.degree (c (σ t)) + 1 = 2 * Fintype.card V) ∧
      (∀ t, p - 3 ≤ t → t < p → ∀ i < p, i ≠ t → G.Adj (c (σ t)) (c (σ i))) ∧
      (∀ z, (∀ j < s, f j ≠ z) → (∀ i < p, c (σ i) ≠ z) →
        bi (G.Adj (c (σ (p - 3))) z) + bi (G.Adj (c (σ (p - 2))) z) +
          bi (G.Adj (c (σ (p - 1))) z) = 2) := by
    intro σ h1 h2 h0
    have hd := hcube p σ h1 h2
    refine lemma28x hS hdeg hd (by omega) (hout p σ h1) hsp
      (nonext_of_max hd (by omega) (hout p σ h1) ?_)
    intro c' hc' hc'S e0 e1
    refine hmaxB c' hc' hc'S ?_
    rw [e0, e1]
    rcases h0 with ⟨a, b⟩ | ⟨a, b⟩ <;> simp only [a, b] <;> omega
  have L25 : ∀ (σ : ℕ → ℕ), (∀ j < p, σ j < p) → (∀ j k, j < p → k < p → σ j = σ k → j = k) →
      dseg G (c (σ (p - 3))) f 0 s + dseg G (c (σ (p - 2))) f 0 s +
        dseg G (c (σ (p - 1))) f 0 s ≤ 2 * s - p + 2 :=
    fun σ h1 h2 => lemma25 hS hdeg (hcube p σ h1 h2) (by omega) (hout p σ h1) hsp
  have idlt : ∀ j < p, (fun j => j) j < p := fun j hj => hj
  have idinj : ∀ j k, j < p → k < p → (fun j : ℕ => j) j = (fun j : ℕ => j) k → j = k :=
    fun j k _ _ h => h
  have ORDid := ORD (fun j => j) idlt idinj (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨Cid, Aid, -, Did⟩ := ORDid
  -- degree comparison: if `c 0` has no neighbour outside `S ∪ P`, no end vertex can have one
  have hdegcmp : ∀ t, p - 3 ≤ t → 2 ≤ t → t < p →
      (∀ z, (∀ j < s, f j ≠ z) → (∀ i < p, c i ≠ z) → ¬ G.Adj (c 0) z) → G.Adj (c t) y → False := by
    intro t ht1 ht2 ht3 hno hty
    have L := L25 (sw 0 t) (sw_lt (by omega) ht3) (fun j k _ _ h => sw_inj j k h)
    have d0 := deg_split (G := G) (c 0) Sf Pc hdisj
    have dt := deg_split (G := G) (c t) Sf Pc hdisj
    rw [← dseg_eq_card_image hSinj] at d0 dt
    have p0 : (Pc.filter (G.Adj (c 0))).card + 1 ≤ p := by
      have := card_filter_adj_self_le (G := G) (mem_image_of_mem c (mem_range.2 (show 0 < p by omega)))
      rwa [card_image_range hc.inj] at this
    have pt : (Pc.filter (G.Adj (c t))).card + 1 = p := card_filter_complete hc.inj hcomp ht3
    have r0 : ((univ \ (Sf ∪ Pc)).filter (G.Adj (c 0))).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro z hz
      exact hno z (ofRest z hz).1 (ofRest z hz).2
    have rt : 1 ≤ ((univ \ (Sf ∪ Pc)).filter (G.Adj (c t))).card :=
      card_pos.2 ⟨y, mem_filter.2 ⟨memRest y hyS hyP, hty⟩⟩
    have e1 := Aid t ht1 ht3
    have e2 := hdeg (c 0) (hnotS 0 (by omega))
    have : t = p - 3 ∨ t = p - 2 ∨ t = p - 1 := by omega
    rcases this with rfl | rfl | rfl
    · rw [sw_right (by omega), sw_other (by omega) (by omega),
        sw_other (by omega) (by omega)] at L
      omega
    · rw [sw_other (by omega) (by omega), sw_right (by omega),
        sw_other (by omega) (by omega)] at L
      omega
    · rw [sw_other (by omega) (by omega), sw_other (by omega) (by omega),
        sw_right (by omega)] at L
      omega
  have STA : ∀ l : List ℕ, l.length = p → (∀ x ∈ l, x < p) → l.Nodup →
      StartsAt G s f p (c (pv l 0)) (c (pv l 1)) := fun l h1 h2 h3 =>
    ⟨_, (hcube p (pv l) (fun j hj => pv_lt h2 j (h1 ▸ hj))
      (fun j k hj hk => pv_inj h3 j k (h1 ▸ hj) (h1 ▸ hk))).isSq, rfl, rfl,
      hout p (pv l) (fun j hj => pv_lt h2 j (h1 ▸ hj))⟩
  have PV : ∀ l : List ℕ, l.length = p → (∀ x ∈ l, x < p) → l.Nodup →
      (∀ j < p, pv l j < p) ∧ (∀ j k, j < p → k < p → pv l j = pv l k → j = k) :=
    fun l h1 h2 h3 => ⟨fun j hj => pv_lt h2 j (h1 ▸ hj),
      fun j k hj hk => pv_inj h3 j k (h1 ▸ hj) (h1 ▸ hk)⟩
  rcases (show p = 4 ∨ p = 5 ∨ 6 ≤ p by omega) with hp | hp | hp6
  · -- `p = 4`
    subst hp
    simp only [show (4 : ℕ) - 3 = 1 from rfl, show (4 : ℕ) - 2 = 2 from rfl,
      show (4 : ℕ) - 1 = 3 from rfl] at Cid Did
    obtain ⟨-, -, -, Dsw⟩ := ORD (sw 0 1) (sw_lt (by omega) (by omega))
      (fun j k _ _ h => sw_inj j k h) (Or.inr ⟨sw_left 0 1, sw_right (by omega)⟩)
    simp only [show (4 : ℕ) - 3 = 1 from rfl, show (4 : ℕ) - 2 = 2 from rfl,
      show (4 : ℕ) - 1 = 3 from rfl] at Dsw
    rw [sw_right (by omega), sw_other (by omega) (by omega), sw_other (by omega) (by omega)] at Dsw
    have step1 : ∀ z, (∀ j < s, f j ≠ z) → (∀ i < 4, c i ≠ z) → G.Adj (c 0) z → G.Adj (c 1) z →
        ¬ G.Adj (c 2) z ∧ ¬ G.Adj (c 3) z := by
      intro z hzS hzc h0 h1
      constructor
      · intro h2
        have q1 := PV [3, 2, 1, 0] rfl (by decide) (by decide)
        have q2 := PV [3, 1, 2, 0] rfl (by decide) (by decide)
        have e1 := hext (pv [3, 2, 1, 0]) q1.1 q1.2 z hzS hzc h0 h1 h2
        have e2 := hext (pv [3, 1, 2, 0]) q2.1 q2.2 z hzS hzc h0 h2 h1
        have L9 := (lemma9 hS (hnotS 1 (by omega)) (hnotS 2 (by omega)) (p := 4) (by omega) hsp
          (STA [1, 2, 0, 3] rfl (by decide) (by decide))
          (STA [2, 1, 0, 3] rfl (by decide) (by decide))).1
        simp only [pv, List.getD_cons_zero, List.getD_cons_succ] at e1 e2 L9
        omega
      · intro h3
        have q1 := PV [2, 3, 1, 0] rfl (by decide) (by decide)
        have q2 := PV [2, 1, 3, 0] rfl (by decide) (by decide)
        have e1 := hext (pv [2, 3, 1, 0]) q1.1 q1.2 z hzS hzc h0 h1 h3
        have e2 := hext (pv [2, 1, 3, 0]) q2.1 q2.2 z hzS hzc h0 h3 h1
        have L9 := (lemma9 hS (hnotS 1 (by omega)) (hnotS 3 (by omega)) (p := 4) (by omega) hsp
          (STA [1, 3, 0, 2] rfl (by decide) (by decide))
          (STA [3, 1, 0, 2] rfl (by decide) (by decide))).1
        simp only [pv, List.getD_cons_zero, List.getD_cons_succ] at e1 e2 L9
        omega
    have step2 : ∀ z, (∀ j < s, f j ≠ z) → (∀ i < 4, c i ≠ z) → ¬ G.Adj (c 0) z := by
      intro z hzS hzc h0
      have D1 := Did z hzS hzc
      have D2 := Dsw z hzS (fun i hi => hzc _ (sw_lt (by omega) (by omega) i hi))
      have := bi_le_one (G.Adj (c 2) z)
      have := bi_le_one (G.Adj (c 3) z)
      by_cases h1 : G.Adj (c 1) z
      · obtain ⟨n2, n3⟩ := step1 z hzS hzc h0 h1
        rw [bi_pos h1, bi_neg n2, bi_neg n3] at D1; omega
      · rw [bi_neg h1] at D1
        rw [bi_pos h0] at D2
        omega
    have D := Did y hyS hyP
    by_cases h2 : G.Adj (c 2) y
    · exact hdegcmp 2 (by omega) (by omega) (by omega) step2 h2
    · by_cases h3 : G.Adj (c 3) y
      · exact hdegcmp 3 (by omega) (by omega) (by omega) step2 h3
      · rw [bi_neg h2, bi_neg h3] at D; have := bi_le_one (G.Adj (c 1) y); omega
  · -- `p = 5`
    subst hp
    simp only [show (5 : ℕ) - 3 = 2 from rfl, show (5 : ℕ) - 2 = 3 from rfl,
      show (5 : ℕ) - 1 = 4 from rfl] at Cid Did
    have step1 : ∀ a b d, a < 5 → b < 5 → d < 5 → 2 ≤ a → 2 ≤ b → 2 ≤ d → a ≠ b → a ≠ d →
        b ≠ d → ∀ z, (∀ j < s, f j ≠ z) → (∀ i < 5, c i ≠ z) → G.Adj (c 0) z →
        G.Adj (c 1) z → G.Adj (c a) z → G.Adj (c b) z → False := by
      intro a b d ha hb hd ha2 hb2 hd2 hab had hbd z hzS hzc h0 h1 hza hzb
      have q1 := PV [d, a, 0, 1, b] rfl (by simp; omega) (by simp; omega)
      have q2 := PV [d, b, 0, 1, a] rfl (by simp; omega) (by simp; omega)
      have e1 := hext (pv [d, a, 0, 1, b]) q1.1 q1.2 z hzS hzc hzb h1 h0
      have e2 := hext (pv [d, b, 0, 1, a]) q2.1 q2.2 z hzS hzc hza h1 h0
      have L9 := (lemma9 hS (hnotS a ha) (hnotS b hb) (p := 5) (by omega) hsp
        (STA [a, b, 0, 1, d] rfl (by simp; omega) (by simp; omega))
        (STA [b, a, 0, 1, d] rfl (by simp; omega) (by simp; omega))).1
      simp only [pv, List.getD_cons_zero, List.getD_cons_succ] at e1 e2 L9
      have hsum : dseg G (c a) f 0 s + dseg G (c b) f 0 s + dseg G (c d) f 0 s =
          dseg G (c 2) f 0 s + dseg G (c 3) f 0 s + dseg G (c 4) f 0 s := by
        rcases (show a = 2 ∨ a = 3 ∨ a = 4 by omega) with rfl | rfl | rfl <;>
        rcases (show b = 2 ∨ b = 3 ∨ b = 4 by omega) with rfl | rfl | rfl <;>
        rcases (show d = 2 ∨ d = 3 ∨ d = 4 by omega) with rfl | rfl | rfl <;> omega
      omega
    have step2 : ∀ a b, a < 5 → b < 5 → 2 ≤ a → 2 ≤ b → a ≠ b → ∀ u v,
        ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)) → ∀ z, (∀ j < s, f j ≠ z) → (∀ i < 5, c i ≠ z) →
        G.Adj (c u) z → G.Adj (c a) z → G.Adj (c b) z → G.Adj (c v) z := by
      intro a b ha hb ha2 hb2 hab u v huv z hzS hzc hu hza hzb
      have hu5 : u < 5 := by omega
      have hv5 : v < 5 := by omega
      have lt4 : ∀ x ∈ [v, u, a, b], x < 5 := by simp; omega
      have nd4 : [v, u, a, b].Nodup := by simp; omega
      have hd := hcube 4 (pv [v, u, a, b]) (fun j hj => pv_lt lt4 j hj)
        (fun j k hj hk => pv_inj nd4 j k hj hk)
      have he := hd.extend (z := z) (fun i hi h => hzc _ (pv_lt lt4 i hi) h)
        (fun _ => hzb) (fun _ => hza) (fun _ => hu)
      have heS : ∀ i < 4 + 1, ∀ j < s, (fun i => if i < 4 then c (pv [v, u, a, b] i) else z) i ≠ f j := by
        intro i hi j hj
        show (if i < 4 then c (pv [v, u, a, b] i) else z) ≠ f j
        split_ifs with hi4
        · exact hcS _ (pv_lt lt4 i hi4) j hj
        · exact fun h => hzS j hj h.symm
      obtain ⟨-, -, hT, -⟩ := lemma28x hS hdeg he (by omega) heS hsp
        (nonext_of_max he (by omega) heS (fun c'' h1 h2 e0 e1 => hmaxB c'' h1 h2 (by
          rw [e0, e1]
          simp only [show (0 : ℕ) < 4 from by omega, show (1 : ℕ) < 4 from by omega, if_true, pv,
            List.getD_cons_zero, List.getD_cons_succ]
          rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega)))
      have := hT 4 (by omega) (by omega) 0 (by omega) (by omega)
      simp only [show ¬ ((4 : ℕ) < 4) from by omega, show (0 : ℕ) < 4 from by omega, if_true,
        if_false, pv, List.getD_cons_zero] at this
      exact this.symm
    have step3 : ∀ z, (∀ j < s, f j ≠ z) → (∀ i < 5, c i ≠ z) → ¬ G.Adj (c 0) z := by
      intro z hzS hzc h0
      have D := Did z hzS hzc
      have g : ∀ a b d, a < 5 → b < 5 → d < 5 → 2 ≤ a → 2 ≤ b → 2 ≤ d → a ≠ b → a ≠ d →
          b ≠ d → G.Adj (c a) z → G.Adj (c b) z → False := fun a b d ha hb hd ha2 hb2 hd2 hab had hbd
          hza hzb => step1 a b d ha hb hd ha2 hb2 hd2 hab had hbd z hzS hzc h0
            (step2 a b ha hb ha2 hb2 hab 0 1 (Or.inl ⟨rfl, rfl⟩) z hzS hzc h0 hza hzb) hza hzb
      by_cases h2 : G.Adj (c 2) z <;> by_cases h3 : G.Adj (c 3) z <;> by_cases h4 : G.Adj (c 4) z
      · exact g 2 3 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) h2 h3
      · exact g 2 3 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) h2 h3
      · exact g 2 4 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) h2 h4
      · rw [bi_pos h2, bi_neg h3, bi_neg h4] at D; omega
      · exact g 3 4 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) h3 h4
      · rw [bi_neg h2, bi_pos h3, bi_neg h4] at D; omega
      · rw [bi_neg h2, bi_neg h3, bi_pos h4] at D; omega
      · rw [bi_neg h2, bi_neg h3, bi_neg h4] at D; omega
    have D := Did y hyS hyP
    by_cases h2 : G.Adj (c 2) y
    · exact hdegcmp 2 (by omega) (by omega) (by omega) step3 h2
    · by_cases h3 : G.Adj (c 3) y
      · exact hdegcmp 3 (by omega) (by omega) (by omega) step3 h3
      · by_cases h4 : G.Adj (c 4) y
        · exact hdegcmp 4 (by omega) (by omega) (by omega) step3 h4
        · rw [bi_neg h2, bi_neg h3, bi_neg h4] at D; omega
  · -- `p ≥ 6`: four triples among the last four vertices
    have D0 := Did y hyS hyP
    have hsw : ∀ b, p - 3 ≤ b → b < p →
        bi (G.Adj (c (sw (p - 4) b (p - 3))) y) + bi (G.Adj (c (sw (p - 4) b (p - 2))) y) +
          bi (G.Adj (c (sw (p - 4) b (p - 1))) y) = 2 := by
      intro b hb1 hb2
      exact (ORD (sw (p - 4) b) (sw_lt (by omega) hb2) (fun j k _ _ h => sw_inj j k h)
        (Or.inl ⟨sw_other (by omega) (by omega), sw_other (by omega) (by omega)⟩)).2.2.2 y hyS
        (fun i hi => hyP _ (sw_lt (by omega) hb2 i hi))
    have D1 := hsw (p - 3) (by omega) (by omega)
    have D2 := hsw (p - 2) (by omega) (by omega)
    have D3 := hsw (p - 1) (by omega) (by omega)
    rw [sw_right (by omega), sw_other (by omega) (by omega), sw_other (by omega) (by omega)] at D1
    rw [sw_other (by omega) (by omega), sw_right (by omega), sw_other (by omega) (by omega)] at D2
    rw [sw_other (by omega) (by omega), sw_other (by omega) (by omega), sw_right (by omega)] at D3
    have := bi_le_one (G.Adj (c (p - 4)) y)
    omega

/- ### Orderings of a set of indices -/

lemma exists_perm4 {h a b c d : ℕ} (ha : a < h) (hb : b < h) (hc : c < h) (hd : d < h)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ σ : ℕ → ℕ, (∀ j < h, σ j < h) ∧ (∀ j k, j < h → k < h → σ j = σ k → j = k) ∧
      σ 0 = a ∧ σ 1 = b ∧ σ (h - 2) = c ∧ σ (h - 1) = d := by
  set M := ((((range h).erase a).erase b).erase c).erase d with hM
  have hMc : M.card + 4 = h := by
    rw [hM, card_erase_of_mem, card_erase_of_mem, card_erase_of_mem, card_erase_of_mem, card_range]
    · have : 4 ≤ h := by omega
      omega
    all_goals simp only [mem_erase, mem_range]; omega
  set L := a :: b :: (M.toList ++ [c, d]) with hL
  have hlen : L.length = h := by simp [hL]; omega
  have hlt : ∀ x ∈ L, x < h := by
    intro x hx
    simp [hL, hM] at hx
    omega
  have hnd : L.Nodup := by
    simp [hL, hM, List.nodup_append]
    exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, nodup_toList _, hcd, fun x h1 h2 _ _ _ => ⟨h2, h1⟩⟩
  refine ⟨pv L, fun j hj => pv_lt hlt j (hlen ▸ hj),
    fun j k hj hk => pv_inj hnd j k (hlen ▸ hj) (hlen ▸ hk), by simp [pv, hL], by simp [pv, hL],
    ?_, ?_⟩
  · have e : h - 2 = M.toList.length + 2 := by simp; omega
    rw [e]; simp [pv, hL]
  · have e : h - 1 = M.toList.length + 3 := by simp; omega
    rw [e]; simp [pv, hL]

/-- Two prescribed first values (for `h ≥ 4`). -/
lemma exists_perm2 {h a b : ℕ} (h4 : 4 ≤ h) (ha : a < h) (hb : b < h) (hab : a ≠ b) :
    ∃ σ : ℕ → ℕ, (∀ j < h, σ j < h) ∧ (∀ j k, j < h → k < h → σ j = σ k → j = k) ∧
      σ 0 = a ∧ σ 1 = b := by
  obtain ⟨c, d, hc, hd, hca, hcb, hda, hdb, hcd⟩ : ∃ c d, c < h ∧ d < h ∧ c ≠ a ∧ c ≠ b ∧
      d ≠ a ∧ d ≠ b ∧ c ≠ d := by
    have h2 : 2 ≤ (((range 4).erase a).erase b).card := by
      have e1 := pred_card_le_card_erase (s := range 4) (a := a)
      have e2 := pred_card_le_card_erase (s := (range 4).erase a) (a := b)
      rw [card_range] at e1
      omega
    obtain ⟨c, hc⟩ := card_pos.1 (show 0 < (((range 4).erase a).erase b).card by omega)
    obtain ⟨d, hd⟩ := card_pos.1 (show 0 < ((((range 4).erase a).erase b).erase c).card by
      rw [card_erase_of_mem hc]; omega)
    simp only [mem_erase, mem_range] at hc hd
    exact ⟨c, d, by omega, by omega, hc.2.1, hc.1, hd.2.2.1, hd.2.1, Ne.symm hd.1⟩
  obtain ⟨σ, h1, h2, h3, h4, -, -⟩ := exists_perm4 ha hb hc hd hab (Ne.symm hca) (Ne.symm hda)
    (Ne.symm hcb) (Ne.symm hdb) hcd
  exact ⟨σ, h1, h2, h3, h4⟩

/- ### The final configuration: `H` complete -/

omit [Fintype V] in
omit [DecidableEq V] in
/-- Lemma 9 analysis for a pair of vertices of a complete `H` in the extremal case: the pair is
of type A (`q = q' = h`) or type B (`q = q' = h + 1`). -/
lemma pairFC (hS : Opt G s f) {h : ℕ} (hh : 2 ≤ h) (hsp : 2 * h + 2 ≤ s)
    {x y : V} (hxS : ∀ i < s, f i ≠ x) (hyS : ∀ i < s, f i ≠ y)
    (hP : StartsAt G s f h x y) (hP' : StartsAt G s f h y x)
    (hx3 : 3 * dseg G x f 0 s = 2 * s - h + 2) (hy3 : 3 * dseg G y f 0 s = 2 * s - h + 2) :
    (cnt2 G x y f (h - 1) ≠ 2 ∧ cnt2 G x y f h = 2 ∧ ∑ i ∈ range h, cnt2 G x y f i = h ∧
      3 * dseg G x f h (s - 2 * h) = 2 * (s - 2 * h) + 2 ∧
      3 * dseg G y f h (s - 2 * h) = 2 * (s - 2 * h) + 2) ∨
    (cnt2 G x y f (h - 1) = 2 ∧ cnt2 G x y f h = 0 ∧ ∑ i ∈ range h, cnt2 G x y f i = h + 1 ∧
      3 * dseg G x f (h + 1) (s - 2 * h - 2) = 2 * (s - 2 * h - 2) + 3 ∧
      3 * dseg G y f (h + 1) (s - 2 * h - 2) = 2 * (s - 2 * h - 2) + 3) := by
  have hOF := hS.optFix
  obtain ⟨q', hq', hQ'⟩ := lemma9_block_right hS hh hsp hP hP'
  have hL : ∀ i, i + 1 ≤ h → cnt2 G x y f i = 2 → cnt2 G x y f (i + 1) = 0 :=
    fun i hi h2 => lemma9_left hS hh hP hP' hi (by omega) h2
  have os := one_sided (cnt2 G x y f) (cnt2_le x y f) (h - 1) (fun i hi h2 => hL i (by omega) h2)
  rw [show h - 1 + 1 = h by omega] at os
  have hh1 := hL (h - 1) (by omega)
  rw [show h - 1 + 1 = h by omega] at hh1
  have hsr := sum_range_succ (cnt2 G x y f) h
  have hcl := cnt2_le (G := G) x y f h
  have dec : ∀ v : V, ∀ q, q + q' ≤ s → dseg G v f 0 s =
      dseg G v f 0 q + dseg G v f q (s - q - q') + dseg G v f (s - q') q' := by
    intro v q hq
    have h1 := dseg_add (G := G) v f 0 q (s - q)
    have h2 := dseg_add (G := G) v f q (s - q - q') q'
    rw [show q + (s - q) = s by omega, zero_add] at h1
    rw [show s - q - q' + q' = s - q by omega, show q + (s - q - q') = s - q' by omega] at h2
    omega
  have pairF : ∀ q, dseg G x f 0 q + dseg G y f 0 q = ∑ i ∈ range q, cnt2 G x y f i := by
    intro q; rw [dseg_pair_eq_sum, zero_add, range_eq_Ico]
  have pairB : dseg G x f (s - q') q' + dseg G y f (s - q') q' =
      ∑ i ∈ Ico (s - q') s, cnt2 G x y f i := by
    rw [dseg_pair_eq_sum, show s - q' + q' = s by omega]
  have dxh := dec x h (by omega)
  have dyh := dec y h (by omega)
  have dxh1 := dec x (h + 1) (by omega)
  have dyh1 := dec y (h + 1) (by omega)
  have Lxh := lemma1 hOF hxS (a := h) (q := s - h - q') (by omega)
  have Lyh := lemma1 hOF hyS (a := h) (q := s - h - q') (by omega)
  have Lxh1 := lemma1 hOF hxS (a := h + 1) (q := s - (h + 1) - q') (by omega)
  have Lyh1 := lemma1 hOF hyS (a := h + 1) (q := s - (h + 1) - q') (by omega)
  have pFh := pairF h
  have pFh1 := pairF (h + 1)
  by_cases hc1 : cnt2 G x y f (h - 1) = 2
  · right
    have hch := hh1 hc1
    rw [if_pos hc1] at os
    rcases hq' with hq | hq
    · exfalso; omega
    · refine ⟨hc1, hch, by omega, ?_, ?_⟩
      · rw [show s - 2 * h - 2 = s - (h + 1) - q' by omega]; omega
      · rw [show s - 2 * h - 2 = s - (h + 1) - q' by omega]; omega
  · left
    rw [if_neg hc1] at os
    rcases hq' with hq | hq
    · have hch : cnt2 G x y f h = 2 := by omega
      refine ⟨hc1, hch, by omega, ?_, ?_⟩
      · rw [show s - 2 * h = s - h - q' by omega]; omega
      · rw [show s - 2 * h = s - h - q' by omega]; omega
    · exfalso; omega

lemma exists_fourth {h a b c : ℕ} (h4 : 4 ≤ h) : ∃ d < h, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  by_cases h0 : 0 ≠ a ∧ 0 ≠ b ∧ 0 ≠ c
  · exact ⟨0, by omega, h0⟩
  by_cases h1 : 1 ≠ a ∧ 1 ≠ b ∧ 1 ≠ c
  · exact ⟨1, by omega, h1⟩
  by_cases h2 : 2 ≠ a ∧ 2 ≠ b ∧ 2 ≠ c
  · exact ⟨2, by omega, h2⟩
  exact ⟨3, by omega, by omega, by omega, by omega⟩

lemma exists_two_others {h a b : ℕ} (h4 : 4 ≤ h) :
    ∃ z w, z < h ∧ w < h ∧ z ≠ a ∧ z ≠ b ∧ w ≠ a ∧ w ≠ b ∧ z ≠ w := by
  obtain ⟨z, hz, h1, h2, -⟩ := exists_fourth (a := a) (b := b) (c := a) h4
  obtain ⟨w, hw, h3, h4, h5⟩ := exists_fourth (a := a) (b := b) (c := z) h4
  exact ⟨z, w, hz, hw, h1, h2, h3, h4, Ne.symm h5⟩

omit [Fintype V] in
omit [DecidableEq V] in
/-- A square path through reversed suffix of `S`, then `P`, then a few vertices of `S` before. -/
lemma assemble (hS : Opt G s f) {m q t : ℕ} (hm : m + 2 ≤ s) {P : ℕ → V} (hP : IsSq G q P)
    (hq : 2 ≤ q) (hPS : ∀ i < q, ∀ j < s, P i ≠ f j) (τ : ℕ → ℕ)
    (hτ : IsSq G t (fun i => f (τ i))) (_ht : 1 ≤ t) (hτm : ∀ i < t, τ i < m)
    (a1 : G.Adj (f m) (P 0)) (a2 : G.Adj (f (m + 1)) (P 0)) (a3 : G.Adj (f m) (P 1))
    (b1 : G.Adj (P (q - 1)) (f (τ 0))) (b2 : G.Adj (P (q - 2)) (f (τ 0)))
    (b3 : 2 ≤ t → G.Adj (P (q - 1)) (f (τ 1))) : s - m + q + t ≤ s := by
  have hA := hS.1.revSuffix m
  have hC := isSq_cat hA hP (fun i hi j hj he => hPS j hj _ (by omega) he.symm)
    (fun _ _ => by rw [show s - 1 - (s - m - 1) = m by omega]; exact a1)
    (fun _ _ => by rw [show s - 1 - (s - m - 2) = m + 1 by omega]; exact a2)
    (fun _ _ => by rw [show s - 1 - (s - m - 1) = m by omega]; exact a3)
  have hD := isSq_cat hC hτ (fun i hi j hj he => by
      unfold cat at he
      split_ifs at he with hi'
      · have := hS.1.inj _ _ (by omega) (by have := hτm j hj; omega) he
        have := hτm j hj
        omega
      · exact hPS _ (by omega) _ (by have := hτm j hj; omega) he)
    (fun _ _ => by
      unfold cat; rw [if_neg (by omega), show s - m + q - 1 - (s - m) = q - 1 by omega]; exact b1)
    (fun _ _ => by
      unfold cat; rw [if_neg (by omega), show s - m + q - 2 - (s - m) = q - 2 by omega]; exact b2)
    (fun _ h2 => by
      unfold cat; rw [if_neg (by omega), show s - m + q - 1 - (s - m) = q - 1 by omega]; exact b3 h2)
  exact (hS.2 _ _ hD).1

omit [Fintype V] in
omit [DecidableEq V] [DecidableRel G.Adj] in
lemma tailSq {s : ℕ} {f : ℕ → V} (hS : IsSq G s f) (l : List ℕ) (hl : ∀ x ∈ l, x < s)
    (hnd : l.Nodup)
    (hclose : ∀ i j, i < j → j ≤ i + 2 → j < l.length → pv l i ≤ pv l j + 2 ∧ pv l j ≤ pv l i + 2) :
    IsSq G l.length (fun i => f (pv l i)) :=
  hS.isSq_comp_close (pv l) (pv_lt hl) (pv_inj hnd) hclose

/-- **The final configuration** of the extremal Lemma 10: `H = G - S` is complete with `h ≥ 4`
vertices and `s ≥ 2h + 2`. This is impossible. -/
lemma lemmaFC (hS : Opt G s f)
    (hdeg : ∀ v, (∀ j < s, f j ≠ v) → 2 * Fintype.card V ≤ 3 * G.degree v + 1)
    (hn3 : Fintype.card V % 3 = 2)
    {h : ℕ} {c : ℕ → V} (hc : IsCube G h c) (hh4 : 4 ≤ h)
    (hcS : ∀ i < h, ∀ j < s, c i ≠ f j) (hsp : 2 * h + 2 ≤ s)
    (hcomp : ∀ i < h, ∀ j < h, i ≠ j → G.Adj (c i) (c j))
    (hcov : ∀ y, (∀ j < s, f j ≠ y) → ∃ i < h, c i = y) : False := by
  classical
  have hOF := hS.optFix
  have hSinj := hS.1.inj
  set Sf := (range s).image f with hSf
  set Pc := (range h).image c with hPc
  have hdisj : Disjoint Sf Pc := by
    rw [disjoint_left]
    intro w hw hw'
    simp only [hSf, hPc, mem_image, mem_range] at hw hw'
    obtain ⟨j, hj, rfl⟩ := hw
    obtain ⟨i, hi, hci⟩ := hw'
    exact hcS i hi j hj hci
  have hnotS : ∀ i < h, ∀ j < s, f j ≠ c i := fun i hi j hj h => hcS i hi j hj h.symm
  have hRest : univ \ (Sf ∪ Pc) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro z hz
    simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or] at hz
    obtain ⟨i, hi, rfl⟩ := hcov z (fun j hj he => hz.1 (he ▸ mem_image_of_mem f (mem_range.2 hj)))
    exact hz.2 (mem_image_of_mem c (mem_range.2 hi))
  have hn : Fintype.card V = s + h := by
    have e := card_univ_sdiff (Sf ∪ Pc)
    rw [hRest, card_empty, card_union_of_disjoint hdisj, card_image_range hSinj,
      card_image_range hc.inj] at e
    have := card_le_univ (Sf ∪ Pc)
    rw [card_union_of_disjoint hdisj, card_image_range hSinj, card_image_range hc.inj] at this
    omega
  have hdegc : ∀ i < h, G.degree (c i) = dseg G (c i) f 0 s + (h - 1) := by
    intro i hi
    have d := deg_split (G := G) (c i) Sf Pc hdisj
    rw [← dseg_eq_card_image hSinj, hRest, filter_empty, card_empty, add_zero] at d
    have : (Pc.filter (G.Adj (c i))).card + 1 = h := card_filter_complete hc.inj hcomp hi
    omega
  have STA : ∀ i j, i < h → j < h → i ≠ j → StartsAt G s f h (c i) (c j) := by
    intro i j hi hj hij
    obtain ⟨σ, h1, h2, h3, h4⟩ := exists_perm2 hh4 hi hj hij
    exact ⟨_, (hc.comp_complete' hcomp σ h1 h2).isSq, by simp only [h3], by simp only [h4],
      fun k hk l hl => hcS _ (h1 k hk) l hl⟩
  have h3d : ∀ i < h, 3 * dseg G (c i) f 0 s = 2 * s - h + 2 := by
    intro i hi
    obtain ⟨j, hj, hji⟩ : ∃ j < h, j ≠ i :=
      ⟨if i = 0 then 1 else 0, by split_ifs <;> omega, by split_ifs <;> omega⟩
    have L9 := (lemma9 hS (hnotS i hi) (hnotS j hj) (p := h) (by omega) hsp
      (STA i j hi hj (Ne.symm hji)) (STA j i hj hi hji)).1
    have e1 := hdeg (c i) (hnotS i hi)
    have e2 := hdeg (c j) (hnotS j hj)
    rw [hdegc i hi] at e1
    rw [hdegc j hj] at e2
    omega
  have PT := fun i j (hi : i < h) (hj : j < h) (hij : i ≠ j) =>
    pairFC hS (by omega) hsp (hnotS i hi) (hnotS j hj) (STA i j hi hj hij)
      (STA j i hj hi (Ne.symm hij)) (h3d i hi) (h3d j hj)
  have RD : ∀ σ : ℕ → ℕ, (∀ j < h, σ j < h) → (∀ j k, j < h → k < h → σ j = σ k → j = k) →
      IsSq G h (fun j => c (σ j)) ∧ ∀ i < h, ∀ j < s, c (σ i) ≠ f j :=
    fun σ h1 h2 => ⟨(hc.comp_complete' hcomp σ h1 h2).isSq, fun i hi j hj => hcS _ (h1 i hi) j hj⟩
  have other : ∀ j < h, ∃ k < h, k ≠ j := fun j hj =>
    ⟨if j = 0 then 1 else 0, by split_ifs <;> omega, by split_ifs <;> omega⟩
  by_cases hB : ∃ i < h, ¬ G.Adj (c i) (f h)
  · -- Type B
    obtain ⟨i0, hi0, hn0⟩ := hB
    have nh : ∀ j < h, ¬ G.Adj (c j) (f h) := by
      intro j hj
      by_cases hji : j = i0
      · rw [hji]; exact hn0
      · rcases PT i0 j hi0 hj (Ne.symm hji) with ⟨-, hA, -⟩ | ⟨-, hB0, -⟩
        · exact absurd (cnt2_two hA).1 hn0
        · intro ha; unfold cnt2 at hB0; rw [bi_pos ha] at hB0; omega
    have typeB : ∀ j k, (hj : j < h) → (hk : k < h) → (hjk : j ≠ k) →
        cnt2 G (c j) (c k) f (h - 1) = 2 ∧ cnt2 G (c j) (c k) f h = 0 ∧
        ∑ i ∈ range h, cnt2 G (c j) (c k) f i = h + 1 ∧
        3 * dseg G (c j) f (h + 1) (s - 2 * h - 2) = 2 * (s - 2 * h - 2) + 3 ∧
        3 * dseg G (c k) f (h + 1) (s - 2 * h - 2) = 2 * (s - 2 * h - 2) + 3 := by
      intro j k hj hk hjk
      rcases PT j k hj hk hjk with ⟨-, hA, -⟩ | hBt
      · exact absurd (cnt2_two hA).1 (nh j hj)
      · exact hBt
    have adjB : ∀ j < h, G.Adj (c j) (f (h - 1)) ∧ G.Adj (c j) (f (h + 1)) ∧
        G.Adj (c j) (f (h + 2)) := by
      intro j hj
      obtain ⟨k, hk, hkj⟩ := other j hj
      obtain ⟨e1, -, -, e4, -⟩ := typeB j k hj hk (Ne.symm hkj)
      obtain ⟨l1, l2, -⟩ := lemma2 hOF (hnotS j hj) (a := h + 1) (q := s - 2 * h - 2) (by omega) e4
      exact ⟨(cnt2_two e1).1, l1, l2⟩
    by_cases hz : ∃ j < h, G.Adj (c j) (f (h - 2))
    · obtain ⟨j0, hj0, hzj⟩ := hz
      have hσ1 : ∀ j < h, sw (h - 1) j0 j < h := sw_lt (by omega) hj0
      obtain ⟨hPs, hPS⟩ := RD (sw (h - 1) j0) hσ1 (fun j k _ _ e => sw_inj j k e)
      have hτ := tailSq hS.1 [h - 1, h - 2] (by simp; omega) (by simp; omega) (by
        intro i j hij hj2 hj; simp at hj; interval_cases j <;> interval_cases i; simp [pv]; omega)
      have := assemble hS (m := h + 1) (by omega) hPs (by omega) hPS (pv [h - 1, h - 2]) hτ
        (by simp) (by intro i hi; simp at hi; interval_cases i <;> simp [pv])
        (adjB _ (hσ1 0 (by omega))).2.1.symm (adjB _ (hσ1 0 (by omega))).2.2.symm
        (adjB _ (hσ1 1 (by omega))).2.1.symm
        (by show G.Adj (c (sw (h - 1) j0 (h - 1))) (f (pv [h - 1, h - 2] 0))
            rw [sw_left]; exact (adjB j0 hj0).1)
        (by show G.Adj (c (sw (h - 1) j0 (h - 2))) (f (pv [h - 1, h - 2] 0))
            exact (adjB _ (hσ1 (h - 2) (by omega))).1)
        (fun _ => by show G.Adj (c (sw (h - 1) j0 (h - 1))) (f (pv [h - 1, h - 2] 1))
                     rw [sw_left]; exact hzj)
      simp at this
      omega
    · push Not at hz
      obtain ⟨e1, -, e3, -, -⟩ := typeB (h - 1) (h - 2) (by omega) (by omega) (by omega)
      have hc2 : cnt2 G (c (h - 1)) (c (h - 2)) f (h - 2) = 0 :=
        cnt2_zero (hz _ (by omega)) (hz _ (by omega))
      have hL : ∀ i, i + 1 ≤ h → cnt2 G (c (h - 1)) (c (h - 2)) f i = 2 →
          cnt2 G (c (h - 1)) (c (h - 2)) f (i + 1) = 0 := fun i hi h2 =>
        lemma9_left hS (by omega) (STA (h - 1) (h - 2) (by omega) (by omega) (by omega))
          (STA (h - 2) (h - 1) (by omega) (by omega) (by omega)) hi (by omega) h2
      have os := one_sided (cnt2 G (c (h - 1)) (c (h - 2)) f) (cnt2_le _ _ f) (h - 3)
        (fun i hi h2 => hL i (by omega) h2)
      have s1 := sum_range_succ (cnt2 G (c (h - 1)) (c (h - 2)) f) (h - 2)
      have s2 := sum_range_succ (cnt2 G (c (h - 1)) (c (h - 2)) f) (h - 1)
      rw [show h - 3 + 1 = h - 2 by omega] at os
      rw [show h - 2 + 1 = h - 1 by omega] at s1
      rw [show h - 1 + 1 = h by omega] at s2
      have hc3 : cnt2 G (c (h - 1)) (c (h - 2)) f (h - 3) = 2 := by
        by_contra hne
        rw [if_neg hne] at os
        omega
      have hx3 := (cnt2_two hc3).1
      have hτ := tailSq hS.1 [h - 1, h - 3, h - 2] (by simp; omega) (by simp; omega) (by
        intro i j hij hj2 hj; simp at hj; interval_cases j <;> interval_cases i <;> simp [pv] <;> omega)
      have := assemble hS (m := h + 1) (by omega) hc.isSq (by omega) hcS (pv [h - 1, h - 3, h - 2]) hτ
        (by simp) (by intro i hi; simp at hi; interval_cases i <;> simp [pv])
        (adjB 0 (by omega)).2.1.symm (adjB 0 (by omega)).2.2.symm (adjB 1 (by omega)).2.1.symm
        (by show G.Adj (c (h - 1)) (f (pv [h - 1, h - 3, h - 2] 0)); exact (adjB _ (by omega)).1)
        (by show G.Adj (c (h - 2)) (f (pv [h - 1, h - 3, h - 2] 0)); exact (adjB _ (by omega)).1)
        (fun _ => by show G.Adj (c (h - 1)) (f (pv [h - 1, h - 3, h - 2] 1)); exact hx3)
      simp at this
      omega
  · -- Type A
    push Not at hB
    have typeA : ∀ j k, (hj : j < h) → (hk : k < h) → (hjk : j ≠ k) →
        cnt2 G (c j) (c k) f (h - 1) ≠ 2 ∧ ∑ i ∈ range h, cnt2 G (c j) (c k) f i = h ∧
        3 * dseg G (c j) f h (s - 2 * h) = 2 * (s - 2 * h) + 2 := by
      intro j k hj hk hjk
      rcases PT j k hj hk hjk with ⟨a1, -, a3, a4, -⟩ | ⟨-, hB0, -⟩
      · exact ⟨a1, a3, a4⟩
      · exfalso; unfold cnt2 at hB0; rw [bi_pos (hB j hj), bi_pos (hB k hk)] at hB0; omega
    have hA1 : ∀ j k, j < h → k < h → j ≠ k → G.Adj (c j) (f (h - 1)) → ¬ G.Adj (c k) (f (h - 1)) := by
      intro j k hj hk hjk h1 h2
      apply (typeA j k hj hk hjk).1
      unfold cnt2; rw [bi_pos h1, bi_pos h2]
    have hAd : ∀ j < h, ¬ G.Adj (c j) (f (h - 1)) → G.Adj (c j) (f (h - 2)) := by
      intro j hj hnj
      obtain ⟨k1, k2, hk1, hk2, e1, -, e3, -, e5⟩ := exists_two_others (a := j) (b := j) hh4
      obtain ⟨k, hk, hkj, hnk⟩ : ∃ k < h, k ≠ j ∧ ¬ G.Adj (c k) (f (h - 1)) := by
        by_cases h1 : G.Adj (c k1) (f (h - 1))
        · exact ⟨k2, hk2, e3, hA1 k1 k2 hk1 hk2 e5 h1⟩
        · exact ⟨k1, hk1, e1, h1⟩
      obtain ⟨-, hsum, -⟩ := typeA j k hj hk (Ne.symm hkj)
      have hc1 : cnt2 G (c j) (c k) f (h - 1) = 0 := cnt2_zero hnj hnk
      have hL : ∀ i, i + 1 ≤ h → cnt2 G (c j) (c k) f i = 2 → cnt2 G (c j) (c k) f (i + 1) = 0 :=
        fun i hi h2 => lemma9_left hS (by omega) (STA j k hj hk (Ne.symm hkj))
          (STA k j hk hj hkj) hi (by omega) h2
      have os := one_sided (cnt2 G (c j) (c k) f) (cnt2_le _ _ f) (h - 2)
        (fun i hi h2 => hL i (by omega) h2)
      have s2 := sum_range_succ (cnt2 G (c j) (c k) f) (h - 1)
      rw [show h - 2 + 1 = h - 1 by omega] at os
      rw [show h - 1 + 1 = h by omega] at s2
      have hc2 : cnt2 G (c j) (c k) f (h - 2) = 2 := by
        by_contra hne
        rw [if_neg hne] at os
        omega
      exact (cnt2_two hc2).1
    have hL2 : ∀ j < h, ¬ G.Adj (c j) (f (h + 1)) →
        G.Adj (c j) (f (h + 2)) ∧ G.Adj (c j) (f (h + 3)) := by
      intro j hj hn1
      obtain ⟨k, hk, hkj⟩ := other j hj
      obtain ⟨-, -, e3⟩ := typeA j k hj hk (Ne.symm hkj)
      have d1 := dseg_add (G := G) (c j) f h 1 (s - 2 * h - 1)
      have d2 := dseg_add (G := G) (c j) f (h + 1) 1 (s - 2 * h - 2)
      rw [show 1 + (s - 2 * h - 1) = s - 2 * h by omega, dseg_one, if_pos (hB j hj)] at d1
      rw [show 1 + (s - 2 * h - 2) = s - 2 * h - 1 by omega, dseg_one, if_neg hn1,
        show h + 1 + 1 = h + 2 by omega] at d2
      obtain ⟨l1, l2, -⟩ := lemma2 hOF (hnotS j hj) (a := h + 2) (q := s - 2 * h - 2) (by omega)
        (by omega)
      exact ⟨l1, l2⟩
    -- the path for the case of two vertices not adjacent to `f (h+1)`, with `P` ending at `v`
    have pathA1i : ∀ j1 k1 w v, j1 < h → k1 < h → w < h → v < h → j1 ≠ k1 → j1 ≠ w → j1 ≠ v →
        k1 ≠ w → k1 ≠ v → w ≠ v → G.Adj (c j1) (f (h + 2)) → G.Adj (c j1) (f (h + 3)) →
        G.Adj (c k1) (f (h + 2)) → G.Adj (c v) (f (h - 1)) → False := by
      intro j1 k1 w v hj1 hk1 hw hv n1 n2 n3 n4 n5 n6 a1 a2 a3 a4
      obtain ⟨σ, h1, h2, e0, e1, e2, e3⟩ := exists_perm4 hj1 hk1 hw hv n1 n2 n3 n4 n5 n6
      obtain ⟨hPs, hPS⟩ := RD σ h1 h2
      have hτ := tailSq hS.1 [h, h - 1, h + 1] (by simp; omega) (by simp; omega) (by
        intro i j hij hj2 hj; simp at hj; interval_cases j <;> interval_cases i <;> simp [pv] <;> omega)
      have := assemble hS (m := h + 2) (by omega) hPs (by omega) hPS (pv [h, h - 1, h + 1]) hτ
        (by simp) (by intro i hi; simp at hi; interval_cases i <;> simp [pv]; omega)
        (by simp only [e0]; exact a1.symm) (by simp only [e0]; exact a2.symm)
        (by simp only [e1]; exact a3.symm)
        (by show G.Adj (c (σ (h - 1))) (f (pv [h, h - 1, h + 1] 0)); rw [e3]; exact hB v hv)
        (by show G.Adj (c (σ (h - 2))) (f (pv [h, h - 1, h + 1] 0)); rw [e2]; exact hB w hw)
        (fun _ => by show G.Adj (c (σ (h - 1))) (f (pv [h, h - 1, h + 1] 1)); rw [e3]; exact a4)
      simp at this
      omega
    have pathA1ii : ∀ j1 k1 z w, j1 < h → k1 < h → z < h → w < h → j1 ≠ k1 → j1 ≠ z → j1 ≠ w →
        k1 ≠ z → k1 ≠ w → z ≠ w → G.Adj (c j1) (f (h + 2)) → G.Adj (c j1) (f (h + 3)) →
        G.Adj (c k1) (f (h + 2)) → G.Adj (c z) (f (h - 2)) → G.Adj (c w) (f (h - 2)) → False := by
      intro j1 k1 z w hj1 hk1 hz hw n1 n2 n3 n4 n5 n6 a1 a2 a3 a4 a5
      obtain ⟨σ, h1, h2, e0, e1, e2, e3⟩ := exists_perm4 hj1 hk1 hz hw n1 n2 n3 n4 n5 n6
      obtain ⟨hPs, hPS⟩ := RD σ h1 h2
      have hτ := tailSq hS.1 [h - 2, h, h - 1, h + 1] (by simp; omega) (by simp; omega) (by
        intro i j hij hj2 hj; simp at hj; interval_cases j <;> interval_cases i <;> simp [pv] <;> omega)
      have := assemble hS (m := h + 2) (by omega) hPs (by omega) hPS (pv [h - 2, h, h - 1, h + 1]) hτ
        (by simp) (by intro i hi; simp at hi; interval_cases i <;> simp [pv] <;> omega)
        (by simp only [e0]; exact a1.symm) (by simp only [e0]; exact a2.symm)
        (by simp only [e1]; exact a3.symm)
        (by show G.Adj (c (σ (h - 1))) (f (pv [h - 2, h, h - 1, h + 1] 0)); rw [e3]; exact a5)
        (by show G.Adj (c (σ (h - 2))) (f (pv [h - 2, h, h - 1, h + 1] 0)); rw [e2]; exact a4)
        (fun _ => by show G.Adj (c (σ (h - 1))) (f (pv [h - 2, h, h - 1, h + 1] 1)); rw [e3];
                     exact hB w hw)
      simp at this
      omega
    have pathA2 : ∀ a b z w, a < h → b < h → z < h → w < h → a ≠ b → a ≠ z → a ≠ w →
        b ≠ z → b ≠ w → z ≠ w → G.Adj (c a) (f (h + 1)) → G.Adj (c z) (f (h - 2)) →
        G.Adj (c w) (f (h - 2)) → False := by
      intro a b z w ha hb hz hw n1 n2 n3 n4 n5 n6 a1 a2 a3
      obtain ⟨σ, h1, h2, e0, e1, e2, e3⟩ := exists_perm4 ha hb hz hw n1 n2 n3 n4 n5 n6
      obtain ⟨hPs, hPS⟩ := RD σ h1 h2
      have hτ := tailSq hS.1 [h - 2] (by simp; omega) (by simp) (by
        intro i j hij hj2 hj; simp at hj; omega)
      have := assemble hS (m := h) (by omega) hPs (by omega) hPS (pv [h - 2]) hτ
        (by simp) (by intro i hi; simp at hi; subst hi; simp [pv]; omega)
        (by simp only [e0]; exact (hB a ha).symm) (by simp only [e0]; exact a1.symm)
        (by simp only [e1]; exact (hB b hb).symm)
        (by show G.Adj (c (σ (h - 1))) (f (pv [h - 2] 0)); rw [e3]; exact a3)
        (by show G.Adj (c (σ (h - 2))) (f (pv [h - 2] 0)); rw [e2]; exact a2)
        (fun h2 => by simp at h2)
      simp at this
      omega
    by_cases hA2 : ∃ j k, j < h ∧ k < h ∧ j ≠ k ∧ ¬ G.Adj (c j) (f (h + 1)) ∧
        ¬ G.Adj (c k) (f (h + 1))
    · obtain ⟨j1, k1, hj1, hk1, hjk, hn1, hn2⟩ := hA2
      obtain ⟨a1, a2⟩ := hL2 j1 hj1 hn1
      obtain ⟨a3, -⟩ := hL2 k1 hk1 hn2
      by_cases hv : ∃ v < h, v ≠ j1 ∧ v ≠ k1 ∧ G.Adj (c v) (f (h - 1))
      · obtain ⟨v, hv, hv1, hv2, hv3⟩ := hv
        obtain ⟨w, hw, w1, w2, w3⟩ := exists_fourth (a := j1) (b := k1) (c := v) hh4
        exact pathA1i j1 k1 w v hj1 hk1 hw hv hjk (Ne.symm w1) (Ne.symm hv1) (Ne.symm w2)
          (Ne.symm hv2) w3 a1 a2 a3 hv3
      · push Not at hv
        obtain ⟨z, w, hz, hw, z1, z2, w1, w2, hzw⟩ := exists_two_others (a := j1) (b := k1) hh4
        exact pathA1ii j1 k1 z w hj1 hk1 hz hw hjk (Ne.symm z1) (Ne.symm w1) (Ne.symm z2)
          (Ne.symm w2) hzw a1 a2 a3 (hAd z hz (hv z hz z1 z2)) (hAd w hw (hv w hw w1 w2))
    · push Not at hA2
      -- two vertices among `c 0, c 1, c 2` adjacent to `f (h-2)`, and the other two of `0..3`
      have pick : ∀ z w r1 r2, z < h → w < h → r1 < h → r2 < h → z ≠ w → z ≠ r1 → z ≠ r2 →
          w ≠ r1 → w ≠ r2 → r1 ≠ r2 → G.Adj (c z) (f (h - 2)) → G.Adj (c w) (f (h - 2)) →
          False := by
        intro z w r1 r2 hz hw hr1 hr2 n1 n2 n3 n4 n5 n6 g1 g2
        by_cases hr : G.Adj (c r1) (f (h + 1))
        · exact pathA2 r1 r2 z w hr1 hr2 hz hw n6 (Ne.symm n2) (Ne.symm n4) (Ne.symm n3)
            (Ne.symm n5) n1 hr g1 g2
        · exact pathA2 r2 r1 z w hr2 hr1 hz hw (Ne.symm n6) (Ne.symm n3) (Ne.symm n5)
            (Ne.symm n2) (Ne.symm n4) n1 (hA2 r1 r2 hr1 hr2 n6 hr) g1 g2
      by_cases g0 : G.Adj (c 0) (f (h - 2))
      · by_cases g1 : G.Adj (c 1) (f (h - 2))
        · exact pick 0 1 2 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) g0 g1
        · have a1 : G.Adj (c 1) (f (h - 1)) := by
            by_contra hc1; exact g1 (hAd 1 (by omega) hc1)
          have g2 := hAd 2 (by omega) (hA1 1 2 (by omega) (by omega) (by omega) a1)
          exact pick 0 2 1 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) g0 g2
      · have a0 : G.Adj (c 0) (f (h - 1)) := by
          by_contra hc0; exact g0 (hAd 0 (by omega) hc0)
        have g1 := hAd 1 (by omega) (hA1 0 1 (by omega) (by omega) (by omega) a0)
        have g2 := hAd 2 (by omega) (hA1 0 2 (by omega) (by omega) (by omega) a0)
        exact pick 1 2 0 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) g1 g2

omit [Fintype V] in
omit [DecidableEq V] in
/-- A square path through a reversed suffix of `S`, a few vertices of `S` before it, then `Q`. -/
lemma assemble2 (hS : Opt G s f) {m k q : ℕ} (hm : m + 2 ≤ s) {π : ℕ → ℕ}
    (hτ : IsSq G k (fun i => f (π i))) (hk : 2 ≤ k) (hπm : ∀ i < k, π i < m)
    {Q : ℕ → V} (hQ : IsSq G q Q) (_hq : 2 ≤ q) (hQS : ∀ i < q, ∀ j < s, Q i ≠ f j)
    (a1 : G.Adj (f m) (f (π 0))) (a2 : G.Adj (f (m + 1)) (f (π 0)))
    (a3 : G.Adj (f m) (f (π 1)))
    (b1 : G.Adj (f (π (k - 1))) (Q 0)) (b2 : G.Adj (f (π (k - 2))) (Q 0))
    (b3 : G.Adj (f (π (k - 1))) (Q 1)) : s - m + k + q ≤ s := by
  have hA := hS.1.revSuffix m
  have hC := isSq_cat hA hτ (fun i hi j hj he => by
      have := hS.1.inj _ _ (by omega) (by have := hπm j hj; omega) he
      have := hπm j hj
      omega)
    (fun _ _ => by rw [show s - 1 - (s - m - 1) = m by omega]; exact a1)
    (fun _ _ => by rw [show s - 1 - (s - m - 2) = m + 1 by omega]; exact a2)
    (fun _ _ => by rw [show s - 1 - (s - m - 1) = m by omega]; exact a3)
  have hD := isSq_cat hC hQ (fun i hi j hj he => by
      unfold cat at he
      split_ifs at he with hi'
      · exact hQS j hj _ (by omega) he.symm
      · exact hQS j hj _ (by have := hπm (i - (s - m)) (by omega); omega) he.symm)
    (fun _ _ => by
      unfold cat; rw [if_neg (by omega), show s - m + k - 1 - (s - m) = k - 1 by omega]; exact b1)
    (fun _ _ => by
      unfold cat; rw [if_neg (by omega), show s - m + k - 2 - (s - m) = k - 2 by omega]; exact b2)
    (fun _ _ => by
      unfold cat; rw [if_neg (by omega), show s - m + k - 1 - (s - m) = k - 1 by omega]; exact b3)
  exact (hS.2 _ _ hD).1

end L28

section L10x

variable [Fintype V] {s : ℕ} {f : ℕ → V}

/-- **Lemma 10** (Fan–Kierstead), including the extremal case: if every vertex outside an
optimal square path `S` has degree at least `(2n-1)/3`, then every edge outside `S` has at most
`s+1` neighbours in `S`. -/
theorem lemma10x (hS : Opt G s f)
    (hdeg : ∀ v, (∀ j < s, f j ≠ v) → 2 * Fintype.card V ≤ 3 * G.degree v + 1)
    {x y : V} (hx : ∀ j < s, f j ≠ x) (hy : ∀ j < s, f j ≠ y) (hxy : G.Adj x y) :
    dseg G x f 0 s + dseg G y f 0 s ≤ s + 1 := by
  classical
  by_cases hn3 : Fintype.card V % 3 = 2
  swap
  · exact lemma10 hS (fun v hv => by have := hdeg v hv; omega) hx hy hxy
  by_contra hcon
  push Not at hcon
  let CPB : ℕ → Prop := fun k => ∃ c : ℕ → V, IsCube G k c ∧ (∀ i < k, ∀ j < s, c i ≠ f j) ∧
    s + 2 ≤ dseg G (c 0) f 0 s + dseg G (c 1) f 0 s
  have hCPB2 : CPB 2 := by
    refine ⟨fun i => if i = 0 then x else y, ⟨fun i j hij hj3 hj => ?_, fun i j hi hj h => ?_⟩,
      fun i hi j hj => ?_, by simp; omega⟩
    · have : i = 0 ∧ j = 1 := by omega
      obtain ⟨rfl, rfl⟩ := this
      simpa using hxy
    · by_contra hne
      have : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp at h; exact hxy.ne h
      · simp at h; exact hxy.ne h.symm
    · show (if i = 0 then x else y) ≠ f j
      split_ifs
      · exact fun h => hx j hj h.symm
      · exact fun h => hy j hj h.symm
  have hn2 : 2 ≤ Fintype.card V := by
    obtain ⟨c, hc, -⟩ := hCPB2; exact hc.le_card
  set p := Nat.findGreatest CPB (Fintype.card V) with hp
  obtain ⟨c, hc, hcS, hB0⟩ : CPB p := Nat.findGreatest_spec hn2 hCPB2
  have hp2 : 2 ≤ p := Nat.le_findGreatest hn2 hCPB2
  have hmaxB : ∀ c' : ℕ → V, IsCube G (p + 1) c' → (∀ i < p + 1, ∀ j < s, c' i ≠ f j) →
      s + 2 ≤ dseg G (c' 0) f 0 s + dseg G (c' 1) f 0 s → False := fun c' h1 h2 h3 =>
    Nat.findGreatest_is_greatest (P := CPB) (n := Fintype.card V) (k := p + 1) (by omega)
      h1.le_card ⟨c', h1, h2, h3⟩
  have hmax0 : ∀ c' : ℕ → V, IsCube G (p + 1) c' → (∀ i < p + 1, ∀ j < s, c' i ≠ f j) →
      c' 0 = c 0 → c' 1 = c 1 → False := fun c' h1 h2 e0 e1 =>
    hmaxB c' h1 h2 (by rw [e0, e1]; exact hB0)
  have hnext := nonext_of_max hc hp2 hcS hmax0
  set n := Fintype.card V with hn
  have hSinj := hS.1.inj
  set Sf := (range s).image f with hSf
  have hSc : Sf.card = s := card_image_range hSinj
  have hnotS : ∀ i < p, ∀ j < s, f j ≠ c i := fun i hi j hj h => hcS i hi j hj h.symm
  have hst01 : StartsAt G s f p (c 0) (c 1) := ⟨c, hc.isSq, rfl, rfl, hcS⟩
  have hst10 : StartsAt G s f p (c 1) (c 0) := by
    refine ⟨_, lemma7_swap01 hc hp2, by simp, by simp, fun i hi j hj => ?_⟩
    split_ifs <;> exact hcS _ (by omega) j hj
  -- `p ≥ 3`
  have hp3 : 3 ≤ p := by
    by_contra hlt
    have hp' : p = 2 := by omega
    have L4a := lemma4 hS (x := c 0) (hnotS 0 (by omega))
    have L4b := lemma4 hS (x := c 1) (hnotS 1 (by omega))
    have da := deg_split (G := G) (c 0) Sf ∅ (disjoint_empty_right _)
    have db := deg_split (G := G) (c 1) Sf ∅ (disjoint_empty_right _)
    simp only [filter_empty, card_empty, add_zero, union_empty] at da db
    rw [← dseg_eq_card_image hSinj] at da db
    have ha := hdeg (c 0) (hnotS 0 (by omega))
    have hb := hdeg (c 1) (hnotS 1 (by omega))
    have hnc : ∀ z ∈ univ \ Sf, ¬ (G.Adj (c 0) z ∧ G.Adj (c 1) z) := by
      intro z hz hzz
      simp only [mem_sdiff, mem_univ, true_and, hSf, mem_image, mem_range, not_exists, not_and]
        at hz
      apply hnext z (fun j hj => hz j hj) (fun i hi h => by
        have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl
        · exact G.loopless.irrefl _ (h ▸ hzz.1)
        · exact G.loopless.irrefl _ (h ▸ hzz.2))
      rw [hp']
      exact ⟨hzz.2, hzz.1, fun h => by omega⟩
    have hunion := card_union_add_card_inter ((univ \ Sf).filter (G.Adj (c 0)))
      ((univ \ Sf).filter (G.Adj (c 1)))
    have hinter : ((univ \ Sf).filter (G.Adj (c 0)) ∩ (univ \ Sf).filter (G.Adj (c 1))) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro z hz
      simp only [mem_inter, mem_filter] at hz
      exact hnc z hz.1.1 ⟨hz.1.2, hz.2.2⟩
    rw [hinter, card_empty, add_zero] at hunion
    have hsub : (univ \ Sf).filter (G.Adj (c 0)) ∪ (univ \ Sf).filter (G.Adj (c 1)) ⊆ univ \ Sf := by
      intro z hz
      simp only [mem_union, mem_filter] at hz
      rcases hz with h | h <;> exact h.1
    have := card_le_card hsub
    rw [card_univ_sdiff, hSc] at this
    have hcard : s + p ≤ n := by
      have hdisj : Disjoint Sf ((range p).image c) := by
        rw [disjoint_left]
        intro w hw hw'
        simp only [hSf, mem_image, mem_range] at hw hw'
        obtain ⟨j, hj, rfl⟩ := hw
        obtain ⟨i, hi, hci⟩ := hw'
        exact hcS i hi j hj hci
      have := card_le_univ (Sf ∪ (range p).image c)
      rw [card_union_of_disjoint hdisj, hSc, card_image_range hc.inj] at this
      exact this
    omega
  -- `s ≥ 2p + 2`, else Lemma 8
  have hsp : 2 * p + 2 ≤ s := by
    by_contra hsp
    push Not at hsp
    have hsum01 := dseg_pair_eq_sum (G := G) (c 0) (c 1) f 0 s
    rw [zero_add, ← range_eq_Ico] at hsum01
    have h8 := lemma8_count (cnt2 G (c 0) (c 1) f) (cnt2_le _ _ f) s
      (fun i hi h => lemma9_left hS hp2 hst01 hst10 (i := i) (by omega) (by omega) h)
      (fun i hi1 hi2 h => lemma9_right hS hp2 hst01 hst10 (i := i) (by omega) (by omega) hi2 h)
    omega
  -- `p ≥ 4` by Lemma 6
  obtain ⟨hT, -, -, -⟩ := lemma28x hS hdeg hc hp3 hcS hsp hnext
  have hp4 : 4 ≤ p := by
    by_contra hlt
    have L6 := lemma6 hS (x1 := c (p - 3)) (x2 := c (p - 2)) (x3 := c (p - 1))
      (hc.adj _ _ (by omega) (by omega) (by omega)) (hc.adj _ _ (by omega) (by omega) (by omega))
      (hc.adj _ _ (by omega) (by omega) (by omega)) (hnotS _ (by omega)) (hnotS _ (by omega))
      (hnotS _ (by omega))
    omega
  have hcomp := complete_of_max hS hdeg hc hp4 hcS hsp hmax0
  have hcov := lemma29x hS hdeg hc hp4 hcS hsp hcomp hB0 hmaxB
  exact lemmaFC hS hdeg hn3 hc hp4 hcS hsp hcomp hcov

end L10x

section EndGameX

variable [Fintype V] {s h : ℕ} {f : ℕ → V}

lemma endgameX (hS : Opt G s f) (hn : Fintype.card V = s + h) (hh : 1 ≤ h)
    (hδ : ∀ v, 2 * (s + h) ≤ 3 * G.degree v + 1)
    (hHam : ∀ x y, (∀ i < s, f i ≠ x) → (∀ i < s, f i ≠ y) → G.Adj x y →
      ∃ P, IsSq G h P ∧ P 0 = x ∧ P 1 = y ∧ ∀ i < h, ∀ j < s, P i ≠ f j)
    (h35 : ∀ x, (∀ i < s, f i ≠ x) → ∀ i < s, G.Adj x (f i) →
      ∃ y, (∀ i < s, f i ≠ y) ∧ G.Adj x y ∧ G.Adj y (f i))
    (h36 : ∀ x, (∀ i < s, f i ≠ x) → ∀ i, i + 1 < s → ¬ (G.Adj x (f i) ∧ G.Adj x (f (i + 1))))
    (h34 : 3 * s + 1 ≤ 2 * (s + h)) (h37 : h + 1 ≤ s)
    {t t' : ℕ} (htt : t ≤ t') (hsum : 3 * t + 3 * t' ≤ s)
    (hgood1 : ∀ i < t, Good G s f (3 * i)) (hgood2 : ∀ i < t', Good G s f (s - 3 - 3 * i))
    (hnext : 3 * t + 3 * t' + 3 ≤ s → ¬ Good G s f (3 * t)) : False := by
  classical
  have hSinj := hS.1.inj
  set Sset := (range s).image f with hSset
  have hSc : Sset.card = s := card_image_range hSinj
  have hHc : (univ \ Sset).card = h := by rw [card_univ_sdiff, hSc, hn]; omega
  have hnotS_of : ∀ z ∈ univ \ Sset, ∀ i < s, f i ≠ z := by
    intro z hz i hi h'
    simp only [mem_sdiff, mem_univ, true_and] at hz
    exact hz (h' ▸ mem_image_of_mem f (mem_range.2 hi))
  -- vertices outside `S` have at most `h - 1` neighbours outside `S`
  have hout : ∀ v, (∀ i < s, f i ≠ v) → ((univ \ Sset).filter (G.Adj v)).card + 1 ≤ h := by
    intro v hv
    have hvm : v ∈ univ \ Sset := by
      simp only [mem_sdiff, mem_univ, true_and, hSset, mem_image, mem_range, not_exists, not_and]
      exact fun i hi => hv i hi
    have := card_filter_adj_self_le (G := G) hvm
    rwa [hHc] at this
  -- Step 1: counting at a vertex outside `S`
  obtain ⟨v0, hv0⟩ : ∃ v, v ∈ univ \ Sset := by
    by_contra hne
    push Not at hne
    have : univ \ Sset = ∅ := eq_empty_of_forall_notMem hne
    rw [this, card_empty] at hHc
    omega
  have hv0S := hnotS_of v0 hv0
  set r := s - 3 * t - 3 * t' with hr
  have hd1 := good_triples_bound (G := G) hv0S 0 t (fun i hi => by simpa using hgood1 i hi)
  have hd3 := good_triples_bound (G := G) hv0S (s - 3 * t') t' (fun k hk => by
    have := hgood2 (t' - 1 - k) (by omega)
    rwa [show s - 3 - 3 * (t' - 1 - k) = s - 3 * t' + 3 * k by omega] at this)
  have hd2 := no_consec_bound (G := G) v0 f r (3 * t) (fun i h1 h2 => h36 v0 hv0S i (by omega))
  have hsplit1 := dseg_add (G := G) v0 f 0 (3 * t) (r + 3 * t')
  have hsplit2 := dseg_add (G := G) v0 f (0 + 3 * t) r (3 * t')
  rw [show 3 * t + (r + 3 * t') = s by omega] at hsplit1
  rw [show 0 + 3 * t + r = s - 3 * t' by omega] at hsplit2
  simp only [Nat.zero_add] at hsplit1 hsplit2
  have hdeg0 : G.degree v0 = dseg G v0 f 0 s + ((univ \ Sset).filter (G.Adj v0)).card :=
    deg_eq_dseg_add (G := G) hSinj v0
  have hδ0 := hδ v0
  have ho0 := hout v0 hv0S
  have hr5 : 3 ≤ r := by omega
  have h2h : s + 6 * t + 1 ≤ 2 * h := by omega
  -- Step 2: the triple at `a = 3t` is not good
  set a := 3 * t with ha
  have hng := hnext (by omega)
  unfold Good at hng
  push Not at hng
  obtain ⟨x, hxS, hx2⟩ := hng
  have e1 := dseg_add (G := G) x f a 1 2
  have e2 := dseg_add (G := G) x f (a + 1) 1 1
  rw [dseg_one, show 1 + 2 = 3 by rfl] at e1
  rw [dseg_one, dseg_one, show 1 + 1 = 2 by rfl, show a + 1 + 1 = a + 2 by omega] at e2
  have nx01 := h36 x hxS a (by omega)
  have nx12 := h36 x hxS (a + 1) (by omega)
  rw [show a + 1 + 1 = a + 2 by omega] at nx12
  have hxa : G.Adj x (f a) ∧ G.Adj x (f (a + 2)) := by
    by_cases h1 : G.Adj x (f (a + 1))
    · have h0 : ¬ G.Adj x (f a) := fun h0 => nx01 ⟨h0, h1⟩
      have h2 : ¬ G.Adj x (f (a + 2)) := fun h2 => nx12 ⟨h1, h2⟩
      rw [if_neg h0] at e1
      rw [if_pos h1, if_neg h2] at e2
      omega
    · rw [if_neg h1] at e2
      by_cases h0 : G.Adj x (f a) <;> by_cases h2 : G.Adj x (f (a + 2))
      · exact ⟨h0, h2⟩
      · rw [if_neg h2] at e2; rw [if_pos h0] at e1; omega
      · rw [if_pos h2] at e2; rw [if_neg h0] at e1; omega
      · rw [if_neg h2] at e2; rw [if_neg h0] at e1; omega
  obtain ⟨y, hyS, hxy, hyf⟩ := h35 x hxS (a + 2) (by omega) hxa.2
  obtain ⟨P, hP, hP0, hP1, hPS⟩ := hHam x y hxS hyS hxy
  -- the path `X = f (a+1), f a, f (a+2), P`
  let T : ℕ → V := fun i => f (if i = 0 then a + 1 else if i = 1 then a else a + 2)
  have hT : IsSq G 3 T := hS.1.isSq_comp_close (fun i => if i = 0 then a + 1 else if i = 1 then a else a + 2)
    (fun i hi => by split_ifs <;> omega) (fun i j hi hj hh => by split_ifs at hh <;> omega)
    (fun i j hij hj2 hj => by split_ifs <;> omega)
  have hX : IsSq G (3 + h) (cat 3 T P) := isSq_cat hT hP
    (fun i hi j hj he => hPS j hj _ (show (if i = 0 then a + 1 else if i = 1 then a else a + 2) < s
      by split_ifs <;> omega) he.symm)
    (fun _ _ => by simpa [T, hP0] using hxa.2.symm)
    (fun _ _ => by simpa [T, hP0] using hxa.1.symm)
    (fun _ _ => by simpa [T, hP1] using hyf.symm)
  set X := cat 3 T P with hXdef
  have hX0 : X 0 = f (a + 1) := by simp [hXdef, cat, T]
  have hX1 : X 1 = f a := by simp [hXdef, cat, T]
  have hXS : ∀ j < 3 + h, ∀ k < s, (k < a ∨ a + 3 ≤ k) → X j ≠ f k := by
    intro j hj k hk hka he
    simp only [hXdef, cat] at he
    split_ifs at he with hj3
    · simp only [T] at he
      have := hSinj _ _ (by split_ifs <;> omega) hk he
      split_ifs at this <;> omega
    · exact hPS _ (by omega) k hk he
  -- (3.12): no consecutive pair of `L` is joined to both `f a` and `f (a+1)`
  have hno4 : ∀ i, a + 3 ≤ i → i + 1 < s → ¬ (G.Adj (f a) (f i) ∧ G.Adj (f a) (f (i + 1)) ∧
      G.Adj (f (a + 1)) (f i) ∧ G.Adj (f (a + 1)) (f (i + 1))) := by
    intro i hi1 hi2 ⟨k1, k2, k3, k4⟩
    have hQ1 := hS.1.revSuffix i
    have c1 := isSq_cat hQ1 hX (fun j hj k hk he => hXS k hk (s - 1 - j) (by omega) (Or.inr (by omega))
        he.symm)
      (fun _ _ => by rw [hX0, show s - 1 - (s - i - 1) = i by omega]; exact k3.symm)
      (fun _ _ => by rw [hX0, show s - 1 - (s - i - 2) = i + 1 by omega]; exact k4.symm)
      (fun _ _ => by rw [hX1, show s - 1 - (s - i - 1) = i by omega]; exact k1.symm)
    have l1 := (hS.2 _ _ c1).1
    have hQ2 := (hS.1.shift (a + 3)).take (m := i - a - 1) (by omega)
    have c2 := isSq_cat hQ2 hX (fun j hj k hk he => hXS k hk (a + 3 + j) (by omega)
        (Or.inr (by omega)) he.symm)
      (fun _ _ => by
        rw [hX0, show a + 3 + (i - a - 1 - 1) = i + 1 by omega]; exact k4.symm)
      (fun _ _ => by
        rw [hX0, show a + 3 + (i - a - 1 - 2) = i by omega]; exact k3.symm)
      (fun _ _ => by
        rw [hX1, show a + 3 + (i - a - 1 - 1) = i + 1 by omega]; exact k2.symm)
    have l2 := (hS.2 _ _ c2).1
    omega
  have hXlen : 3 + h ≤ s := (hS.2 _ _ hX).1
  have hl6 : a + 6 ≤ s := by omega
  -- (3.13)
  obtain ⟨z, hzS, hxz, hzf⟩ := h35 x hxS a (by omega) hxa.1
  obtain ⟨P', hP', hP'0, hP'1, hP'S⟩ := hHam x z hxS hzS hxz
  have n313a : ¬ G.Adj (f a) (f (a + 3)) := by
    intro hq
    have hτ := tailSq hS.1 [a + 2, a] (by simp; omega) (by simp) (by
      intro i j hij hj2 hj; simp at hj; interval_cases j <;> interval_cases i; simp [pv]; omega)
    have := assemble2 hS (m := a + 3) (by omega) hτ (by simp) (by
        intro i hi; simp at hi; interval_cases i <;> simp [pv]) hP' (by omega) hP'S
      (show G.Adj (f (a + 3)) (f (a + 2)) from (hS.1.adj1 (a + 2) (by omega)).symm)
      (show G.Adj (f (a + 4)) (f (a + 2)) from (hS.1.adj2 (a + 2) (by omega)).symm)
      (show G.Adj (f (a + 3)) (f a) from hq.symm)
      (show G.Adj (f a) (P' 0) by rw [hP'0]; exact hxa.1.symm)
      (show G.Adj (f (a + 2)) (P' 0) by rw [hP'0]; exact hxa.2.symm)
      (show G.Adj (f a) (P' 1) by rw [hP'1]; exact hzf.symm)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have n313b : ¬ G.Adj (f (a + 1)) (f (a + 4)) := by
    intro hq
    have hτ := tailSq hS.1 [a + 1, a + 2, a] (by simp; omega) (by simp) (by
      intro i j hij hj2 hj; simp at hj; interval_cases j <;> interval_cases i <;> simp [pv] <;> omega)
    have := assemble2 hS (m := a + 3) (by omega) hτ (by simp) (by
        intro i hi; simp at hi; interval_cases i <;> simp [pv]) hP' (by omega) hP'S
      (show G.Adj (f (a + 3)) (f (a + 1)) from (hS.1.adj2 (a + 1) (by omega)).symm)
      (show G.Adj (f (a + 4)) (f (a + 1)) from hq.symm)
      (show G.Adj (f (a + 3)) (f (a + 2)) from (hS.1.adj1 (a + 2) (by omega)).symm)
      (show G.Adj (f a) (P' 0) by rw [hP'0]; exact hxa.1.symm)
      (show G.Adj (f (a + 2)) (P' 0) by rw [hP'0]; exact hxa.2.symm)
      (show G.Adj (f a) (P' 1) by rw [hP'1]; exact hzf.symm)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have n313c : ¬ (G.Adj (f a) (f (a + 4)) ∧ G.Adj (f a) (f (a + 5))) := by
    intro ⟨hq1, hq2⟩
    have hτ := tailSq hS.1 [a, a + 2] (by simp; omega) (by simp) (by
      intro i j hij hj2 hj; simp at hj; interval_cases j <;> interval_cases i; simp [pv]; omega)
    have := assemble2 hS (m := a + 4) (by omega) hτ (by simp) (by
        intro i hi; simp at hi; interval_cases i <;> simp [pv]) hP (by omega) hPS
      (show G.Adj (f (a + 4)) (f a) from hq1.symm)
      (show G.Adj (f (a + 5)) (f a) from hq2.symm)
      (show G.Adj (f (a + 4)) (f (a + 2)) from (hS.1.adj2 (a + 2) (by omega)).symm)
      (show G.Adj (f (a + 2)) (P 0) by rw [hP0]; exact hxa.2.symm)
      (show G.Adj (f a) (P 0) by rw [hP0]; exact hxa.1.symm)
      (show G.Adj (f (a + 2)) (P 1) by rw [hP1]; exact hyf.symm)
    simp only [List.length_cons, List.length_nil] at this
    omega
  -- Step 3: counting at the edge `e = f a f (a+1)`
  set l := s - a - 3 with hl
  have hcle : ∀ j, cnt2 G (f a) (f (a + 1)) f j ≤ 2 := cnt2_le (f a) (f (a + 1)) f
  have hsumS := dseg_pair_eq_sum (G := G) (f a) (f (a + 1)) f 0 s
  rw [zero_add, ← sum_Ico_consecutive _ (show 0 ≤ a by omega) (show a ≤ s by omega),
    ← sum_Ico_consecutive _ (show a ≤ a + 3 by omega) (show a + 3 ≤ s by omega)] at hsumS
  have hT3 : ∑ j ∈ Ico a (a + 3), cnt2 G (f a) (f (a + 1)) f j ≤ 4 := by
    rw [sum_Ico_eq_sum_range, show a + 3 - a = 3 by omega]
    simp only [sum_range_succ, sum_range_zero, zero_add, add_zero]
    have c0 : cnt2 G (f a) (f (a + 1)) f a ≤ 1 := by
      unfold cnt2; rw [bi_neg (G.irrefl (v := f a))]; have := bi_le_one (G.Adj (f (a + 1)) (f a))
      omega
    have c1 : cnt2 G (f a) (f (a + 1)) f (a + 1) ≤ 1 := by
      unfold cnt2; rw [bi_neg (G.irrefl (v := f (a + 1)))]
      have := bi_le_one (G.Adj (f a) (f (a + 1))); omega
    have c2 := hcle (a + 2)
    omega
  have hL3 : 2 * ∑ j ∈ Ico (a + 3) s, cnt2 G (f a) (f (a + 1)) f j + 2 ≤ 3 * l := by
    have hpb := pair_bound (cnt2 G (f a) (f (a + 1)) f) hcle (l - 3) (a + 6) (fun i h1 h2 => by
      by_contra hc
      have hi2 : cnt2 G (f a) (f (a + 1)) f i = 2 := by have := hcle i; have := hcle (i + 1); omega
      have hi3 : cnt2 G (f a) (f (a + 1)) f (i + 1) = 2 := by
        have := hcle i; have := hcle (i + 1); omega
      obtain ⟨k1, k3⟩ := cnt2_two hi2
      obtain ⟨k2, k4⟩ := cnt2_two hi3
      exact hno4 i (by omega) (by omega) ⟨k1, k2, k3, k4⟩)
    rw [show a + 6 + (l - 3) = s by omega] at hpb
    rw [← sum_Ico_consecutive _ (show a + 3 ≤ a + 6 by omega) (show a + 6 ≤ s by omega)]
    have h3 : ∑ j ∈ Ico (a + 3) (a + 6), cnt2 G (f a) (f (a + 1)) f j ≤ 3 := by
      rw [sum_Ico_eq_sum_range, show a + 6 - (a + 3) = 3 by omega]
      simp only [sum_range_succ, sum_range_zero, zero_add, add_zero]
      rw [show a + 3 + 1 = a + 4 by omega, show a + 3 + 2 = a + 5 by omega]
      unfold cnt2
      rw [bi_neg n313a, bi_neg n313b]
      have := bi_le_one (G.Adj (f (a + 1)) (f (a + 3)))
      have := bi_le_one (G.Adj (f (a + 1)) (f (a + 5)))
      have := bi_le_one (G.Adj (f a) (f (a + 4)))
      have := bi_le_one (G.Adj (f a) (f (a + 5)))
      by_cases q4 : G.Adj (f a) (f (a + 4))
      · rw [bi_neg (fun q5 => n313c ⟨q4, q5⟩)]; omega
      · rw [bi_neg q4]; omega
    omega
  have hHe : ((univ \ Sset).filter (G.Adj (f a))).card +
      ((univ \ Sset).filter (G.Adj (f (a + 1)))).card ≤ h := by
    rw [card_filter_eq_sum_bi, card_filter_eq_sum_bi, ← sum_add_distrib, ← hHc, card_eq_sum_ones]
    apply sum_le_sum
    intro z hz
    have hn36 := h36 z (hnotS_of z hz) a (by omega)
    by_cases h0 : G.Adj (f a) z
    · rw [bi_pos h0, bi_neg (show ¬ G.Adj (f (a + 1)) z from fun h1 => hn36 ⟨h0.symm, h1.symm⟩)]
    · rw [bi_neg h0]; have := bi_le_one (G.Adj (f (a + 1)) z); omega
  have dfa : G.degree (f a) = dseg G (f a) f 0 s + ((univ \ Sset).filter (G.Adj (f a))).card :=
    deg_eq_dseg_add (G := G) hSinj (f a)
  have dfa1 : G.degree (f (a + 1)) =
      dseg G (f (a + 1)) f 0 s + ((univ \ Sset).filter (G.Adj (f (a + 1)))).card :=
    deg_eq_dseg_add (G := G) hSinj (f (a + 1))
  have hδa := hδ (f a)
  have hδa1 := hδ (f (a + 1))
  -- hence a consecutive pair of `M` joined to both `f a` and `f (a+1)`
  have hMle : ∑ i ∈ Ico 0 a, cnt2 G (f a) (f (a + 1)) f i ≤ 2 * a := by
    calc _ ≤ (Ico 0 a).card • 2 := sum_le_card_nsmul _ _ 2 (fun i _ => hcle i)
      _ = 2 * a := by simp [mul_comm]
  have hD2 : G.degree (f a) + G.degree (f (a + 1)) ≤
      ∑ i ∈ Ico 0 a, cnt2 G (f a) (f (a + 1)) f i + 4 +
        ∑ i ∈ Ico (a + 3) s, cnt2 G (f a) (f (a + 1)) f i + h := by omega
  have e1 : 4 * (s + h) ≤ 3 * (∑ i ∈ Ico 0 a, cnt2 G (f a) (f (a + 1)) f i + 4 +
        ∑ i ∈ Ico (a + 3) s, cnt2 G (f a) (f (a + 1)) f i + h) + 2 := by omega
  have h2a : 2 * a + 3 ≤ s := by omega
  have ha6 : 6 ≤ a := by
    have hl' : l + a + 3 = s := by omega
    clear_value a l
    generalize ∑ i ∈ Ico 0 a, cnt2 G (f a) (f (a + 1)) f i = SM at e1 hMle
    generalize ∑ i ∈ Ico (a + 3) s, cnt2 G (f a) (f (a + 1)) f i = SL at e1 hL3
    omega
  -- hence a consecutive pair of `M` joined to both `f a` and `f (a+1)`
  obtain ⟨i, hia, hi4⟩ : ∃ i, i + 1 < a ∧
      4 ≤ cnt2 G (f a) (f (a + 1)) f i + cnt2 G (f a) (f (a + 1)) f (i + 1) := by
    by_contra hc
    push Not at hc
    have hM := pair_bound (cnt2 G (f a) (f (a + 1)) f) hcle a 0 (fun i _ h2 => by
      have := hc i (by omega); omega)
    rw [zero_add] at hM
    have hl' : l + a + 3 = s := by omega
    clear_value a l
    generalize ∑ i ∈ Ico 0 a, cnt2 G (f a) (f (a + 1)) f i = SM at e1 hM
    generalize ∑ i ∈ Ico (a + 3) s, cnt2 G (f a) (f (a + 1)) f i = SL at e1 hL3
    omega
  have hci : cnt2 G (f a) (f (a + 1)) f i = 2 := by
    have := hcle i; have := hcle (i + 1); omega
  have hci1 : cnt2 G (f a) (f (a + 1)) f (i + 1) = 2 := by
    have := hcle i; have := hcle (i + 1); omega
  obtain ⟨m1, m3⟩ := cnt2_two hci
  obtain ⟨m2, m4⟩ := cnt2_two hci1
  -- Step 4: the paths `W = f i, f (i+1), X` and `W' = f (i+1), f i, X`
  have hW2 : IsSq G 2 (fun k => f (i + k)) := (hS.1.shift i).take (by omega)
  have hW2' : IsSq G 2 (fun k => f (i + 1 - k)) := by
    refine isSq_of_pairs _ (fun k k' hkk hk2 hk => ?_) (fun k k' hk hk' hh => ?_)
    · have : k = 0 ∧ k' = 1 := by omega
      obtain ⟨rfl, rfl⟩ := this
      simpa using (hS.1.adj1 i (by omega)).symm
    · have := hSinj _ _ (by omega) (by omega) hh; omega
  have hW := isSq_cat hW2 hX (fun k hk j hj he => hXS j hj (i + k) (by omega) (Or.inl (by omega)) he.symm)
    (fun _ _ => by rw [hX0, show i + (2 - 1) = i + 1 by omega]; exact m4.symm)
    (fun _ _ => by rw [hX0, show i + (2 - 2) = i by omega]; exact m3.symm)
    (fun _ _ => by rw [hX1, show i + (2 - 1) = i + 1 by omega]; exact m2.symm)
  have hW' := isSq_cat hW2' hX (fun k hk j hj he => hXS j hj (i + 1 - k) (by omega) (Or.inl (by omega))
      he.symm)
    (fun _ _ => by rw [hX0, show i + 1 - (2 - 1) = i by omega]; exact m3.symm)
    (fun _ _ => by rw [hX0, show i + 1 - (2 - 2) = i + 1 by omega]; exact m4.symm)
    (fun _ _ => by rw [hX1, show i + 1 - (2 - 1) = i by omega]; exact m1.symm)
  set W := cat 2 (fun k => f (i + k)) X with hWdef
  set W' := cat 2 (fun k => f (i + 1 - k)) X with hW'def
  have hW0 : W 0 = f i := by simp [hWdef, cat]
  have hW1 : W 1 = f (i + 1) := by simp [hWdef, cat]
  have hW'0 : W' 0 = f (i + 1) := by simp [hW'def, cat]
  have hW'1 : W' 1 = f i := by simp [hW'def, cat]
  have hWS : ∀ j < 2 + (3 + h), ∀ k < s, a + 3 ≤ k → W j ≠ f k := by
    intro j hj k hk hka he
    simp only [hWdef, cat] at he
    split_ifs at he with hj2
    · have := hSinj _ _ (by omega) hk he; omega
    · exact hXS _ (by omega) k hk (Or.inr hka) he
  have hW'S : ∀ j < 2 + (3 + h), ∀ k < s, a + 3 ≤ k → W' j ≠ f k := by
    intro j hj k hk hka he
    simp only [hW'def, cat] at he
    split_ifs at he with hj2
    · have := hSinj _ _ (by omega) hk he; omega
    · exact hXS _ (by omega) k hk (Or.inr hka) he
  -- Lemma 8 for the pair `f i, f (i+1)` along `L`
  have h8 := lemma8_count (cnt2 G (f i) (f (i + 1)) (fun j => f (a + 3 + j)))
    (cnt2_le _ _ _) l
    (fun j hj h2 => by
      obtain ⟨p1, p2⟩ := cnt2_two h2
      have hQ := hS.1.revSuffix (a + 3 + j)
      apply cnt2_zero
      · intro hq
        have c := isSq_cat hQ hW (fun k hk j' hj' he => hWS j' hj' (s - 1 - k) (by omega) (by omega) he.symm)
          (fun _ _ => by rw [hW0, show s - 1 - (s - (a + 3 + j) - 1) = a + 3 + j by omega]; exact p1.symm)
          (fun _ _ => by
            rw [hW0, show s - 1 - (s - (a + 3 + j) - 2) = a + 3 + (j + 1) by omega]; exact hq.symm)
          (fun _ _ => by rw [hW1, show s - 1 - (s - (a + 3 + j) - 1) = a + 3 + j by omega]; exact p2.symm)
        have := (hS.2 _ _ c).1
        clear_value a l
        omega
      · intro hq
        have c := isSq_cat hQ hW' (fun k hk j' hj' he => hW'S j' hj' (s - 1 - k) (by omega) (by omega) he.symm)
          (fun _ _ => by rw [hW'0, show s - 1 - (s - (a + 3 + j) - 1) = a + 3 + j by omega]; exact p2.symm)
          (fun _ _ => by
            rw [hW'0, show s - 1 - (s - (a + 3 + j) - 2) = a + 3 + (j + 1) by omega]; exact hq.symm)
          (fun _ _ => by rw [hW'1, show s - 1 - (s - (a + 3 + j) - 1) = a + 3 + j by omega]; exact p1.symm)
        have := (hS.2 _ _ c).1
        clear_value a l
        omega)
    (fun j hj1 hj2 h2 => by
      obtain ⟨p1, p2⟩ := cnt2_two h2
      have hQ := (hS.1.shift (a + 3)).take (m := j + 1) (by omega)
      apply cnt2_zero
      · intro hq
        have c := isSq_cat hQ hW (fun k hk j' hj' he => hWS j' hj' (a + 3 + k) (by omega) (by omega) he.symm)
          (fun _ _ => by rw [hW0, show j + 1 - 1 = j by omega]; exact p1.symm)
          (fun _ _ => by rw [hW0, show a + 3 + (j + 1 - 2) = a + 3 + (j - 1) by omega]; exact hq.symm)
          (fun _ _ => by rw [hW1, show j + 1 - 1 = j by omega]; exact p2.symm)
        have := (hS.2 _ _ c).1
        clear_value a l
        omega
      · intro hq
        have c := isSq_cat hQ hW' (fun k hk j' hj' he => hW'S j' hj' (a + 3 + k) (by omega) (by omega) he.symm)
          (fun _ _ => by rw [hW'0, show j + 1 - 1 = j by omega]; exact p2.symm)
          (fun _ _ => by rw [hW'0, show a + 3 + (j + 1 - 2) = a + 3 + (j - 1) by omega]; exact hq.symm)
          (fun _ _ => by rw [hW'1, show j + 1 - 1 = j by omega]; exact p1.symm)
        have := (hS.2 _ _ c).1
        clear_value a l
        omega)
  -- Step 5: degree count for `f i, f (i+1)`
  have hsumI := dseg_pair_eq_sum (G := G) (f i) (f (i + 1)) f 0 s
  rw [zero_add, ← sum_Ico_consecutive _ (show 0 ≤ a by omega) (show a ≤ s by omega),
    ← sum_Ico_consecutive _ (show a ≤ a + 3 by omega) (show a + 3 ≤ s by omega)] at hsumI
  have hLI : ∑ j ∈ Ico (a + 3) s, cnt2 G (f i) (f (i + 1)) f j =
      ∑ j ∈ range l, cnt2 G (f i) (f (i + 1)) (fun j => f (a + 3 + j)) j := by
    rw [sum_Ico_eq_sum_range, show s - (a + 3) = l by omega]
    rfl
  have hMI := dseg_pair_eq_sum (G := G) (f i) (f (i + 1)) f 0 a
  rw [zero_add] at hMI
  have hTI := dseg_pair_eq_sum (G := G) (f i) (f (i + 1)) f a 3
  have hMi := dseg_add_card_le (G := G) (f i) f 0 a {i} (by
    intro k hk; rw [mem_singleton] at hk; subst hk; simp only [mem_Ico]; omega)
    (fun k hk => by rw [mem_singleton] at hk; subst hk; exact G.irrefl)
  have hMi1 := dseg_add_card_le (G := G) (f (i + 1)) f 0 a {i + 1} (by
    intro k hk; rw [mem_singleton] at hk; subst hk; simp only [mem_Ico]; omega)
    (fun k hk => by rw [mem_singleton] at hk; subst hk; exact G.irrefl)
  rw [card_singleton] at hMi hMi1
  have hTi := dseg_le (G := G) (f i) f a 3
  have hTi1 := dseg_le (G := G) (f (i + 1)) f a 3
  have hHI : ((univ \ Sset).filter (G.Adj (f i))).card +
      ((univ \ Sset).filter (G.Adj (f (i + 1)))).card ≤ h := by
    rw [card_filter_eq_sum_bi, card_filter_eq_sum_bi, ← sum_add_distrib, ← hHc, card_eq_sum_ones]
    apply sum_le_sum
    intro z hz
    have hn36 := h36 z (hnotS_of z hz) i (by omega)
    by_cases h0 : G.Adj (f i) z
    · rw [bi_pos h0, bi_neg (show ¬ G.Adj (f (i + 1)) z from fun h1 => hn36 ⟨h0.symm, h1.symm⟩)]
    · rw [bi_neg h0]; have := bi_le_one (G.Adj (f (i + 1)) z); omega
  have dfi : G.degree (f i) = dseg G (f i) f 0 s + ((univ \ Sset).filter (G.Adj (f i))).card :=
    deg_eq_dseg_add (G := G) hSinj (f i)
  have dfi1 : G.degree (f (i + 1)) =
      dseg G (f (i + 1)) f 0 s + ((univ \ Sset).filter (G.Adj (f (i + 1)))).card :=
    deg_eq_dseg_add (G := G) hSinj (f (i + 1))
  have hδi := hδ (f i)
  have hδi1 := hδ (f (i + 1))
  rw [hLI] at hsumI
  clear_value a l
  generalize ∑ j ∈ range l, cnt2 G (f i) (f (i + 1)) (fun j => f (a + 3 + j)) j = SL at hsumI h8
  generalize ∑ x ∈ Ico 0 a, cnt2 G (f i) (f (i + 1)) f x = SM at hsumI hMI
  generalize ∑ x ∈ Ico a (a + 3), cnt2 G (f i) (f (i + 1)) f x = ST at hsumI hTI
  omega


end EndGameX


section MainStepX

variable [Fintype V]

theorem main_stepX (hδ : ∀ v, 2 * Fintype.card V ≤ 3 * G.degree v + 1) (v0 : V) :
    ∃ f, IsSq G (Fintype.card V) f := by
  classical
  set n := Fintype.card V with hn
  obtain ⟨s, f, hS⟩ := exists_opt (G := G) v0
  have hsn : s ≤ n := hS.1.le_card
  by_cases hs : s = n
  · exact ⟨f, hs ▸ hS.1⟩
  set h := n - s with hhdef
  have hh : 1 ≤ h := by omega
  have hs1 : 1 ≤ s := (hS.2 1 _ (isSq_one v0)).1
  have hSinj := hS.1.inj
  set Sset := (range s).image f with hSset
  have hSc : Sset.card = s := card_image_range hSinj
  have hHc : (univ \ Sset).card = h := by rw [card_univ_sdiff, hSc]
  have memS : ∀ v, v ∈ Sset ↔ ∃ i < s, f i = v := by
    intro v; simp only [hSset, mem_image, mem_range]
  have notS_iff : ∀ v, v ∉ Sset ↔ ∀ i < s, f i ≠ v := by
    intro v; rw [memS]; push Not; rfl
  -- degrees split between `S` and `H`
  have hsplit : ∀ v, G.degree v = dseg G v f 0 s + ((univ \ Sset).filter (G.Adj v)).card :=
    fun v => deg_eq_dseg_add (G := G) hSinj v
  have hHself : ∀ v, v ∉ Sset → ((univ \ Sset).filter (G.Adj v)).card + 1 ≤ h := by
    intro v hv
    have := card_filter_adj_self_le (G := G) (A := univ \ Sset) (v := v) (by simp [hv])
    rwa [hHc] at this
  -- (3.1)
  have h31 : ∀ v, v ∉ Sset → 2 * h ≤ 3 * ((univ \ Sset).filter (G.Adj v)).card := by
    intro v hv
    have := lemma4 hS ((notS_iff v).1 hv)
    have := hsplit v
    have := hδ v
    omega
  -- the graph `H = G - S`
  set W : Set V := {v | v ∉ Sset} with hW
  have hWc : Fintype.card W = h := by
    rw [← hHc, Fintype.card_subtype]; congr 1; ext v; simp [hW]
  have hdegW : ∀ w : W, (G.induce W).degree w = ((univ \ Sset).filter (G.Adj w.1)).card := by
    intro w
    rw [degree_induce]
    congr 1
    ext u
    simp [hW]
  -- the induction hypothesis: `h ≤ s`
  obtain ⟨g, hg⟩ := fk_nat (Fintype.card W) W (G.induce W) rfl (by omega) (fun w => by
    rw [hdegW, hWc]; have := h31 w.1 w.2; omega)
  rw [hWc] at hg
  have hhs : h ≤ s := (hS.2 h _ hg.lift_induce).1
  -- Lemma 10
  have hL10 : ∀ x y, x ∉ Sset → y ∉ Sset → G.Adj x y → dseg G x f 0 s + dseg G y f 0 s ≤ s + 1 :=
    fun x y hx hy hxy => lemma10x hS (fun v hv => hδ v) ((notS_iff x).1 hx) ((notS_iff y).1 hy) hxy
  -- (3.2) and Lemma 11 on `H`
  have h32 : ∀ x y, x ∉ Sset → y ∉ Sset → G.Adj x y →
      5 * (h - 1) ≤ 3 * (((univ \ Sset).filter (G.Adj x)).card +
        ((univ \ Sset).filter (G.Adj y)).card) := by
    intro x y hx hy hxy
    have := hL10 x y hx hy hxy
    have := hsplit x
    have := hsplit y
    have := hδ x
    have := hδ y
    omega
  have hHam : ∀ x y, (∀ i < s, f i ≠ x) → (∀ i < s, f i ≠ y) → G.Adj x y →
      ∃ P, IsSq G h P ∧ P 0 = x ∧ P 1 = y ∧ ∀ i < h, ∀ j < s, P i ≠ f j := by
    intro x y hx hy hxy
    have hx' := (notS_iff x).2 hx
    have hy' := (notS_iff y).2 hy
    obtain ⟨Q, hQ, hQ0, hQ1⟩ := lemma11 (G := G.induce W)
      (fun w => by rw [hdegW, hWc]; have := h31 w.1 w.2; omega)
      (fun a b hab => by rw [hdegW, hdegW, hWc]; exact h32 a.1 b.1 a.2 b.2 hab)
      (a := ⟨x, hx'⟩) (b := ⟨y, hy'⟩) hxy
    rw [hWc] at hQ
    refine ⟨fun i => (Q i).1, hQ.lift_induce, by simp [hQ0], by simp [hQ1], fun i hi j hj he => ?_⟩
    have he' : (Q i).1 = f j := he
    have := (Q i).2
    simp only [hW, Set.mem_ofPred_eq] at this
    exact this (by rw [he']; exact mem_image_of_mem f (mem_range.2 hj))
  -- a neighbour outside `S` for every vertex outside `S`
  have hnbrH : ∀ v, v ∉ Sset → ∃ y, y ∉ Sset ∧ G.Adj v y := by
    intro v hv
    have := h31 v hv
    obtain ⟨y, hy⟩ : ((univ \ Sset).filter (G.Adj v)).Nonempty := by
      rw [← card_pos]; omega
    simp only [mem_filter, mem_sdiff, mem_univ, true_and] at hy
    exact ⟨y, hy.1, hy.2⟩
  obtain ⟨v1, hv1⟩ : ∃ v, v ∉ Sset := by
    by_contra hc
    push Not at hc
    have : univ \ Sset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]; intro v hv; simp [hc v] at hv
    rw [this, card_empty] at hHc
    omega
  -- (3.4)
  have h34 : 3 * s + 1 ≤ 2 * (s + h) := by
    obtain ⟨y, hy, hvy⟩ := hnbrH v1 hv1
    have := hL10 v1 y hv1 hy hvy
    have := hsplit v1
    have := hsplit y
    have := hδ v1
    have := hδ y
    have := hHself v1 hv1
    have := hHself y hy
    omega
  have hh2 : 2 ≤ h := by
    have := h31 v1 hv1
    have := hHself v1 hv1
    omega
  -- (3.5), with the extremal paragraph
  have h35 : ∀ x, (∀ i < s, f i ≠ x) → ∀ i < s, G.Adj x (f i) →
      ∃ y, (∀ i < s, f i ≠ y) ∧ G.Adj x y ∧ G.Adj y (f i) := by
    intro x hx i hi hxi
    have hx' := (notS_iff x).2 hx
    by_contra hcon
    push Not at hcon
    have hsub : G.neighborFinset x ∩ G.neighborFinset (f i) ⊆ (Sset.filter (G.Adj x)).erase (f i) := by
      intro z hz
      simp only [mem_inter, SimpleGraph.mem_neighborFinset] at hz
      refine mem_erase.2 ⟨fun he => G.irrefl (he ▸ hz.2), mem_filter.2 ⟨?_, hz.1⟩⟩
      by_contra hzS
      exact hcon z ((notS_iff z).1 hzS) hz.1 hz.2.symm
    have hcs := card_le_card hsub
    rw [card_erase_of_mem (mem_filter.2 ⟨mem_image_of_mem f (mem_range.2 hi), hxi⟩),
      ← dseg_eq_card_image hSinj] at hcs
    have hun := card_union_add_card_inter (G.neighborFinset x) (G.neighborFinset (f i))
    have hu : (G.neighborFinset x ∪ G.neighborFinset (f i)).card ≤ n := card_le_univ _
    rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hun
    have hdx := hsplit x
    have hδx := hδ x
    have hδi := hδ (f i)
    -- every neighbour `y` of `x` outside `S` gives equality in Lemma 10
    have keyY : ∀ y, y ∉ Sset → G.Adj x y →
        dseg G x f 0 s + dseg G y f 0 s = s + 1 ∧ 3 * dseg G x f 0 s = n + 1 ∧
          3 * G.degree x + 1 = 2 * n := by
      intro y hy hxy
      have := hL10 x y hx' hy hxy
      have := hsplit y
      have := hHself y hy
      have := hδ y
      refine ⟨by omega, by omega, by omega⟩
    obtain ⟨y0, hy0, hxy0⟩ := hnbrH x hx'
    obtain ⟨-, hdxS, hdegx⟩ := keyY y0 hy0 hxy0
    -- the clique `K = x + N_H(x)`
    set K := insert x ((univ \ Sset).filter (G.Adj x)) with hK
    have hKc : K.card = ((univ \ Sset).filter (G.Adj x)).card + 1 := by
      rw [hK, card_insert_of_notMem]
      simp only [mem_filter]
      exact fun h => G.irrefl h.2
    have hKH : ∀ z ∈ K, z ∉ Sset := by
      intro z hz
      rcases mem_insert.1 hz with rfl | hz'
      · exact hx'
      · simp only [mem_filter, mem_sdiff, mem_univ, true_and] at hz'; exact hz'.1
    -- Lemma 8 equality at the middle `M = s / 2`
    set M := s / 2 with hMdef
    have hM : ∀ y, y ∉ Sset → G.Adj x y → cnt2 G x y f M ≠ 1 := by
      intro y hy hxy
      have hy' := (notS_iff y).1 hy
      obtain ⟨P, hP, hP0, hP1, hPS⟩ := hHam x y hx hy' hxy
      obtain ⟨P', hP', hP'0, hP'1, hP'S⟩ := hHam y x hy' hx hxy.symm
      have st1 : StartsAt G s f h x y := ⟨P, hP, hP0, hP1, hPS⟩
      have st2 : StartsAt G s f h y x := ⟨P', hP', hP'0, hP'1, hP'S⟩
      have hsum := dseg_pair_eq_sum (G := G) x y f 0 s
      rw [zero_add, ← range_eq_Ico] at hsum
      refine lemma8_count_eq (cnt2 G x y f) (cnt2_le x y f) s
        (fun j hj h2 => lemma9_left hS hh2 st1 st2 (i := j) (by omega) (by omega) h2)
        (fun j hj1 hj2 h2 => lemma9_right hS hh2 st1 st2 (i := j) (by omega) (by omega) hj2 h2) ?_
      rw [← hsum]
      exact (keyY y hy hxy).1
    have hMs : M < s := by omega
    -- a vertex of `S` without neighbours in `K`
    obtain ⟨u, hus, hu0⟩ : ∃ j < s, ∀ z ∈ K, ¬ G.Adj (f j) z := by
      by_cases hxM : G.Adj x (f M)
      · have hKM : ∀ z ∈ K, G.Adj z (f M) := by
          intro z hz
          rcases mem_insert.1 hz with rfl | hz'
          · exact hxM
          · simp only [mem_filter, mem_sdiff, mem_univ, true_and] at hz'
            have := hM z hz'.1 hz'.2
            unfold cnt2 at this
            rw [bi_pos hxM] at this
            by_contra hzM
            rw [bi_neg hzM] at this
            exact this rfl
        refine ⟨M - 1, by omega, fun z hz hadj => ?_⟩
        obtain ⟨w, hw, hzw⟩ : ∃ w ∈ K, G.Adj z w := by
          rcases mem_insert.1 hz with rfl | hz'
          · exact ⟨y0, mem_insert_of_mem (by simp [hy0, hxy0]), hxy0⟩
          · simp only [mem_filter] at hz'
            exact ⟨x, mem_insert_self _ _, hz'.2.symm⟩
        obtain ⟨P, hP, hP0, hP1, hPS⟩ := hHam z w ((notS_iff z).1 (hKH z hz))
          ((notS_iff w).1 (hKH w hw)) hzw
        have c := isSq_cat (hS.1.take (m := M + 1) (by omega)) hP
          (fun j hj k hk he => hPS k hk j (by omega) he.symm)
          (fun _ _ => by rw [hP0, show M + 1 - 1 = M by omega]; exact (hKM z hz).symm)
          (fun _ _ => by rw [hP0, show M + 1 - 2 = M - 1 by omega]; exact hadj)
          (fun _ _ => by rw [hP1, show M + 1 - 1 = M by omega]; exact (hKM w hw).symm)
        have := (hS.2 _ _ c).1
        omega
      · refine ⟨M, hMs, fun z hz hadj => ?_⟩
        rcases mem_insert.1 hz with rfl | hz'
        · exact hxM hadj.symm
        · simp only [mem_filter, mem_sdiff, mem_univ, true_and] at hz'
          have := hM z hz'.1 hz'.2
          unfold cnt2 at this
          rw [bi_neg hxM, bi_pos hadj.symm] at this
          exact this rfl
    -- its degree is too small
    have hsubu : G.neighborFinset (f u) ⊆ (univ \ K).erase (f u) := by
      intro z hz
      rw [SimpleGraph.mem_neighborFinset] at hz
      refine mem_erase.2 ⟨fun he => G.irrefl (he ▸ hz), mem_sdiff.2 ⟨mem_univ _, fun hzK => hu0 z hzK hz⟩⟩
    have hcu := card_le_card hsubu
    have hfuK : f u ∉ K := fun h => hKH _ h (mem_image_of_mem f (mem_range.2 hus))
    rw [card_erase_of_mem (mem_sdiff.2 ⟨mem_univ _, hfuK⟩), card_univ_sdiff,
      SimpleGraph.card_neighborFinset_eq_degree] at hcu
    have := hδ (f u)
    omega
  -- (3.6)
  have h36 : ∀ x, (∀ i < s, f i ≠ x) → ∀ i, i + 1 < s → ¬ (G.Adj x (f i) ∧ G.Adj x (f (i + 1))) := by
    intro x hx i hi ⟨a1, a2⟩
    by_cases hi2 : 2 * i < s
    · obtain ⟨y, hy, hxy, hyf⟩ := h35 x hx i (by omega) a1
      obtain ⟨P, hP, hP0, hP1, hPS⟩ := hHam x y hx hy hxy
      have c := isSq_cat (hS.1.revSuffix i) hP (fun j hj k hk he => hPS k hk _ (by omega) he.symm)
        (fun _ _ => by rw [hP0, show s - 1 - (s - i - 1) = i by omega]; exact a1.symm)
        (fun _ _ => by rw [hP0, show s - 1 - (s - i - 2) = i + 1 by omega]; exact a2.symm)
        (fun _ _ => by rw [hP1, show s - 1 - (s - i - 1) = i by omega]; exact hyf.symm)
      have := (hS.2 _ _ c).1
      omega
    · obtain ⟨y, hy, hxy, hyf⟩ := h35 x hx (i + 1) (by omega) a2
      obtain ⟨P, hP, hP0, hP1, hPS⟩ := hHam x y hx hy hxy
      have c := isSq_cat (hS.1.take (m := i + 2) (by omega)) hP
        (fun j hj k hk he => hPS k hk j (by omega) he.symm)
        (fun _ _ => by rw [hP0, show i + 2 - 1 = i + 1 by omega]; exact a2.symm)
        (fun _ _ => by rw [hP0, show i + 2 - 2 = i by omega]; exact a1.symm)
        (fun _ _ => by rw [hP1, show i + 2 - 1 = i + 1 by omega]; exact hyf.symm)
      have := (hS.2 _ _ c).1
      omega
  -- (3.7)
  have h37 : h + 1 ≤ s := by
    have hv1' := (notS_iff v1).1 hv1
    obtain ⟨i, hi, hxi⟩ : ∃ i < s, G.Adj v1 (f i) := by
      by_contra hc
      push Not at hc
      have : dseg G v1 f 0 s = 0 := by
        unfold dseg
        rw [card_eq_zero, filter_eq_empty_iff]
        intro i hi; simp only [mem_Ico] at hi; exact hc i (by omega)
      have := hsplit v1
      have := hδ v1
      have := hHself v1 hv1
      omega
    obtain ⟨y, hy, hxy, hyf⟩ := h35 v1 hv1' i hi hxi
    obtain ⟨P, hP, hP0, hP1, hPS⟩ := hHam v1 y hv1' hy hxy
    have c := isSq_cat (isSq_one (f i)) hP (fun j hj k hk he => hPS k hk i hi he.symm)
      (fun _ _ => by rw [hP0]; exact hxi.symm) (fun h2 _ => by omega)
      (fun _ _ => by rw [hP1]; exact hyf.symm)
    have := (hS.2 _ _ c).1
    omega
  -- the maximal configuration of good triples
  let Cfg : ℕ → ℕ → Prop := fun t t' => 3 * t + 3 * t' ≤ s ∧ (∀ i < t, Good G s f (3 * i)) ∧
    (∀ i < t', Good G s f (s - 3 - 3 * i))
  have hCfg0 : Cfg 0 0 := ⟨by omega, fun i hi => by omega, fun i hi => by omega⟩
  set K := Nat.findGreatest (fun k => ∃ t t', t + t' = k ∧ Cfg t t') s with hK
  obtain ⟨t, t', htK, hCfg⟩ : ∃ t t', t + t' = K ∧ Cfg t t' :=
    Nat.findGreatest_spec (P := fun k => ∃ t t', t + t' = k ∧ Cfg t t') (Nat.zero_le s) ⟨0, 0, rfl, hCfg0⟩
  have hKmax : ∀ t1 t1', Cfg t1 t1' → t1 + t1' ≤ K := fun t1 t1' hc =>
    Nat.le_findGreatest (P := fun k => ∃ t t', t + t' = k ∧ Cfg t t') (by have := hc.1; omega)
      ⟨t1, t1', rfl, hc⟩
  have hsn' : n = s + h := by omega
  obtain ⟨hsum, hg1, hg2⟩ := hCfg
  by_cases htt : t ≤ t'
  · exfalso
    exact endgameX hS (by omega) hh (fun v => by rw [← hsn']; exact hδ v) hHam h35 h36 h34 h37 htt
      hsum hg1 hg2 (fun h3 hgood => by
        have := hKmax (t + 1) t' ⟨by omega, fun i hi => by
          rcases Nat.lt_or_ge i t with h' | h'
          · exact hg1 i h'
          · rw [show i = t by omega]; exact hgood, hg2⟩
        omega)
  · exfalso
    -- apply the end game to the reversed path
    have hnot : ∀ x, (∀ i < s, rev s f i ≠ x) ↔ (∀ i < s, f i ≠ x) := by
      intro x
      constructor
      · intro hx i hi he
        exact hx (s - 1 - i) (by omega) (by simp only [rev]; rw [show s - 1 - (s - 1 - i) = i by omega]; exact he)
      · intro hx i hi he
        exact hx (s - 1 - i) (by omega) he
    refine endgameX (f := rev s f) (t := t') (t' := t) hS.rev (by omega) hh
      (fun v => by rw [← hsn']; exact hδ v) ?_ ?_ ?_ h34 h37 (by omega) (by omega) ?_ ?_ ?_
    · intro x y hx hy hxy
      obtain ⟨P, hP, hP0, hP1, hPS⟩ := hHam x y ((hnot x).1 hx) ((hnot y).1 hy) hxy
      exact ⟨P, hP, hP0, hP1, fun i hi j hj => hPS i hi (s - 1 - j) (by omega)⟩
    · intro x hx i hi hxi
      obtain ⟨y, hy, hxy, hyf⟩ := h35 x ((hnot x).1 hx) (s - 1 - i) (by omega) hxi
      exact ⟨y, (hnot y).2 hy, hxy, hyf⟩
    · intro x hx i hi ⟨a1, a2⟩
      have := h36 x ((hnot x).1 hx) (s - 1 - (i + 1)) (by omega)
      simp only [rev] at a1 a2
      rw [show s - 1 - (i + 1) + 1 = s - 1 - i by omega] at this
      exact this ⟨a2, a1⟩
    · intro i hi
      rw [good_rev (by omega)]
      exact hg2 i hi
    · intro i hi
      rw [good_rev (by omega), show s - 3 - (s - 3 - 3 * i) = 3 * i by omega]
      exact hg1 i hi
    · intro h3 hgood
      rw [good_rev (by omega)] at hgood
      have := hKmax t (t' + 1) ⟨by omega, hg1, fun i hi => by
        rcases Nat.lt_or_ge i t' with h' | h'
        · exact hg2 i h'
        · rw [show i = t' by omega]; exact hgood⟩
      omega


end MainStepX

section FinalX

/-- **Fan–Kierstead** (full theorem, including the extremal case): a graph on `n` vertices with
minimum degree at least `(2n-1)/3` has a hamiltonian square path. -/
theorem fk_H2 {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hδ : ∀ v, 2 * Fintype.card V ≤ 3 * G.degree v + 1) :
    ∃ f : Fin (Fintype.card V) ≃ V, ∀ i j : Fin (Fintype.card V),
      i.val < j.val → j.val ≤ i.val + 2 → G.Adj (f i) (f j) := by
  classical
  by_cases h0 : Fintype.card V = 0
  · refine ⟨(Fintype.equivFin V).symm, fun i j _ _ => ?_⟩
    exact absurd i.2 (by omega)
  obtain ⟨v0⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨f, hf⟩ := main_stepX (G := G) hδ v0
  let e : Fin (Fintype.card V) → V := fun i => f i
  have he : Function.Injective e := fun i j h => Fin.ext (hf.inj i j i.2 j.2 h)
  have hb : Function.Bijective e := (Fintype.bijective_iff_injective_and_card e).2 ⟨he, by simp⟩
  refine ⟨Equiv.ofBijective e hb, fun i j hij hj2 => ?_⟩
  exact hf.adj_close i.2 j.2 hij hj2

end FinalX

end FK

/-
# Packing a graph of maximum degree two whose components are cycles or isolated vertices

Using the full Fan–Kierstead theorem (`FK.fk_H2`): the complement of `G` contains a hamiltonian
square-path, and every cycle can be numbered in zigzag order `v₀, v₁, v_{k-1}, v₂, v_{k-2}, …` so
that adjacent vertices get numbers at most two apart.
-/

namespace FKL

open SimpleGraph Finset BollobasEldridgeCatlinConjecture

section Labelling

variable {V : Type} [Fintype V] [DecidableEq V] {C : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
/-- A set closed under adjacency contains every vertex reachable from one of its vertices. -/
lemma reach_mem {T : Set V} (hT : ∀ u ∈ T, ∀ w, C.Adj u w → w ∈ T) {v u : V} (hv : v ∈ T)
    (h : C.Reachable v u) : u ∈ T := by
  obtain ⟨p⟩ := h
  revert hv
  induction p with
  | nil => exact id
  | cons e _ ih => exact fun hv => ih (hT _ hv _ e)

omit [Fintype V] [DecidableEq V] in
lemma nbr_two (hC2 : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    {v a b w : V} (ha : C.Adj v a) (hb : C.Adj v b) (hab : a ≠ b) (hw : C.Adj v w) :
    w = a ∨ w = b := by
  rcases hC2 v a b w ha hb hw with h | h | h
  · exact absurd h hab
  · exact Or.inl h.symm
  · exact Or.inr h.symm

omit [Fintype V] in
/-- Peeling off components one at a time: if every nonempty closed set contains a nonempty closed
block that can be labelled, then every closed set can be labelled. -/
lemma label_aux
    (hblock : ∀ S : Finset V, S.Nonempty → (∀ u ∈ S, ∀ w, C.Adj u w → w ∈ S) →
      ∃ T ⊆ S, T.Nonempty ∧ (∀ u ∈ T, ∀ w, C.Adj u w → w ∈ T) ∧
        ∃ p : V → ℕ, Set.InjOn p T ∧ (∀ u ∈ T, p u < T.card) ∧
          ∀ u ∈ T, ∀ w, C.Adj u w → p w ≤ p u + 2) :
    ∀ n (S : Finset V), S.card = n → (∀ u ∈ S, ∀ w, C.Adj u w → w ∈ S) →
      ∃ τ : V → ℕ, Set.InjOn τ S ∧ (∀ u ∈ S, τ u < S.card) ∧
        ∀ u ∈ S, ∀ w, C.Adj u w → τ w ≤ τ u + 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS hcl
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, by simp, by simp, by simp⟩
  obtain ⟨T, hTS, hTne, hTcl, p, hpinj, hplt, hpadj⟩ := hblock S hne hcl
  have hS'cl : ∀ u ∈ S \ T, ∀ w, C.Adj u w → w ∈ S \ T := by
    intro u hu w huw
    rw [mem_sdiff] at hu ⊢
    exact ⟨hcl u hu.1 w huw, fun hw => hu.2 (hTcl w hw u huw.symm)⟩
  have hcard : (S \ T).card + T.card = S.card := card_sdiff_add_card_eq_card hTS
  have hlt : (S \ T).card < n := by
    have := hTne.card_pos
    omega
  obtain ⟨τ, hτinj, hτlt, hτadj⟩ := ih _ hlt (S \ T) rfl hS'cl
  refine ⟨fun x => if x ∈ T then (S \ T).card + p x else τ x, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only at hxy
    by_cases hxT : x ∈ T <;> by_cases hyT : y ∈ T <;> simp only [hxT, hyT, if_true, if_false] at hxy
    · exact hpinj hxT hyT (by omega)
    · have := hτlt y (mem_sdiff.2 ⟨hy, hyT⟩)
      omega
    · have := hτlt x (mem_sdiff.2 ⟨hx, hxT⟩)
      omega
    · exact hτinj (mem_sdiff.2 ⟨hx, hxT⟩) (mem_sdiff.2 ⟨hy, hyT⟩) hxy
  · intro x hx
    by_cases hxT : x ∈ T
    · simp only [hxT, if_true]
      have := hplt x hxT
      omega
    · simp only [hxT, if_false]
      have := hτlt x (mem_sdiff.2 ⟨hx, hxT⟩)
      omega
  · intro u hu w huw
    by_cases huT : u ∈ T
    · have hwT := hTcl u huT w huw
      simp only [huT, hwT, if_true]
      have := hpadj u huT w huw
      omega
    · have huS' : u ∈ S \ T := mem_sdiff.2 ⟨hu, huT⟩
      have hwS' := hS'cl u huS' w huw
      have hwT : w ∉ T := (mem_sdiff.1 hwS').2
      simp only [huT, hwT, if_false]
      exact hτadj u huS' w huw

/-- The zigzag numbering of a cycle of length `k`. -/
def zz (k i : ℕ) : ℕ := if i = 0 then 0 else if 2 * i ≤ k then 2 * i - 1 else 2 * (k - i)

lemma zz_lt {k i : ℕ} (hk : 3 ≤ k) (hi : i < k) : zz k i < k := by
  unfold zz; split_ifs <;> omega

lemma zz_inj {k i j : ℕ} (_hk : 3 ≤ k) (hi : i < k) (hj : j < k) (h : zz k i = zz k j) : i = j := by
  unfold zz at h; split_ifs at h <;> omega

lemma zz_step {k i : ℕ} (hk : 3 ≤ k) (hi : i + 1 < k) :
    zz k (i + 1) ≤ zz k i + 2 ∧ zz k i ≤ zz k (i + 1) + 2 := by
  unfold zz; split_ifs <;> first | omega | contradiction

lemma zz_wrap {k : ℕ} (hk : 3 ≤ k) : zz k (k - 1) ≤ zz k 0 + 2 ∧ zz k 0 ≤ zz k (k - 1) + 2 := by
  unfold zz; split_ifs <;> omega

omit [Fintype V] [DecidableEq V] in
lemma isCycles_of (hC2 : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hC : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z) : C.IsCycles := by
  intro v ⟨a, ha⟩
  rw [mem_neighborSet] at ha
  obtain ⟨b, hba, hb⟩ := hC v a ha
  rw [Set.ncard_eq_two]
  refine ⟨a, b, hba.symm, ?_⟩
  ext w
  simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hw; exact nbr_two hC2 ha hb hba.symm hw
  · rintro (rfl | rfl) <;> assumption

/-- Every nonempty closed set contains a component of `C` (a cycle or an isolated vertex),
labelled so that adjacent vertices get labels at most two apart. -/
lemma blockGen
    (hC2 : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hC : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z)
    (S : Finset V) (hne : S.Nonempty) (hcl : ∀ u ∈ S, ∀ w, C.Adj u w → w ∈ S) :
    ∃ T ⊆ S, T.Nonempty ∧ (∀ u ∈ T, ∀ w, C.Adj u w → w ∈ T) ∧
      ∃ p : V → ℕ, Set.InjOn p T ∧ (∀ u ∈ T, p u < T.card) ∧
        ∀ u ∈ T, ∀ w, C.Adj u w → p w ≤ p u + 2 := by
  classical
  obtain ⟨v, hv⟩ := hne
  by_cases hiso : ∀ w, ¬ C.Adj v w
  · refine ⟨{v}, by simpa using hv, by simp, ?_, fun _ => 0, by simp, by simp, ?_⟩
    · intro u hu w huw
      rw [mem_singleton] at hu
      subst hu
      exact absurd huw (hiso w)
    · intro u hu w huw
      rw [mem_singleton] at hu
      subst hu
      exact absurd huw (hiso w)
  push Not at hiso
  obtain ⟨a, hva⟩ := hiso
  have hcyc := isCycles_of hC2 hC
  obtain ⟨q, hq, hverts⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := C.connectedComponentMk v) (v := v) ((ConnectedComponent.mem_supp_iff _ _).2 rfl)
    ⟨a, hva⟩
  set k := q.length with hk
  have hk3 : 3 ≤ k := hq.three_le_length
  have hginj : ∀ i j, i < k → j < k → q.getVert i = q.getVert j → i = j := fun i j hi hj h =>
    hq.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) h
  have hgk : q.getVert k = q.getVert 0 := by rw [hk, Walk.getVert_length, Walk.getVert_zero]
  -- the vertices of the component are exactly `q.getVert i`, `i < k`
  have hsupp : ∀ u, C.Reachable v u ↔ ∃ i < k, q.getVert i = u := by
    intro u
    constructor
    · intro hr
      have hu : u ∈ q.toSubgraph.verts := by
        rw [hverts, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
        exact hr.symm
      rw [Walk.mem_verts_toSubgraph, Walk.mem_support_iff_exists_getVert] at hu
      obtain ⟨n, hn, hnl⟩ := hu
      by_cases hnk : n = k
      · refine ⟨0, by omega, ?_⟩
        rw [← hgk, ← hnk, hn]
      · exact ⟨n, by omega, hn⟩
    · rintro ⟨i, -, rfl⟩
      have hu : q.getVert i ∈ q.toSubgraph.verts :=
        (Walk.mem_verts_toSubgraph _).2 (Walk.getVert_mem_support _ _)
      rw [hverts, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq] at hu
      exact hu.symm
  set T := (range k).image q.getVert with hT
  have hmemT : ∀ u, u ∈ T ↔ ∃ i < k, q.getVert i = u := by
    intro u; simp only [hT, mem_image, mem_range]
  have hTcard : T.card = k := by
    rw [hT, card_image_of_injOn (fun i hi j hj h => hginj i j (mem_range.1 hi) (mem_range.1 hj) h),
      card_range]
  have hTcl : ∀ u ∈ T, ∀ w, C.Adj u w → w ∈ T := by
    intro u hu w huw
    rw [hmemT, ← hsupp] at hu ⊢
    exact hu.trans huw.reachable
  -- the index of a vertex of the cycle
  let idx : V → ℕ := fun x => if h : ∃ i, i < k ∧ q.getVert i = x then Nat.find h else 0
  have hidx : ∀ i < k, idx (q.getVert i) = i := by
    intro i hi
    have hex : ∃ j, j < k ∧ q.getVert j = q.getVert i := ⟨i, hi, rfl⟩
    simp only [idx, dif_pos hex]
    have hs := Nat.find_spec hex
    exact hginj _ _ hs.1 hi hs.2
  refine ⟨T, ?_, ⟨v, (hmemT v).2 ⟨0, by omega, Walk.getVert_zero _⟩⟩, hTcl,
    fun x => zz k (idx x), ?_, ?_, ?_⟩
  · intro u hu
    rw [hmemT, ← hsupp] at hu
    exact reach_mem (T := (S : Set V)) (fun u hu w huw => hcl u hu w huw) hv hu
  · intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := (hmemT x).1 hx
    obtain ⟨j, hj, rfl⟩ := (hmemT y).1 hy
    simp only [hidx i hi, hidx j hj] at hxy
    rw [zz_inj hk3 hi hj hxy]
  · intro u hu
    obtain ⟨i, hi, rfl⟩ := (hmemT u).1 hu
    simp only [hidx i hi, hTcard]
    exact zz_lt hk3 hi
  · intro u hu w huw
    have huv : u ∈ q.toSubgraph.verts := by
      obtain ⟨i, hi, rfl⟩ := (hmemT u).1 hu
      exact (Walk.mem_verts_toSubgraph _).2 (Walk.getVert_mem_support _ _)
    have hadj := (hq.adj_toSubgraph_iff_of_isCycles hcyc huv w).2 huw
    rw [Walk.toSubgraph_adj_iff] at hadj
    obtain ⟨m, hm, hml⟩ := hadj
    rw [Sym2.eq_iff] at hm
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1 h2
      by_cases hmk : m + 1 < k
      · simp only [hidx m hml, hidx (m + 1) hmk]
        exact (zz_step hk3 hmk).1
      · have : m + 1 = k := by omega
        rw [this, hgk]
        simp only [hidx m hml, hidx 0 (by omega)]
        rw [show m = k - 1 by omega]
        exact (zz_wrap hk3).2
    · subst h1 h2
      by_cases hmk : m + 1 < k
      · simp only [hidx m hml, hidx (m + 1) hmk]
        exact (zz_step hk3 hmk).2
      · have : m + 1 = k := by omega
        rw [this, hgk]
        simp only [hidx m hml, hidx 0 (by omega)]
        rw [show m = k - 1 by omega]
        exact (zz_wrap hk3).1

/-- Every graph of maximum degree two without vertices of degree one can be labelled
`0, …, n-1` so that adjacent vertices get labels at most two apart. -/
lemma labellingGen
    (hC2 : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hC : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z) :
    ∃ τ : V → ℕ, Set.InjOn τ (univ : Finset V) ∧ (∀ u, τ u < Fintype.card V) ∧
      ∀ u w, C.Adj u w → τ w ≤ τ u + 2 := by
  obtain ⟨τ, h1, h2, h3⟩ := label_aux (blockGen hC2 hC) _ (univ : Finset V) rfl (by simp)
  exact ⟨τ, h1, fun u => by simpa using h2 u (mem_univ u), fun u w h => h3 u (mem_univ u) w h⟩

end Labelling

/-- Packing a graph of maximum degree two whose components are cycles or isolated vertices, when
`3 (Δ(G) + 1) ≤ n + 1`. -/
theorem pack_of {V : Type} [Fintype V] [DecidableEq V] (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (hC2 : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hC : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z) : Packs C G := by
  classical
  obtain ⟨τ, hτinj, hτlt, hτadj⟩ := labellingGen hC2 hC
  let g : V → Fin (Fintype.card V) := fun x => ⟨τ x, hτlt x⟩
  have hginj : Function.Injective g := by
    intro x y hxy
    exact hτinj (mem_coe.2 (mem_univ x)) (mem_coe.2 (mem_univ y)) (congrArg Fin.val hxy)
  have hgbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).2 ⟨hginj, by simp⟩
  let e : V ≃ Fin (Fintype.card V) := Equiv.ofBijective g hgbij
  have he : ∀ x, ((e x : Fin (Fintype.card V)) : ℕ) = τ x := fun x => rfl
  have hdeg : ∀ v, 2 * Fintype.card V ≤ 3 * Gᶜ.degree v + 1 := by
    intro v
    rw [degree_compl]
    have h1' := G.degree_le_maxDegree v
    have h2' := G.degree_lt_card_verts v
    omega
  obtain ⟨f, hf⟩ := FK.fk_H2 Gᶜ hdeg
  refine ⟨e.trans f, ?_⟩
  intro u w huw
  have a1 := hτadj u w huw
  have a2 := hτadj w u huw.symm
  have hτne : τ u ≠ τ w := fun h =>
    huw.ne (hτinj (mem_coe.2 (mem_univ u)) (mem_coe.2 (mem_univ w)) h)
  simp only [Equiv.trans_apply]
  rcases Nat.lt_or_gt_of_ne hτne with hlt | hlt
  · have := hf (e u) (e w) (by rw [he, he]; exact hlt) (by rw [he, he]; omega)
    exact ((compl_adj G _ _).1 this).2
  · have := hf (e w) (e u) (by rw [he, he]; exact hlt) (by rw [he, he]; omega)
    exact fun h => ((compl_adj G _ _).1 this).2 h.symm


end FKL

theorem OMA.solution : OMA.R_BollobasEldridgeCatlinConjecture_bollobas_eldridge_catlin_conjecture_variants_maxDegree_le_two_R1_H2_R1.H2 := by
  intro V _ _ C G _ hd _ _ _ hC2 hC
  intros
  exact FKL.pack_of C G hd hC2 hC
