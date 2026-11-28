import OMAReductions.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R2
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# A seven-total-color construction from three edge classes

Credit: @witeg4. The simple graph forbidden-color lemma and its supporting proofs
are due to @koolkao in proofs/TotalColoringConjecture.total_coloring_conjecture.variants.maxDegree_le_five.R1.H1.lean.
That merged proof is compiled as an individual submission by the project, so its
reused lemmas are included here. The multigraph lift, regular integral decomposition,
bipartite case and palette construction are given below.
-/

namespace OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R2_H2_R1
namespace Forbidden

open SimpleGraph

/-- A colour in `0..3` avoiding the three given values. -/
private def l1_pick (u v w : ℕ) : ℕ :=
  if 0 ≠ u ∧ 0 ≠ v ∧ 0 ≠ w then 0
  else if 1 ≠ u ∧ 1 ≠ v ∧ 1 ≠ w then 1
  else if 2 ≠ u ∧ 2 ≠ v ∧ 2 ≠ w then 2 else 3

lemma l1_pick_spec (u v w : ℕ) :
    l1_pick u v w < 4 ∧ l1_pick u v w ≠ u ∧ l1_pick u v w ≠ v ∧ l1_pick u v w ≠ w := by
  unfold l1_pick
  split_ifs <;> omega

lemma l1_per {k : ℕ} {a : ℕ → ℕ} (ha : ∀ i, a (i + k) = a i) (n i : ℕ) :
    a (i + k * n) = a i := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, ← Nat.add_assoc, ha, ih]

lemma l1_mod {k : ℕ} {a : ℕ → ℕ} (ha : ∀ i, a (i + k) = a i) (i j : ℕ) :
    a (i + j) = a (i % k + j) := by
  have h := Nat.mod_add_div i k
  rw [← l1_per ha (i / k) (i % k + j)]
  congr 1
  omega

lemma l1_succ_mod {k : ℕ} (hk : 2 ≤ k) (i : ℕ) :
    (i % k = k - 1 ∧ (i + 1) % k = 0) ∨ (i % k < k - 1 ∧ (i + 1) % k = i % k + 1) := by
  have hlt := Nat.mod_lt i (by omega : 0 < k)
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < k)]
  rcases Nat.lt_or_ge (i % k + 1) k with h | h
  · right; exact ⟨by omega, Nat.mod_eq_of_lt h⟩
  · left; refine ⟨by omega, ?_⟩
    rw [show i % k + 1 = k by omega, Nat.mod_self]

lemma l1_three (k : ℕ) (hk : 2 ≤ k) (P : ℕ → Prop) (c1 c2 c3 : ℕ)
    (h12 : c1 ≠ c2) (h13 : c1 ≠ c3) (h23 : c2 ≠ c3) (p1 : P c1) (p2 : P c2) (p3 : P c3) :
    ∃ f : ℕ → ℕ, (∀ i, f (i + k) = f i) ∧ ∀ i, P (f i) ∧ f i ≠ f (i + 1) := by
  refine ⟨fun i => if i % k = k - 1 then c3 else if i % k % 2 = 0 then c1 else c2, ?_, ?_⟩
  · intro i; simp only [Nat.add_mod_right]
  · intro i
    refine ⟨by dsimp only; split_ifs <;> assumption, ?_⟩
    dsimp only
    rcases l1_succ_mod hk i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; split_ifs <;> omega
    · rw [h2]; split_ifs <;> omega

lemma l1_two (k : ℕ) (hk : k % 2 = 0) (P : ℕ → Prop) (c1 c2 : ℕ) (h12 : c1 ≠ c2)
    (p1 : P c1) (p2 : P c2) :
    ∃ f : ℕ → ℕ, (∀ i, f (i + k) = f i) ∧ ∀ i, P (f i) ∧ f i ≠ f (i + 1) := by
  refine ⟨fun i => if i % 2 = 0 then c1 else c2, ?_, ?_⟩
  · intro i; dsimp only
    rw [show (i + k) % 2 = i % 2 by omega]
  · intro i
    refine ⟨by dsimp only; split_ifs <;> assumption, ?_⟩
    dsimp only; split_ifs <;> omega

/-- Greedy colouring of a path starting with colour `x`. -/
private def l1_g (a : ℕ → ℕ) (x : ℕ) : ℕ → ℕ
  | 0 => x
  | j + 1 => l1_pick (a (j + 1)) (a (j + 2)) (l1_g a x j)

lemma l1_caseA0 (k : ℕ) (hk : 2 ≤ k) (a : ℕ → ℕ) (ha : ∀ i, a (i + k) = a i)
    (hx : a (k - 1) < 4 ∧ a (k - 1) ≠ a 0 ∧ a (k - 1) ≠ a 1) :
    ∃ f : ℕ → ℕ, (∀ i, f (i + k) = f i) ∧
      ∀ i, f i < 4 ∧ f i ≠ a i ∧ f i ≠ a (i + 1) ∧ f i ≠ f (i + 1) := by
  have hg : ∀ j, l1_g a (a (k - 1)) j < 4 ∧ l1_g a (a (k - 1)) j ≠ a j ∧
      l1_g a (a (k - 1)) j ≠ a (j + 1) := by
    intro j
    cases j with
    | zero => exact hx
    | succ j =>
      have := l1_pick_spec (a (j + 1)) (a (j + 2)) (l1_g a (a (k - 1)) j)
      exact ⟨this.1, this.2.1, this.2.2.1⟩
  refine ⟨fun i => l1_g a (a (k - 1)) (i % k), ?_, ?_⟩
  · intro i; simp only [Nat.add_mod_right]
  · intro i
    dsimp only
    have e0 : a i = a (i % k) := by simpa using l1_mod ha i 0
    have e1 := l1_mod ha i 1
    obtain ⟨g1, g2, g3⟩ := hg (i % k)
    refine ⟨g1, by rw [e0]; exact g2, by rw [e1]; exact g3, ?_⟩
    rcases l1_succ_mod hk i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2, h1]; rw [h1] at g2; exact g2
    · rw [h2]; exact (l1_pick_spec _ _ (l1_g a (a (k - 1)) (i % k))).2.2.2.symm

lemma l1_caseA (k : ℕ) (hk : 2 ≤ k) (a : ℕ → ℕ) (ha : ∀ i, a (i + k) = a i) (s : ℕ)
    (hx : a (s + k - 1) < 4 ∧ a (s + k - 1) ≠ a s ∧ a (s + k - 1) ≠ a (s + 1)) :
    ∃ f : ℕ → ℕ, (∀ i, f (i + k) = f i) ∧
      ∀ i, f i < 4 ∧ f i ≠ a i ∧ f i ≠ a (i + 1) ∧ f i ≠ f (i + 1) := by
  obtain ⟨f, hf1, hf2⟩ := l1_caseA0 k hk (fun j => a (j + s))
    (fun i => by rw [show i + k + s = i + s + k by omega, ha])
    (by rw [show k - 1 + s = s + k - 1 by omega, Nat.zero_add,
      show 1 + s = s + 1 by omega]; exact hx)
  have hts : ∀ i, i + (k - s % k) + s = i + k * (s / k + 1) := by
    intro i
    have h := Nat.mod_add_div s k
    have := Nat.mod_lt s (by omega : 0 < k)
    rw [Nat.mul_add, Nat.mul_one]; omega
  refine ⟨fun i => f (i + (k - s % k)), ?_, ?_⟩
  · intro i; dsimp only
    rw [show i + k + (k - s % k) = i + (k - s % k) + k by omega, hf1]
  · intro i; simp only
    obtain ⟨h1, h2, h3, h4⟩ := hf2 (i + (k - s % k))
    rw [hts, l1_per ha] at h2
    rw [show i + (k - s % k) + 1 + s = (i + 1) + k * (s / k + 1) by rw [← hts]; omega,
      l1_per ha] at h3
    rw [show i + 1 + (k - s % k) = i + (k - s % k) + 1 by omega]
    exact ⟨h1, h2, h3, h4⟩

private def l1_P (a : ℕ → ℕ) (i c : ℕ) : Prop := c < 4 ∧ c ≠ a i ∧ c ≠ a (i + 1)

lemma l1_caseB (k : ℕ) (hk : 3 ≤ k) (a : ℕ → ℕ) (ha : ∀ i, a (i + k) = a i)
    (hB : ∀ i, a i < 4 → a i ≠ a (i + 1) → a i = a (i + 2)) :
    ∃ f : ℕ → ℕ, (∀ i, f (i + k) = f i) ∧
      ∀ i, f i < 4 ∧ f i ≠ a i ∧ f i ≠ a (i + 1) ∧ f i ≠ f (i + 1) := by
  have step : ∀ m i c, l1_P a (i + m) c → l1_P a i c := by
    intro m
    induction m with
    | zero => intro i c h; exact h
    | succ m ih =>
      intro i c h
      have h' := ih (i + 1) c (by rw [show i + 1 + m = i + (m + 1) by omega]; exact h)
      have := hB i
      unfold l1_P at h' ⊢
      rw [show i + 1 + 1 = i + 2 by omega] at h'
      omega
  have up : ∀ c, l1_P a 0 c → ∀ i, l1_P a i c := by
    intro c h i
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show i ≤ k * (i + 1) by nlinarith)
    apply step m i c
    rw [← hm]
    have e0 : a (k * (i + 1)) = a 0 := by simpa using l1_per ha (i + 1) 0
    have e1 : a (k * (i + 1) + 1) = a 1 := by rw [Nat.add_comm]; exact l1_per ha (i + 1) 1
    unfold l1_P at h ⊢
    rw [e0, e1]; exact h
  have fin : ∀ f : ℕ → ℕ, (∀ i, f (i + k) = f i) →
      (∀ i, (∀ j, l1_P a j (f i)) ∧ f i ≠ f (i + 1)) →
      ∃ f : ℕ → ℕ, (∀ i, f (i + k) = f i) ∧
        ∀ i, f i < 4 ∧ f i ≠ a i ∧ f i ≠ a (i + 1) ∧ f i ≠ f (i + 1) := by
    intro f hf hf2
    refine ⟨f, hf, fun i => ?_⟩
    obtain ⟨hp, hne⟩ := hf2 i
    obtain ⟨x1, x2, x3⟩ := hp i
    exact ⟨x1, x2, x3, hne⟩
  obtain ⟨p1, p11, p12, p13⟩ := l1_pick_spec (a 0) (a 1) (a 0)
  obtain ⟨p2, p21, p22, p23⟩ := l1_pick_spec (a 0) (a 1) (l1_pick (a 0) (a 1) (a 0))
  have q1 : l1_P a 0 (l1_pick (a 0) (a 1) (a 0)) := ⟨p1, p11, p12⟩
  have q2 : l1_P a 0 (l1_pick (a 0) (a 1) (l1_pick (a 0) (a 1) (a 0))) := ⟨p2, p21, p22⟩
  by_cases hpar : k % 2 = 0
  · obtain ⟨f, hf, hf2⟩ := l1_two k hpar (fun c => ∀ j, l1_P a j c) _ _ (Ne.symm p23)
      (up _ q1) (up _ q2)
    exact fin f hf hf2
  by_cases h3 : ∃ c3, l1_P a 0 c3 ∧ c3 ≠ l1_pick (a 0) (a 1) (a 0) ∧
      c3 ≠ l1_pick (a 0) (a 1) (l1_pick (a 0) (a 1) (a 0))
  · obtain ⟨c3, hc3, n1, n2⟩ := h3
    obtain ⟨f, hf, hf2⟩ := l1_three k (by omega) (fun c => ∀ j, l1_P a j c) _ _ _
      (Ne.symm p23) (Ne.symm n1) (Ne.symm n2) (up _ q1) (up _ q2) (up _ hc3)
    exact fin f hf hf2
  exfalso
  have hno : ∀ c, l1_P a 0 c → c = l1_pick (a 0) (a 1) (a 0) ∨
      c = l1_pick (a 0) (a 1) (l1_pick (a 0) (a 1) (a 0)) := fun c hc => by
    by_contra hh
    exact h3 ⟨c, hc, fun e => hh (Or.inl e), fun e => hh (Or.inr e)⟩
  have hne : a 0 < 4 ∧ a 1 < 4 ∧ a 0 ≠ a 1 := by
    have t0 := hno 0
    have t1 := hno 1
    have t2 := hno 2
    have t3 := hno 3
    unfold l1_P at t0 t1 t2 t3
    simp only [imp_iff_not_or, not_and_or, not_not, Nat.zero_add] at t0 t1 t2 t3
    omega
  have hn : ∀ i, ¬ l1_P a i (a 0) ∧ ¬ l1_P a i (a 1) := fun i =>
    ⟨fun h => (step i 0 _ (by rwa [Nat.zero_add])).2.1 rfl,
     fun h => (step i 0 _ (by rwa [Nat.zero_add])).2.2 rfl⟩
  have h2 : ∀ i, a (i + 2) = a i := by
    intro i
    have u := hn i
    have v := hn (i + 1)
    unfold l1_P at u v
    rw [show i + 1 + 1 = i + 2 by omega] at v
    omega
  have hev : ∀ j, a (2 * j) = a 0 := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Nat.mul_succ, h2, ih]
  have e := ha 1
  rw [show 1 + k = 2 * ((k + 1) / 2) by omega, hev] at e
  exact hne.2.2 e

theorem cyc_col (q k : ℕ) (hq3 : 3 ≤ q) (hq4 : q ≤ 4) (hk : 3 ≤ k) (a : ℕ → ℕ)
    (ha : ∀ i, a (i + k) = a i) (h3 : q = 3 → ∀ i, q ≤ a i) :
    ∃ f : ℕ → ℕ, (∀ i, f (i + k) = f i) ∧
      ∀ i, f i < q ∧ f i ≠ a i ∧ f i ≠ a (i + 1) ∧ f i ≠ f (i + 1) := by
  rcases (show q = 3 ∨ q = 4 by omega) with rfl | rfl
  · obtain ⟨f, hf, hf2⟩ := l1_three k (by omega) (fun c => c < 3) 0 1 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨f, hf, fun i => ?_⟩
    have u1 := h3 rfl i
    have u2 := h3 rfl (i + 1)
    obtain ⟨h4, h5⟩ := hf2 i
    exact ⟨h4, by omega, by omega, h5⟩
  · by_cases hA : ∃ s, a (s + k - 1) < 4 ∧ a (s + k - 1) ≠ a s ∧ a (s + k - 1) ≠ a (s + 1)
    · obtain ⟨s, hs⟩ := hA
      exact l1_caseA k (by omega) a ha s hs
    · apply l1_caseB k hk a ha
      intro i u1 u2
      by_contra u4
      apply hA
      refine ⟨i + 1, ?_⟩
      rw [show i + 1 + k - 1 = i + k by omega, ha, show i + 1 + 1 = i + 2 by omega]
      exact ⟨u1, u2, u4⟩


/-- Successor modulo `k` for `k ≥ 2`. -/
lemma lc_succ_mod {k r : ℕ} (hk : 2 ≤ k) (i : ℕ) (hr : i % k = r) :
    (i + 1) % k = if r + 1 = k then 0 else r + 1 := by
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hlt : r < k := hr ▸ Nat.mod_lt _ (by omega)
  rw [Nat.add_mod, hr, h1]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- A cycle extracted from a nodup chain whose entry `j ≥ 2` is adjacent to its head. -/
lemma lc_cycle {V : Type} (H : SimpleGraph V) (l : List V) (hnd : l.Nodup)
    (hc : l.IsChain H.Adj) (j : ℕ) (hj2 : 2 ≤ j) (hjl : j < l.length)
    (hadj : H.Adj l[j] l[0]) :
    ∃ (k : ℕ) (z : ℕ → V), 3 ≤ k ∧ (∀ i, z (i + k) = z i) ∧
      (∀ i j, i < k → j < k → z i = z j → i = j) ∧ ∀ i, H.Adj (z i) (z (i + 1)) := by
  have hl0 : 0 < l.length := by omega
  refine ⟨j + 1, fun i => l.getD (i % (j + 1)) l[0], by omega, ?_, ?_, ?_⟩
  · intro i
    simp only [Nat.add_mod_right]
  · intro a b ha hb hab
    simp only [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hab
    exact (hnd.getElem_inj_iff).1 hab
  · intro i
    have hr : i % (j + 1) < j + 1 := Nat.mod_lt _ (by omega)
    have hs := lc_succ_mod (k := j + 1) (by omega) i rfl
    simp only
    rw [hs]
    split_ifs with h
    · have hij : i % (j + 1) = j := by omega
      rw [hij, List.getD_eq_getElem _ _ hjl, List.getD_eq_getElem _ _ hl0]
      exact hadj
    · rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      exact hc.getElem _ (by omega)

theorem leaf_or_cycle {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) {u v : V}
    (huv : H.Adj u v) :
    (∃ l x : V, H.Adj l x ∧ ∀ y, H.Adj l y → y = x) ∨
    (∃ (k : ℕ) (z : ℕ → V), 3 ≤ k ∧ (∀ i, z (i + k) = z i) ∧
      (∀ i j, i < k → j < k → z i = z j → i = j) ∧ ∀ i, H.Adj (z i) (z (i + 1))) := by
  classical
  let P : ℕ → Prop := fun m => ∃ l : List V, l.Nodup ∧ l.IsChain H.Adj ∧ l.length = m
  let n := Fintype.card V
  have h2 : P 2 := ⟨[u, v], by simp [H.ne_of_adj huv], by simp [huv], rfl⟩
  have h2n : 2 ≤ n := by
    have := List.Nodup.length_le_card (show [u, v].Nodup by simp [H.ne_of_adj huv])
    simpa using this
  have hN : 2 ≤ Nat.findGreatest P n := Nat.le_findGreatest h2n h2
  obtain ⟨l, hnd, hc, hlen⟩ := Nat.findGreatest_spec (P := P) h2n h2
  -- every neighbour of the head lies on `l`
  match l, hnd, hc, hlen with
  | a :: b :: t, hnd, hc, hlen =>
    have hmem : ∀ y, H.Adj a y → y ∈ a :: b :: t := by
      intro y hy
      by_contra hy'
      have hnd' : (y :: a :: b :: t).Nodup := List.nodup_cons.2 ⟨hy', hnd⟩
      have hle := hnd'.length_le_card
      have hP : P (Nat.findGreatest P n + 1) :=
        ⟨y :: a :: b :: t, hnd', List.IsChain.cons_cons hy.symm hc, by simp [← hlen]⟩
      exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (by rw [← hlen]; simpa [n] using hle) hP
    by_cases hcyc : ∃ j, ∃ hj : j < (a :: b :: t).length, 2 ≤ j ∧
        H.Adj (a :: b :: t)[j] a
    · obtain ⟨j, hj, hj2, hadj⟩ := hcyc
      exact Or.inr (lc_cycle H _ hnd hc j hj2 hj hadj)
    · refine Or.inl ⟨a, b, List.rel_of_isChain_cons_cons hc, fun y hy => ?_⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hmem y hy)
      match j, hj with
      | 0, _ => exact absurd hy (by simp)
      | 1, _ => rfl
      | j + 2, hj => exact absurd ⟨j + 2, hj, by omega, hy.symm⟩ hcyc
  | [], _, _, hlen => simp at hlen; omega
  | [_], _, _, hlen => simp at hlen; omega


/-! ## Edge colourings with one forbidden colour per vertex -/

section edge

variable {V : Type} [Fintype V] [DecidableEq V]

open Classical in
/-- Degree, with classical decidability. -/
private noncomputable def dg (H : SimpleGraph V) (z : V) : ℕ := (Finset.univ.filter (H.Adj z)).card

open Classical in
/-- Number of ordered adjacent pairs (twice the number of edges). -/
private noncomputable def em (H : SimpleGraph V) : ℕ :=
  (Finset.univ.filter (fun p : V × V => H.Adj p.1 p.2)).card

/-- `1` if `b` is a real colour (below `q`), `0` otherwise. -/
private def ind (b q : ℕ) : ℕ := if b < q then 1 else 0

lemma ind_le (b q : ℕ) : ind b q ≤ 1 := by unfold ind; split_ifs <;> omega

/-- A proper edge colouring of `H` with colours below `q` avoiding `b x` at every end `x`. -/
private def GoodE (H : SimpleGraph V) (b : V → ℕ) (q : ℕ) (φ : Sym2 V → ℕ) : Prop :=
  (∀ x y, H.Adj x y → φ s(x, y) < q ∧ φ s(x, y) ≠ b x) ∧
  (∀ x y w, H.Adj x y → H.Adj x w → y ≠ w → φ s(x, y) ≠ φ s(x, w))

lemma exists_avoid {q : ℕ} (S : Finset ℕ) (h : (S.filter (· < q)).card < q) :
    ∃ c, c < q ∧ c ∉ S := by
  by_contra hc
  push_neg at hc
  have : Finset.range q ⊆ S.filter (· < q) := by
    intro c hc'
    rw [Finset.mem_range] at hc'
    exact Finset.mem_filter.mpr ⟨hc c hc', hc'⟩
  have := Finset.card_le_card this
  simp at this
  omega

lemma card_pair_filter (a c q : ℕ) :
    (({a, c} : Finset ℕ).filter (· < q)).card ≤ ind a q + ind c q := by
  unfold ind
  by_cases ha : a < q <;> by_cases hc : c < q
  · rw [if_pos ha, if_pos hc]
    exact (Finset.card_filter_le _ _).trans (Finset.card_insert_le _ _)
  · rw [if_pos ha, if_neg hc]
    have : ({a, c} : Finset ℕ).filter (· < q) ⊆ {a} := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with ⟨rfl | rfl, h⟩
      · simp
      · exact absurd h hc
    exact (Finset.card_le_card this).trans (by simp)
  · rw [if_neg ha, if_pos hc]
    have : ({a, c} : Finset ℕ).filter (· < q) ⊆ {c} := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with ⟨rfl | rfl, h⟩
      · exact absurd h ha
      · simp
    exact (Finset.card_le_card this).trans (by simp)
  · rw [if_neg ha, if_neg hc]
    have : ({a, c} : Finset ℕ).filter (· < q) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | rfl) <;> assumption
    rw [this]; simp

lemma card_single_filter (a q : ℕ) : (({a} : Finset ℕ).filter (· < q)).card ≤ ind a q := by
  unfold ind
  by_cases ha : a < q
  · rw [if_pos ha]; exact (Finset.card_filter_le _ _).trans (by simp)
  · rw [if_neg ha]
    have : ({a} : Finset ℕ).filter (· < q) = ∅ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false,
        not_and]; rintro rfl; exact ha
    rw [this]; simp

lemma dg_mono {H H' : SimpleGraph V} (h : H' ≤ H) (z : V) : dg H' z ≤ dg H z := by
  classical
  unfold dg
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  convert h hy

lemma em_lt {H H' : SimpleGraph V} (h : H' ≤ H) {x y : V} (hxy : H.Adj x y)
    (hn : ¬ H'.Adj x y) : em H' < em H := by
  classical
  unfold em
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(x, y), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; convert hxy
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; convert hn
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    convert h hp

lemma dg_pos {H : SimpleGraph V} {x y : V} (h : H.Adj x y) : 1 ≤ dg H x := by
  classical
  unfold dg
  apply Finset.card_pos.mpr
  exact ⟨y, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; convert h⟩

lemma dg_erase_two {H H' : SimpleGraph V} (h : H' ≤ H) {z a c : V} (ha : H.Adj z a) (hc : H.Adj z c)
    (hac : a ≠ c) (hna : ¬ H'.Adj z a) (hnc : ¬ H'.Adj z c) : dg H' z + 2 ≤ dg H z := by
  classical
  unfold dg
  have hsub : Finset.univ.filter (H'.Adj z) ⊆ ((Finset.univ.filter (H.Adj z)).erase a).erase c := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hy ⊢
    have hy' : H'.Adj z y := by convert hy
    refine ⟨fun e => hnc (e ▸ hy'), fun e => hna (e ▸ hy'), ?_⟩
    convert h hy'
  have h1 := Finset.card_le_card hsub
  have hmc : c ∈ (Finset.univ.filter (H.Adj z)).erase a := by
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun e => hac e.symm, by convert hc⟩
  have hma : a ∈ Finset.univ.filter (H.Adj z) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; convert ha
  rw [Finset.card_erase_of_mem hmc, Finset.card_erase_of_mem hma] at h1
  have : 2 ≤ (Finset.univ.filter (H.Adj z)).card := by
    have := Finset.card_le_card (show {a, c} ⊆ Finset.univ.filter (H.Adj z) by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hma
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; convert hc)
    rwa [Finset.card_pair hac] at this
  omega

lemma dg_erase_one {H H' : SimpleGraph V} (h : H' ≤ H) {z a : V} (ha : H.Adj z a)
    (hna : ¬ H'.Adj z a) : dg H' z + 1 ≤ dg H z := by
  classical
  unfold dg
  have hsub : Finset.univ.filter (H'.Adj z) ⊆ (Finset.univ.filter (H.Adj z)).erase a := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hy ⊢
    have hy' : H'.Adj z y := by convert hy
    refine ⟨fun e => hna (e ▸ hy'), ?_⟩
    convert h hy'
  have h1 := Finset.card_le_card hsub
  have hma : a ∈ Finset.univ.filter (H.Adj z) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; convert ha
  rw [Finset.card_erase_of_mem hma] at h1
  have : 1 ≤ (Finset.univ.filter (H.Adj z)).card := Finset.card_pos.mpr ⟨a, hma⟩
  omega

/-- Periodic sequences agree on residues. -/
lemma per_mod {α : Type*} {z : ℕ → α} {k : ℕ} (hper : ∀ i, z (i + k) = z i) (i : ℕ) :
    z i = z (i % k) := by
  have key : ∀ m r, z (r + k * m) = z r := by
    intro m
    induction m with
    | zero => intro r; simp
    | succ m ih => intro r; rw [show r + k * (m + 1) = (r + k * m) + k by ring, hper, ih]
  conv_lhs => rw [← Nat.mod_add_div i k]
  exact key _ _

lemma mod_succ' {i k : ℕ} (hk : 2 ≤ k) :
    (i + 1) % k = if i % k + 1 < k then i % k + 1 else 0 := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < k by omega)]
  have hr := Nat.mod_lt i (show 0 < k by omega)
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [show i % k + 1 = k by omega, Nat.mod_self]

lemma mod_pred' {p k : ℕ} (hk : 2 ≤ k) (hp : p < k) :
    (p + k - 1) % k = if p = 0 then k - 1 else p - 1 := by
  split_ifs with h
  · subst h; rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  · rw [show p + k - 1 = (p - 1) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

end edge

section lem2

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The leaf step: colour the pendant edge last. -/
lemma leaf_step {q : ℕ} {H : SimpleGraph V} {b : V → ℕ}
    (hb : ∀ z, dg H z + ind (b z) q + 1 ≤ q) {l x : V} (hlx : H.Adj l x)
    (hl : ∀ y, H.Adj l y → y = x) {φ' : Sym2 V → ℕ}
    (hφ' : GoodE (H.deleteEdges {s(l, x)}) b q φ') : ∃ φ, GoodE H b q φ := by
  classical
  set H' := H.deleteEdges {s(l, x)} with hH'
  have adj' : ∀ a c, H'.Adj a c ↔ H.Adj a c ∧ s(a, c) ≠ s(l, x) := by
    intro a c; simp [hH', deleteEdges_adj]
  set N := Finset.univ.filter (fun y => H.Adj x y ∧ y ≠ l) with hN
  set S := N.image (fun y => φ' s(x, y)) ∪ {b l, b x} with hS
  have hNc : N.card + 1 ≤ dg H x := by
    have hsub : N ⊆ (Finset.univ.filter (H.Adj x)).erase l := by
      intro y hy
      simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hy.2, hy.1⟩
    have hm : l ∈ Finset.univ.filter (H.Adj x) := by simp [hlx.symm]
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hm] at this
    have h1 : 1 ≤ (Finset.univ.filter (H.Adj x)).card := Finset.card_pos.mpr ⟨l, hm⟩
    have hd : dg H x = (Finset.univ.filter (H.Adj x)).card := rfl
    omega
  have hSc : (S.filter (· < q)).card < q := by
    rw [hS, Finset.filter_union]
    have e1 := Finset.card_union_le ((N.image (fun y => φ' s(x, y))).filter (· < q))
      (({b l, b x} : Finset ℕ).filter (· < q))
    have e2 := (Finset.card_filter_le ((N.image (fun y => φ' s(x, y)))) (· < q)).trans
      (Finset.card_image_le (s := N) (f := fun y => φ' s(x, y)))
    have e3 := card_pair_filter (b l) (b x) q
    have h1 := hb l
    have h2 := hb x
    have hl1 := dg_pos hlx
    have := ind_le (b l) q
    omega
  obtain ⟨c, hcq, hcS⟩ := exists_avoid S hSc
  have cne : ∀ y, H.Adj x y → y ≠ l → c ≠ φ' s(x, y) := by
    intro y hy hyl h
    exact hcS (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨y, by simp [hN, hy, hyl], h.symm⟩))
  have cbl : c ≠ b l := fun h => hcS (Finset.mem_union_right _ (by simp [h]))
  have cbx : c ≠ b x := fun h => hcS (Finset.mem_union_right _ (by simp [h]))
  refine ⟨fun e => if e = s(l, x) then c else φ' e, ?_, ?_⟩
  · intro a d had
    by_cases he : s(a, d) = s(l, x)
    · simp only [he, if_true]
      refine ⟨hcq, ?_⟩
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact cbl
      · exact cbx
    · simp only [he, if_false]
      exact hφ'.1 a d ((adj' a d).mpr ⟨had, he⟩)
  · intro a d w had haw hdw
    by_cases h1 : s(a, d) = s(l, x) <;> by_cases h2 : s(a, w) = s(l, x)
    · exact absurd (h1.trans h2.symm) (fun h => hdw (Sym2.congr_right.mp h))
    · simp only [h1, h2, if_true, if_false]
      rcases Sym2.eq_iff.mp h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd (hl w haw) (fun h => hdw h.symm)
      · exact cne w haw (fun h => hdw h.symm)
    · simp only [h1, h2, if_true, if_false]
      rcases Sym2.eq_iff.mp h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd (hl d had) hdw
      · exact (cne d had hdw).symm
    · simp only [h1, h2, if_false]
      exact hφ'.2 a d w ((adj' a d).mpr ⟨had, h1⟩) ((adj' a w).mpr ⟨haw, h2⟩) hdw

/-- The cycle step: recolour a whole cycle using `cyc_col`. -/
lemma cycle_step {q : ℕ} (hq3 : 3 ≤ q) (hq4 : q ≤ 4) {H : SimpleGraph V} {b : V → ℕ}
    (hb : ∀ z, dg H z + ind (b z) q + 1 ≤ q) {k : ℕ} {z : ℕ → V} (hk : 3 ≤ k)
    (hper : ∀ i, z (i + k) = z i) (hinj : ∀ i j, i < k → j < k → z i = z j → i = j)
    (hadj : ∀ i, H.Adj (z i) (z (i + 1))) {φ' : Sym2 V → ℕ}
    (hφ' : GoodE (H.deleteEdges {e | ∃ i, e = s(z i, z (i + 1))}) b q φ') :
    ∃ φ, GoodE H b q φ := by
  classical
  set CE : Set (Sym2 V) := {e | ∃ i, e = s(z i, z (i + 1))} with hCE
  set H' := H.deleteEdges CE with hH'
  have adj' : ∀ a c, H'.Adj a c ↔ H.Adj a c ∧ s(a, c) ∉ CE := by
    intro a c; simp only [hH', deleteEdges_adj]
  have hk0 : 0 < k := by omega
  have zm : ∀ i, z i = z (i % k) := per_mod hper
  have zeq : ∀ a c, z a = z c → a % k = c % k := by
    intro a c h
    rw [zm a, zm c] at h
    exact hinj _ _ (Nat.mod_lt _ hk0) (Nat.mod_lt _ hk0) h
  have zs : ∀ i, z (i + 1) = z (i % k + 1) := by
    intro i
    rw [zm (i + 1), zm (i % k + 1)]
    congr 1
    rw [Nat.add_mod i 1 k, Nat.add_mod (i % k) 1 k, Nat.mod_mod]
  -- the two cycle neighbours of `z p`
  have nb : ∀ p, p < k → ∀ y, s(z p, y) ∈ CE → y = z (p + 1) ∨ y = z (p + k - 1) := by
    intro p hp y hy
    obtain ⟨i, hi⟩ := hy
    rcases Sym2.eq_iff.mp hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      have := zeq _ _ h1
      rw [Nat.mod_eq_of_lt hp] at this
      rw [h2, zs i, ← this]
    · right
      have := zeq _ _ h1
      rw [Nat.mod_eq_of_lt hp, mod_succ' (by omega)] at this
      have key : i % k = (p + k - 1) % k := by
        rw [mod_pred' (by omega) hp]
        have hr := Nat.mod_lt i hk0
        split_ifs at this ⊢ <;> omega
      rw [h2, zm i, zm (p + k - 1), key]
  have nne : ∀ p, p < k → z (p + 1) ≠ z (p + k - 1) := by
    intro p hp h
    have := zeq _ _ h
    rw [mod_pred' (by omega) hp, mod_succ' (by omega), Nat.mod_eq_of_lt hp] at this
    split_ifs at this <;> omega
  have zk : ∀ p, z (p + k - 1 + 1) = z p := by
    intro p; rw [show p + k - 1 + 1 = p + k by omega, hper]
  have inCE1 : ∀ p, s(z p, z (p + 1)) ∈ CE := fun p => ⟨p, rfl⟩
  have inCE2 : ∀ p, s(z p, z (p + k - 1)) ∈ CE := fun p => ⟨p + k - 1, by rw [zk, Sym2.eq_swap]⟩
  have hle : H' ≤ H := deleteEdges_le _
  -- forbidden colours at a vertex
  set A : V → Finset ℕ := fun w =>
    ((Finset.univ.filter (H'.Adj w)).image (fun y => φ' s(w, y)) ∪ {b w}).filter (· < q) with hA
  have hAc : ∀ i, (A (z i)).card + 3 ≤ q := by
    intro i
    rw [zm i]
    set p := i % k
    have hp : p < k := Nat.mod_lt _ hk0
    have hb2 : H.Adj (z p) (z (p + k - 1)) := by
      have := hadj (p + k - 1); rw [zk] at this; exact this.symm
    have hd := dg_erase_two hle (hadj p) hb2 (nne p hp) (fun h => ((adj' _ _).mp h).2 (inCE1 p)) (fun h => ((adj' _ _).mp h).2 (inCE2 p))
    have e1 : (A (z p)).card ≤ dg H' (z p) + ind (b (z p)) q := by
      simp only [hA, Finset.filter_union]
      refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ (card_single_filter _ _))
      refine (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans ?_)
      unfold dg; apply le_of_eq; congr 1; ext; simp
    have := hb (z p)
    omega
  set aa : ℕ → ℕ := fun i => if h : (A (z i)).Nonempty then (A (z i)).min' h else q with haa
  have aa_per : ∀ i, aa (i + k) = aa i := by intro i; simp only [haa, hper]
  have aa_eq : ∀ i, ∀ c ∈ A (z i), c = aa i := by
    intro i c hc
    have hne : (A (z i)).Nonempty := ⟨c, hc⟩
    simp only [haa, dif_pos hne]
    have h1 : (A (z i)).card ≤ 1 := by have := hAc i; omega
    exact Finset.card_le_one.mp h1 _ hc _ (Finset.min'_mem _ _)
  have aa3 : q = 3 → ∀ i, q ≤ aa i := by
    intro h3 i
    have h0 : A (z i) = ∅ := by
      have := hAc i
      exact Finset.card_eq_zero.mp (by omega)
    simp only [haa, h0, Finset.not_nonempty_empty, dif_neg, not_false_eq_true, le_refl]
  obtain ⟨f, fper, hf⟩ := cyc_col q k hq3 hq4 hk aa aa_per aa3
  have fm : ∀ i, f i = f (i % k) := per_mod fper
  -- the new colouring
  let φ : Sym2 V → ℕ := fun e =>
    if h : ∃ i, i < k ∧ e = s(z i, z (i + 1)) then f (Nat.find h) else φ' e
  have φc : ∀ i, φ s(z i, z (i + 1)) = f i := by
    intro i
    have h : ∃ j, j < k ∧ s(z i, z (i + 1)) = s(z j, z (j + 1)) :=
      ⟨i % k, Nat.mod_lt _ hk0, by rw [zm i, zs i, ← zm i]⟩
    simp only [φ, dif_pos h]
    obtain ⟨hj, he⟩ := Nat.find_spec h
    set j := Nat.find h
    rw [fm i]
    congr 1
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := zeq _ _ h1; rw [Nat.mod_eq_of_lt hj] at this; exact this.symm
    · exfalso
      have e1 := zeq _ _ h1
      have e2 := zeq _ _ h2
      rw [mod_succ' (i := j) (show 2 ≤ k by omega), Nat.mod_eq_of_lt hj] at e1
      rw [mod_succ' (i := i) (show 2 ≤ k by omega), Nat.mod_eq_of_lt hj] at e2
      have hr := Nat.mod_lt i hk0
      split_ifs at e1 e2 <;> omega
  have φo : ∀ e, e ∉ CE → φ e = φ' e := by
    intro e he
    have h : ¬ ∃ i, i < k ∧ e = s(z i, z (i + 1)) := fun ⟨i, _, hi⟩ => he ⟨i, hi⟩
    simp only [φ, dif_neg h]
  -- a vertex on a cycle edge is some `z p`
  have onc : ∀ x y, s(x, y) ∈ CE → ∃ p, p < k ∧ x = z p := by
    intro x y ⟨i, hi⟩
    rcases Sym2.eq_iff.mp hi with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨i % k, Nat.mod_lt _ hk0, h1.trans (zm i)⟩
    · exact ⟨(i + 1) % k, Nat.mod_lt _ hk0, h1.trans (zm (i + 1))⟩
  -- colour of a cycle edge at `z p`
  have cyc_val : ∀ p, p < k → ∀ y, s(z p, y) ∈ CE →
      (y = z (p + 1) ∧ φ s(z p, y) = f p) ∨ (y = z (p + k - 1) ∧ φ s(z p, y) = f (p + k - 1)) := by
    intro p hp y hy
    rcases nb p hp y hy with rfl | rfl
    · exact Or.inl ⟨rfl, φc p⟩
    · refine Or.inr ⟨rfl, ?_⟩
      rw [Sym2.eq_swap, ← zk p, φc]
  -- members of `A`
  have memA : ∀ w y, H'.Adj w y → φ' s(w, y) ∈ A w := by
    intro w y hy
    simp only [hA, Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Or.inl ⟨y, hy, rfl⟩, (hφ'.1 w y hy).1⟩
  have memB : ∀ w, b w < q → b w ∈ A w := by
    intro w hw
    simp [hA, hw]
  -- the colour of a cycle edge at `x` avoids everything in `A x`
  have cav : ∀ p, p < k → ∀ y, s(z p, y) ∈ CE → ∀ c ∈ A (z p), φ s(z p, y) ≠ c := by
    intro p hp y hy c hc
    rcases cyc_val p hp y hy with ⟨-, h⟩ | ⟨-, h⟩
    · rw [h, aa_eq p c hc]; exact (hf p).2.1
    · rw [h]
      have : c = aa (p + k - 1 + 1) := by rw [aa_eq _ c (by rw [zk]; exact hc)]
      rw [this]; exact (hf _).2.2.1
  refine ⟨φ, ?_, ?_⟩
  · intro x y hxy
    by_cases he : s(x, y) ∈ CE
    · obtain ⟨p, hp, rfl⟩ := onc x y he
      refine ⟨?_, ?_⟩
      · rcases cyc_val p hp y he with ⟨-, h⟩ | ⟨-, h⟩
        · rw [h]; exact (hf p).1
        · rw [h]; exact (hf (p + k - 1)).1
      · by_cases hbq : b (z p) < q
        · exact cav p hp y he _ (memB _ hbq)
        · intro h
          rcases cyc_val p hp y he with ⟨-, h'⟩ | ⟨-, h'⟩
          · have := (hf p).1; omega
          · have := (hf (p + k - 1)).1; omega
    · rw [φo _ he]; exact hφ'.1 x y ((adj' x y).mpr ⟨hxy, he⟩)
  · intro x y w hxy hxw hyw
    by_cases h1 : s(x, y) ∈ CE <;> by_cases h2 : s(x, w) ∈ CE
    · obtain ⟨p, hp, rfl⟩ := onc x y h1
      rcases cyc_val p hp y h1 with ⟨ry, cy⟩ | ⟨ry, cy⟩ <;>
        rcases cyc_val p hp w h2 with ⟨rw', cw⟩ | ⟨rw', cw⟩
      · exact absurd (ry.trans rw'.symm) hyw
      · rw [cy, cw]
        have := (hf (p + k - 1)).2.2.2
        rw [show p + k - 1 + 1 = p + k by omega, fm (p + k), Nat.add_mod_right, ← fm p] at this
        exact fun h => this h.symm
      · rw [cy, cw]
        have := (hf (p + k - 1)).2.2.2
        rw [show p + k - 1 + 1 = p + k by omega, fm (p + k), Nat.add_mod_right, ← fm p] at this
        exact this
      · exact absurd (ry.trans rw'.symm) hyw
    · obtain ⟨p, hp, rfl⟩ := onc x y h1
      rw [φo _ h2]
      exact cav p hp y h1 _ (memA _ _ ((adj' _ _).mpr ⟨hxw, h2⟩))
    · obtain ⟨p, hp, rfl⟩ := onc x w h2
      rw [φo _ h1]
      exact fun h => cav p hp w h2 _ (memA _ _ ((adj' _ _).mpr ⟨hxy, h1⟩)) h.symm
    · rw [φo _ h1, φo _ h2]
      exact hφ'.2 x y w ((adj' x y).mpr ⟨hxy, h1⟩) ((adj' x w).mpr ⟨hxw, h2⟩) hyw

/-- **Lemma 2.** For `q ∈ {3, 4}`, a graph with `deg z + [b z < q] ≤ q - 1` has a proper edge
colouring with `q` colours avoiding `b x` at each end `x`. -/
theorem lem2 {q : ℕ} (hq3 : 3 ≤ q) (hq4 : q ≤ 4) :
    ∀ (n : ℕ) (H : SimpleGraph V), em H = n → ∀ b : V → ℕ,
      (∀ z, dg H z + ind (b z) q + 1 ≤ q) → ∃ φ, GoodE H b q φ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H hn b hb
  by_cases hE : ∃ u v, H.Adj u v
  swap
  · push_neg at hE
    exact ⟨fun _ => 0, fun x y h => absurd h (hE x y), fun x y _ h => absurd h (hE x y)⟩
  obtain ⟨u, v, huv⟩ := hE
  rcases leaf_or_cycle H huv with ⟨l, x, hlx, hl⟩ | ⟨k, z, hk, hper, hinj, hadj⟩
  · have hlt : em (H.deleteEdges {s(l, x)}) < n := by
      rw [← hn]
      exact em_lt (deleteEdges_le _) hlx (by simp [deleteEdges_adj])
    obtain ⟨φ', hφ'⟩ := ih _ hlt _ rfl b (fun z =>
      (Nat.add_le_add_right (Nat.add_le_add_right (dg_mono (deleteEdges_le _) z) _) _).trans (hb z))
    exact leaf_step hb hlx hl hφ'
  · have hlt : em (H.deleteEdges {e | ∃ i, e = s(z i, z (i + 1))}) < n := by
      rw [← hn]
      exact em_lt (deleteEdges_le _) (hadj 0) (by simp only [deleteEdges_adj]; exact fun h => h.2 ⟨0, rfl⟩)
    obtain ⟨φ', hφ'⟩ := ih _ hlt _ rfl b (fun z =>
      (Nat.add_le_add_right (Nat.add_le_add_right (dg_mono (deleteEdges_le _) z) _) _).trans (hb z))
    exact cycle_step hq3 hq4 hb hk hper hinj hadj hφ'

end lem2
end Forbidden
open scoped BigOperators Classical

/-- Two residual edges per vertex can be assigned four colors while avoiding
a prescribed proper vertex coloring, including isolated doubled edges. -/
theorem two_left {W : Type} [Fintype W] [DecidableEq W] (m : W → W → ℕ)
    (symm : ∀ x y, m x y = m y x) (loop : ∀ x, m x x = 0)
    (deg : ∀ x, ∑ y, m x y ≤ 2) (v : W → Fin 4)
    (proper : ∀ x y, 0 < m x y → v x ≠ v y) :
    ∃ e : W → W → Finset (Fin 4), (∀ x y, e x y = e y x) ∧
      (∀ x y, (e x y).card = m x y) ∧ (∀ x y, v x ∉ e x y) ∧
      (∀ x y z, y ≠ z → Disjoint (e x y) (e x z)) := by
  classical
  let G : SimpleGraph W := SimpleGraph.mk (fun x y => m x y = 1)
    (by constructor; intro x y h; exact (symm y x).trans h)
    (by constructor; intro x; simp [loop])
  have bound (x y : W) : m x y ≤ 2 := le_trans (Finset.single_le_sum
    (f := m x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)) (deg x)
  have degree (x : W) : Forbidden.dg G x ≤ 2 := by
    apply le_trans _ (deg x)
    rw [Forbidden.dg,Finset.card_filter]
    apply Finset.sum_le_sum; intro y _
    split_ifs with h
    · change m x y = 1 at h; omega
    · exact Nat.zero_le _
  obtain ⟨c,hc⟩ := Forbidden.lem2 (V := W) (q := 4) (by decide) (by decide)
    _ G rfl (fun x => (v x).val) (fun x => by have := degree x; have := Forbidden.ind_le (v x).val 4; omega)
  let col (x y : W) : Fin 4 := ⟨c s(x,y) % 4, Nat.mod_lt _ (by decide)⟩
  have col_val (x y : W) (h : m x y = 1) : (col x y).val = c s(x,y) :=
    Nat.mod_eq_of_lt (hc.1 x y h).1
  let e (x y : W) : Finset (Fin 4) := if m x y = 2 then Finset.univ \ {v x,v y}
    else if m x y = 1 then {col x y} else ∅
  have isolated (x y z : W) (hne : y ≠ z) (h : m x y = 2) : m x z = 0 := by
    have hh := Finset.sum_le_sum_of_subset (f := m x)
      (Finset.subset_univ ({y,z} : Finset W))
    simp [hne] at hh
    have := deg x
    omega
  have empty (x y : W) (h : m x y = 0) : e x y = ∅ := by simp [e,h]
  refine ⟨e,?_,?_,?_,?_⟩
  · intro x y
    have eq : col x y = col y x := by simp only [col,Sym2.eq_swap]
    simp only [e,symm x y,Finset.pair_comm (v x) (v y),eq]
  · intro x y
    by_cases h : m x y = 2
    · have neq := proper x y (by omega)
      simp [e,h,Finset.card_sdiff_of_subset (Finset.subset_univ _),neq]
    · by_cases h' : m x y = 1
      · simp [e,h,h']
      · have := bound x y; have hz : m x y = 0 := by omega
        simp [e,hz]
  · intro x y
    by_cases h : m x y = 2
    · simp [e,h]
    · by_cases h' : m x y = 1
      · simp only [e,if_neg h,if_pos h',Finset.mem_singleton]
        intro eq
        exact (hc.1 x y h').2 ((col_val x y h').symm.trans (congrArg Fin.val eq.symm))
      · simp [e,h,h']
  · intro x y z hne
    by_cases h : m x y = 2
    · simp [empty _ _ (isolated x y z hne h)]
    by_cases h' : m x z = 2
    · simp [empty _ _ (isolated x z y hne.symm h')]
    by_cases hy : m x y = 1
    · by_cases hz : m x z = 1
      · simp only [e,if_neg h,if_neg h',if_pos hy,if_pos hz,Finset.disjoint_singleton]
        intro eq
        exact hc.2 x y z hy hz hne ((col_val x y hy).symm.trans ((congrArg Fin.val eq).trans (col_val x z hz)))
      · simp [e,h',hz]
    · simp [e,h,hy]


open Finset

private theorem support_perm {W : Type} [Fintype W] [DecidableEq W] (m : W → W → ℕ)
    {d : ℕ} (hd : 0 < d) (row : ∀ x, ∑ y, m x y = d) (col : ∀ y, ∑ x, m x y = d) :
    ∃ σ : Equiv.Perm W, ∀ x, 0 < m x (σ x) := by
  classical
  let N (x : W) := (Finset.univ : Finset W).filter (fun y => 0 < m x y)
  have hall (A : Finset W) : A.card ≤ (A.biUnion N).card := by
    have rows (x : W) : ∑ y ∈ N x, m x y = d := by
      rw [← row x, Finset.sum_subset (Finset.subset_univ _)]
      intro y _ hy
      simp [N] at hy
      exact hy
    have b : A.card*d ≤ (A.biUnion N).card*d := by
      calc A.card*d = ∑ x ∈ A, ∑ y ∈ N x, m x y := by simp [rows]
           _ ≤ ∑ x ∈ A, ∑ y ∈ A.biUnion N, m x y := by
              apply Finset.sum_le_sum; intro x hx
              exact Finset.sum_le_sum_of_subset (Finset.subset_biUnion_of_mem N hx)
           _ ≤ ∑ x, ∑ y ∈ A.biUnion N, m x y := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
           _ = _ := by rw [Finset.sum_comm]; simp [col]
    exact Nat.le_of_mul_le_mul_right b hd
  obtain ⟨g, hinj, hg⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective N).mp hall
  exact ⟨Equiv.ofBijective g ((Finite.injective_iff_bijective).mp hinj),
    fun x => (Finset.mem_filter.mp (hg x)).2⟩

theorem decomposition {W : Type} [Fintype W] [DecidableEq W] (d : ℕ) (m : W → W → ℕ)
    (row : ∀ x, ∑ y, m x y = d) (col : ∀ y, ∑ x, m x y = d) :
    ∃ f : Fin d → Equiv.Perm W, ∀ x y, m x y = ∑ k, if f k x = y then 1 else 0 := by
  classical
  induction d generalizing m with
  | zero =>
    refine ⟨Fin.elim0, fun x y => ?_⟩
    have h := Finset.single_le_sum (f := m x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)
    simp [row] at h
    simp [h]
  | succ d ih =>
    obtain ⟨σ,hσ⟩ := support_perm m (Nat.succ_pos d) row col
    let rest (x y : W) := m x y - if σ x = y then 1 else 0
    have split (x y : W) : m x y = rest x y + (if σ x = y then 1 else 0) := by
      by_cases h : σ x = y
      · subst y; simp [rest]; have := hσ x; omega
      · simp [rest,h]
    have row' (x : W) : ∑ y, rest x y = d := by
      have h := row x
      simp_rw [split x] at h
      simpa [Finset.sum_add_distrib] using h
    have col' (y : W) : ∑ x, rest x y = d := by
      have h := col y
      simp_rw [fun x => split x y,σ.apply_eq_iff_eq_symm_apply] at h
      simpa [Finset.sum_add_distrib] using h
    obtain ⟨f,hf⟩ := ih rest row' col'
    refine ⟨Fin.cons σ f, fun x y => ?_⟩
    rw [Fin.sum_univ_succ]
    simpa [hf x y,add_comm] using split x y

/-- A regular bipartite multiplicity matrix admits d edge colors, with
symmetric sets recording all the copies of each unordered edge. -/
theorem bipartite_edges {W : Type} [Fintype W] [DecidableEq W] (d : ℕ) (m : W → W → ℕ)
    (symm : ∀ x y, m x y = m y x) (row : ∀ x, ∑ y, m x y = d)
    (b : W → Bool) (cross : ∀ x y, 0 < m x y → b x ≠ b y) :
    ∃ e : W → W → Finset (Fin d), (∀ x y, e x y = e y x) ∧
      (∀ x y, (e x y).card = m x y) ∧ (∀ x y z, y ≠ z → Disjoint (e x y) (e x z)) := by
  classical
  have col (y : W) : ∑ x, m x y = d := by simpa only [fun x => symm x y] using row y
  obtain ⟨f,hf⟩ := decomposition d m row col
  let dir (x y : W) := (Finset.univ : Finset (Fin d)).filter (fun k => f k x = y)
  have card (x y : W) : (dir x y).card = m x y := by
    rw [hf x y]; exact Finset.card_filter _ _
  let e (x y : W) : Finset (Fin d) := if b x = b y then ∅ else if b x then dir x y else dir y x
  refine ⟨e,?_,?_,?_⟩
  · intro x y
    cases hx : b x <;> cases hy : b y <;> simp [e,hx,hy]
  · intro x y
    by_cases h : b x = b y
    · have hz : m x y = 0 := by by_contra! hpos; exact cross x y (Nat.pos_of_ne_zero hpos) h
      simp [e,h,hz]
    · simp only [e, if_neg h]
      cases hx : b x <;> simp [card,symm y x]
  · intro x y z hyz
    apply Finset.disjoint_left.mpr
    intro k hk hl
    by_cases h : b x = b y
    · simp [e,h] at hk
    by_cases h' : b x = b z
    · simp [e,h'] at hl
    simp only [e, if_neg h] at hk
    simp only [e, if_neg h'] at hl
    cases hx : b x
    · simp [hx,dir] at hk hl
      exact hyz ((f k).injective (hk.trans hl.symm))
    · simp [hx,dir] at hk hl
      exact hyz (hk.symm.trans hl)

/-- Combine the residual four-color lists with three edge colors on the
complementary copies. The vertex colors belong to the four-color palette. -/
theorem assemble {W : Type} (A : SimpleGraph W) (m : W → W → ℕ) (v : W → Fin 4)
    (hv : ∀ x y, A.Adj x y → v x ≠ v y)
    (a : W → W → Finset (Fin 4)) (b : W → W → Finset (Fin 3))
    (sa : ∀ x y, a x y = a y x) (sb : ∀ x y, b x y = b y x)
    (counts : ∀ x y, (a x y).card + (b x y).card = m x y)
    (avoid : ∀ x y, v x ∉ a x y)
    (da : ∀ x y z, y ≠ z → Disjoint (a x y) (a x z))
    (db : ∀ x y z, y ≠ z → Disjoint (b x y) (b x z)) :
    ∃ (vc : W → Fin 7) (e : W → W → Finset (Fin 7)),
      (∀ x y, e x y = e y x) ∧ (∀ x y, (e x y).card = m x y) ∧
      (∀ x y, A.Adj x y → vc x ≠ vc y) ∧ (∀ x y, vc x ∉ e x y) ∧
      (∀ x y z, y ≠ z → Disjoint (e x y) (e x z)) := by
  classical
  let lo : Fin 4 ↪ Fin 7 := Fin.castLEEmb (by decide)
  let hi : Fin 3 ↪ Fin 7 := Fin.natAddEmb 4
  have sep : ∀ (c : Fin 4) (d : Fin 3), lo c ≠ hi d := by decide
  have apart (X : Finset (Fin 4)) (Y : Finset (Fin 3)) : Disjoint (X.map lo) (Y.map hi) := by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    obtain ⟨x,_,hx⟩ := Finset.mem_map.mp hk
    obtain ⟨y,_,hy⟩ := Finset.mem_map.mp hl
    exact sep x y (hx.trans hy.symm)
  let E (x y : W) := (a x y).map lo ∪ (b x y).map hi
  refine ⟨fun x => lo (v x),E,?_,?_,?_,?_,?_⟩
  · intro x y; simp only [E,sa x y,sb x y]
  · intro x y
    simpa only [E,Finset.card_union_of_disjoint (apart _ _),Finset.card_map] using counts x y
  · intro x y h eq; exact hv x y h (lo.injective eq)
  · intro x y h
    rcases Finset.mem_union.mp h with h|h
    · exact avoid x y ((Finset.mem_map' lo).mp h)
    · obtain ⟨c,_,eq⟩ := Finset.mem_map.mp h
      exact sep _ _ eq.symm
  · intro x y z h
    change Disjoint (_ ∪ _) (_ ∪ _)
    rw [Finset.disjoint_union_left,Finset.disjoint_union_right,Finset.disjoint_union_right]
    exact ⟨⟨(Finset.disjoint_map lo).mpr (da x y z h),apart _ _⟩,
      (apart _ _).symm,(Finset.disjoint_map hi).mpr (db x y z h)⟩

/-- Three edge color classes leaving residual degree at most two suffice
when the full support has a proper four-vertex-coloring. -/
theorem three_classes {W : Type} [Fintype W] (A : SimpleGraph W) (m : W → W → ℕ)
    (symm : ∀ x y, m x y = m y x) (loop : ∀ x, m x x = 0)
    (support : ∀ x y, A.Adj x y ↔ 0 < m x y)
    (v : W → Fin 4) (hv : ∀ x y, A.Adj x y → v x ≠ v y)
    (e : W → W → Finset (Fin 3)) (es : ∀ x y, e x y = e y x)
    (ec : ∀ x y, (e x y).card ≤ m x y) (deg : ∀ x, (∑ y, (m x y-(e x y).card)) ≤ 2)
    (ed : ∀ x y z, y ≠ z → Disjoint (e x y) (e x z)) :
    ∃ (vc : W → Fin 7) (edges : W → W → Finset (Fin 7)),
      (∀ x y, edges x y = edges y x) ∧ (∀ x y, (edges x y).card = m x y) ∧
      (∀ x y, A.Adj x y → vc x ≠ vc y) ∧ (∀ x y, vc x ∉ edges x y) ∧
      (∀ x y z, y ≠ z → Disjoint (edges x y) (edges x z)) := by
  classical
  let r (x y : W) := m x y-(e x y).card
  have rs (x y : W) : r x y = r y x := by simp only [r,symm x y,es x y]
  have rl (x : W) : r x x = 0 := by simp [r,loop]
  have proper (x y : W) (h : 0 < r x y) := hv x y ((support x y).mpr
    (lt_of_lt_of_le h (Nat.sub_le _ _)))
  obtain ⟨a,sa,ca,av,da⟩ := two_left r rs rl deg v proper
  apply assemble A m v hv a e sa es _ av da ed
  intro x y
  rw [ca x y]; exact Nat.sub_add_cancel (ec x y)


private def bits4 (side orientation : Bool) : Fin 4 :=
  if side then (if orientation then 3 else 2) else (if orientation then 1 else 0)

private def trim (s : Finset (Fin 4)) : Finset (Fin 3) :=
  Finset.univ.filter (fun k => k.castSucc ∈ s)

/-- Bipartiteness after deleting a perfect matching provides both a
four-vertex-coloring and three edge classes leaving degree at most two. -/
theorem bipartite_data {W : Type} [Fintype W] (A : SimpleGraph W) (M : A.Subgraph)
    (hM : M.IsPerfectMatching) (m r : W → W → ℕ)
    (symm : ∀ x y, m x y = m y x) (deg : ∀ x, ∑ y, m x y = 5)
    (support : ∀ x y, A.Adj x y ↔ 0 < m x y)
    (onM : ∀ x y, M.Adj x y → r x y+1 = m x y)
    (offM : ∀ x y, ¬M.Adj x y → r x y = m x y)
    (b : W → Bool) (hb : ∀ x y, 0 < r x y → b x ≠ b y) :
    (∃ v : W → Fin 4, ∀ x y, A.Adj x y → v x ≠ v y) ∧
    ∃ e : W → W → Finset (Fin 3), (∀ x y, e x y = e y x) ∧
      (∀ x y, (e x y).card ≤ m x y) ∧ (∀ x, (∑ y, (m x y-(e x y).card)) ≤ 2) ∧
      (∀ x y z, y ≠ z → Disjoint (e x y) (e x z)) := by
  classical
  letI : LinearOrder W := WellOrderingRel.isWellOrder.linearOrder
  have hu := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM
  let mate (x : W) := (hu x).choose
  have adj (x y : W) : M.Adj x y ↔ y = mate x :=
    ⟨(hu x).choose_spec.2 y, fun e => e ▸ (hu x).choose_spec.1⟩
  have split (x y : W) : m x y = r x y + if y = mate x then 1 else 0 := by
    by_cases h : M.Adj x y
    · simpa [(adj x y).mp h] using (onM x y h).symm
    · simpa [(adj x y).not.mp h] using (offM x y h).symm
  constructor
  · refine ⟨fun x => bits4 (b x) (decide (x < mate x)),?_⟩
    intro x y hxy eq
    have inj : ∀ a b c d, bits4 a b = bits4 c d → a=c ∧ b=d := by decide
    obtain ⟨hs,hbit⟩ := inj _ _ _ _ eq
    have mxy : M.Adj x y := by
      by_contra h
      exact hb x y (by rw [offM x y h]; exact (support x y).mp hxy) hs
    have e1 := (adj x y).mp mxy
    have e2 := (adj y x).mp (M.adj_symm mxy)
    rw [← e1,← e2] at hbit
    have hn := A.ne_of_adj hxy
    rcases lt_or_gt_of_ne hn with lt|gt
    · simp [lt,lt_asymm lt] at hbit
    · simp [gt,lt_asymm gt] at hbit
  · have rs (x y : W) : r x y = r y x := by
      by_cases h : M.Adj x y
      · have h1 := onM x y h; have h2 := onM y x (M.adj_symm h); have := symm x y; omega
      · rw [offM x y h,offM y x (fun h' => h (M.adj_symm h')),symm x y]
    have dr (x : W) : ∑ y, r x y = 4 := by
      have h := deg x
      simp_rw [split x] at h
      simp [Finset.sum_add_distrib] at h
      omega
    obtain ⟨e,es,ec,ed⟩ := bipartite_edges 4 r rs dr b hb
    have cnt : ∀ s : Finset (Fin 4), (trim s).card + (if (3 : Fin 4) ∈ s then 1 else 0) = s.card := by decide
    let extra (x y : W) := if (3 : Fin 4) ∈ e x y then 1 else 0
    have exc (x : W) : ∑ y, extra x y ≤ 1 := by
      rw [show (∑ y, extra x y) = (Finset.univ.filter (fun y => (3 : Fin 4) ∈ e x y)).card from
        (Finset.card_filter _ _).symm]
      apply Finset.card_le_one.mpr
      intro y hy z hz
      by_contra h
      exact Finset.disjoint_left.mp (ed x y z h) (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2
    have rem (x y : W) : m x y-(trim (e x y)).card = (if y = mate x then 1 else 0) + extra x y := by
      have h : (trim (e x y)).card + extra x y = r x y := (cnt (e x y)).trans (ec x y)
      have := split x y
      omega
    refine ⟨fun x y => trim (e x y),fun x y => congrArg trim (es x y),?_,?_,?_⟩
    · intro x y
      calc (trim (e x y)).card ≤ (e x y).card := by have h := cnt (e x y); omega
           _ = r x y := ec x y
           _ ≤ m x y := by rw [split x y]; exact Nat.le_add_right _ _
    · intro x
      simp_rw [rem x]
      simp [Finset.sum_add_distrib]
      have := exc x; omega
    · intro x y z h
      apply Finset.disjoint_left.mpr
      intro k hy hz
      exact Finset.disjoint_left.mp (ed x y z h) (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2

/-- A labeling by residues modulo seven, injective on each closed
neighborhood, gives a total coloring of a simple graph by endpoint sums. -/
theorem cyclic_seven {W : Type} (A : SimpleGraph W) (m : W → W → ℕ)
    (symm : ∀ x y, m x y = m y x) (simple : ∀ x y, m x y ≤ 1)
    (support : ∀ x y, A.Adj x y ↔ 0 < m x y) (l : W → Fin 7)
    (vertex : ∀ x y, A.Adj x y → l x ≠ l y)
    (localInj : ∀ x y z, A.Adj x y → A.Adj x z → y ≠ z → l y ≠ l z) :
    ∃ (vc : W → Fin 7) (e : W → W → Finset (Fin 7)),
      (∀ x y, e x y = e y x) ∧ (∀ x y, (e x y).card = m x y) ∧
      (∀ x y, A.Adj x y → vc x ≠ vc y) ∧ (∀ x y, vc x ∉ e x y) ∧
      (∀ x y z, y ≠ z → Disjoint (e x y) (e x z)) := by
  classical
  let e (x y : W) : Finset (Fin 7) := if 0 < m x y then {l x+l y} else ∅
  have dbl : ∀ a b : Fin 7, a+a=b+b → a=b := by decide
  refine ⟨fun x => l x+l x,e,?_,?_,?_,?_,?_⟩
  · intro x y; simp only [e,symm x y,add_comm (l x) (l y)]
  · intro x y
    by_cases h : 0 < m x y
    · have := simple x y; have v : m x y = 1 := by omega
      simp [e,v]
    · simp [e,Nat.eq_zero_of_not_pos h]
  · intro x y h eq; exact vertex x y h (dbl _ _ eq)
  · intro x y
    by_cases h : 0 < m x y
    · simpa [e,h] using vertex x y ((support x y).mpr h)
    · simp [e,h]
  · intro x y z neq
    by_cases hy : 0 < m x y
    · by_cases hz : 0 < m x z
      · simpa [e,hy,hz] using localInj x y z ((support x y).mpr hy) ((support x z).mpr hz) neq
      · simp [e,hz]
    · simp [e,hy]

/-- The full support needs at least five vertex colors. -/
def H1 : Prop :=
  ∀ (W : Type) [Fintype W] (A : SimpleGraph W) (m : W → W → ℕ),
    (∀ x y, m x y = m y x) → (∀ x, m x x = 0) →
    (∀ x, ∑ y, m x y = 5) → (∀ x y, A.Adj x y ↔ 0 < m x y) →
    ∀ (M : A.Subgraph), M.IsPerfectMatching → ∀ (r : W → W → ℕ) (c : W → Bool),
    let inside (a : W → W → ℕ) (x : W) : ℤ :=
      ∑ y, if c x = c y then (a x y : ℤ) else 0
    (∀ x y, M.Adj x y → r x y + 1 = m x y) →
    (∀ x y, ¬ M.Adj x y → r x y = m x y) →
    (∀ v, inside m v ≤ 2) →
    (∀ d : W → Bool, (∀ x y, 0 < r x y → c x ≠ c y → d x = d y) →
        ∀ x y, 0 < r x y → d x = d y) →
    (∀ v w, c v ≠ c w → 0 < r w v → inside r v < 2 ∨ inside r w < 2) →
    (¬ ∃ b : W → Bool, ∀ x y, 0 < r x y → b x ≠ b y) →
    (¬ ((∀ x y, m x y ≤ 1) ∧ ∃ l : W → Fin 7, (∀ x y, A.Adj x y → l x ≠ l y) ∧ (∀ x y z, A.Adj x y → A.Adj x z → y ≠ z → l y ≠ l z))) →
    (¬ (∃ v : W → Fin 4, ∀ x y, A.Adj x y → v x ≠ v y)) →
    ∃ (vc : W → Fin 7) (ec : W → W → Finset (Fin 7)),
      (∀ x y, ec x y = ec y x) ∧ (∀ x y, (ec x y).card = m x y) ∧
      (∀ x y, A.Adj x y → vc x ≠ vc y) ∧ (∀ x y, vc x ∉ ec x y) ∧
      (∀ x y z, y ≠ z → Disjoint (ec x y) (ec x z))

/-- Four vertex colors exist, but three edge classes cannot leave residual degree two. -/
def H2 : Prop :=
  ∀ (W : Type) [Fintype W] (A : SimpleGraph W) (m : W → W → ℕ),
    (∀ x y, m x y = m y x) → (∀ x, m x x = 0) →
    (∀ x, ∑ y, m x y = 5) → (∀ x y, A.Adj x y ↔ 0 < m x y) →
    ∀ (M : A.Subgraph), M.IsPerfectMatching → ∀ (r : W → W → ℕ) (c : W → Bool),
    let inside (a : W → W → ℕ) (x : W) : ℤ :=
      ∑ y, if c x = c y then (a x y : ℤ) else 0
    (∀ x y, M.Adj x y → r x y + 1 = m x y) →
    (∀ x y, ¬ M.Adj x y → r x y = m x y) →
    (∀ v, inside m v ≤ 2) →
    (∀ d : W → Bool, (∀ x y, 0 < r x y → c x ≠ c y → d x = d y) →
        ∀ x y, 0 < r x y → d x = d y) →
    (∀ v w, c v ≠ c w → 0 < r w v → inside r v < 2 ∨ inside r w < 2) →
    (¬ ∃ b : W → Bool, ∀ x y, 0 < r x y → b x ≠ b y) →
    (¬ ((∀ x y, m x y ≤ 1) ∧ ∃ l : W → Fin 7, (∀ x y, A.Adj x y → l x ≠ l y) ∧ (∀ x y z, A.Adj x y → A.Adj x z → y ≠ z → l y ≠ l z))) →
    (∃ v : W → Fin 4, ∀ x y, A.Adj x y → v x ≠ v y) →
    (¬ (∃ e : W → W → Finset (Fin 3), (∀ x y, e x y = e y x) ∧ (∀ x y, (e x y).card ≤ m x y) ∧
      (∀ x, (∑ y, (m x y-(e x y).card)) ≤ 2) ∧ (∀ x y z, y ≠ z → Disjoint (e x y) (e x z)))) →
    ∃ (vc : W → Fin 7) (ec : W → W → Finset (Fin 7)),
      (∀ x y, ec x y = ec y x) ∧ (∀ x y, (ec x y).card = m x y) ∧
      (∀ x y, A.Adj x y → vc x ≠ vc y) ∧ (∀ x y, vc x ∉ ec x y) ∧
      (∀ x y z, y ≠ z → Disjoint (ec x y) (ec x z))

theorem main : H1 → H2 → OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R2.H2 := by
  intro h1 h2 W _ A m ms ml md ss M matchM r c _insideDef onM offM inside connected strict
  classical
  have solve (v : W → Fin 4) (hv : ∀ x y, A.Adj x y → v x ≠ v y) (he : (∃ e : W → W → Finset (Fin 3), (∀ x y, e x y = e y x) ∧ (∀ x y, (e x y).card ≤ m x y) ∧
      (∀ x, (∑ y, (m x y-(e x y).card)) ≤ 2) ∧ (∀ x y z, y ≠ z → Disjoint (e x y) (e x z)))) : ∃ (vc : W → Fin 7) (ec : W → W → Finset (Fin 7)),
      (∀ x y, ec x y = ec y x) ∧ (∀ x y, (ec x y).card = m x y) ∧
      (∀ x y, A.Adj x y → vc x ≠ vc y) ∧ (∀ x y, vc x ∉ ec x y) ∧
      (∀ x y z, y ≠ z → Disjoint (ec x y) (ec x z)) := by
    obtain ⟨e,es,ec,de,ed⟩ := he
    exact three_classes A m ms ml ss v hv e es ec de ed
  by_cases hb : ∃ b : W → Bool, ∀ x y, 0 < r x y → b x ≠ b y
  · obtain ⟨b,hb'⟩ := hb
    obtain ⟨⟨v,hv⟩,he⟩ := bipartite_data A M matchM m r ms md ss onM offM b hb'
    exact solve v hv he
  by_cases hloc : ((∀ x y, m x y ≤ 1) ∧ ∃ l : W → Fin 7, (∀ x y, A.Adj x y → l x ≠ l y) ∧ (∀ x y z, A.Adj x y → A.Adj x z → y ≠ z → l y ≠ l z))
  · obtain ⟨simple,l,vl,il⟩ := hloc; exact cyclic_seven A m ms simple ss l vl il
  by_cases hc : (∃ v : W → Fin 4, ∀ x y, A.Adj x y → v x ≠ v y)
  · by_cases he : (∃ e : W → W → Finset (Fin 3), (∀ x y, e x y = e y x) ∧ (∀ x y, (e x y).card ≤ m x y) ∧
      (∀ x, (∑ y, (m x y-(e x y).card)) ≤ 2) ∧ (∀ x y z, y ≠ z → Disjoint (e x y) (e x z)))
    · obtain ⟨v,hv⟩ := hc; exact solve v hv he
    · exact h2 W A m ms ml md ss M matchM r c onM offM inside connected strict hb hloc hc he
  · exact h1 W A m ms ml md ss M matchM r c onM offM inside connected strict hb hloc hc

end OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R2_H2_R1
