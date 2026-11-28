import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1_H2_R1

-- Reduction WrittenOnTheWallII.GraphConjecture133.conjecture133.R1.H1.R1.H2.R1.H4.R1 of step WrittenOnTheWallII.GraphConjecture133.conjecture133.R1.H1.R1.H2.R1.H4
-- Credit: @chris01-dev

/-!
A sub-reduction of the radius-two step (gap at least four) of Written on the Wall II,
Conjecture 133.

Proved here, with no hypothesis: in a finite graph with no 4-cycle and no 5-cycle (as subgraphs,
triangles allowed), if the neighbourhood independence numbers sum to more than `g * n` with
`g ≥ 2`, then there is an induced path on `g + 3` vertices. Hence `l G ≤ path G - 2` for every such
graph with `path G ≥ 4`, which is the radius-two bound for all graphs without a 5-cycle.

Method. Deleting a vertex `v` lowers the sum of the local independence numbers by at most
`2 * lam v`, so vertices with `lam v ≤ g / 2` can be pruned while the sum stays above `g` times
the order. In the remaining vertex set every vertex has `lam > g / 2`, and one vertex `y` has
`lam y > g`. Take a longest induced path ending at `y`. At its other end `x` every neighbour is
blocked by a path vertex at distance two; without 4-cycles two neighbours are never blocked by
the same vertex, and without 5-cycles never by two consecutive path vertices, nor by the three
path vertices nearest to `x`. So the path has at least `2 * lam x + 1` vertices. When `g` is odd
this is one short, and the same count at `y` (where `lam y > g`) gives a free neighbour of `y`
that extends the path by one vertex.

What is left: the same step for graphs that contain a 5-cycle, split by whether the graph also
contains a triangle (H2) or not (H1, graphs of girth exactly five, where `l G` is the average
degree).
-/

namespace OMA.W133NoFive

open SimpleGraph

private def NoC4 {α : Type} (G : SimpleGraph α) : Prop :=
  ∀ a b c d : α, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a ≠ c → b ≠ d → False

private def NoC5 {α : Type} (G : SimpleGraph α) : Prop :=
  ∀ a b c d e : α, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj e a →
    a ≠ c → a ≠ d → b ≠ d → b ≠ e → c ≠ e → False

/-- `f 0, …, f (m - 1)` is an induced path inside `A`. -/
private def IP {α : Type} (G : SimpleGraph α) (A : Finset α) (f : ℕ → α) (m : ℕ) : Prop :=
  (∀ i, i < m → f i ∈ A) ∧ (∀ i j, i < m → j < m → f i = f j → i = j) ∧
  (∀ i j, i < m → j < m → (G.Adj (f i) (f j) ↔ i + 1 = j ∨ j + 1 = i))

/-- `W` is an independent set of neighbours of `v` inside `A`. -/
private def Fan {α : Type} (G : SimpleGraph α) (A : Finset α) (v : α) (W : Finset α) : Prop :=
  W ⊆ A ∧ (∀ x ∈ W, G.Adj v x) ∧ (∀ x ∈ W, ∀ y ∈ W, x ≠ y → ¬ G.Adj x y)

/-- `lam v` is the largest size of an independent set of neighbours of `v` inside `A`. -/
private def IsLam {α : Type} (G : SimpleGraph α) (A : Finset α) (lam : α → ℕ) : Prop :=
  ∀ v, (∀ W, Fan G A v W → W.card ≤ lam v) ∧ ∃ W, Fan G A v W ∧ W.card = lam v

private lemma exists_lam {α : Type} (G : SimpleGraph α) (A : Finset α) :
    ∃ lam : α → ℕ, IsLam G A lam := by
  classical
  have h : ∀ v, ∃ k, (∀ W, Fan G A v W → W.card ≤ k) ∧ ∃ W, Fan G A v W ∧ W.card = k := by
    intro v
    have hne : (A.powerset.filter (fun W => Fan G A v W)).Nonempty := by
      refine ⟨∅, ?_⟩
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.empty_subset _, Finset.empty_subset _, ?_, ?_⟩
      · intro x hx
        simp at hx
      · intro x hx
        simp at hx
    obtain ⟨W0, hW0, hmax⟩ := Finset.exists_max_image _ Finset.card hne
    rw [Finset.mem_filter] at hW0
    refine ⟨W0.card, ?_, W0, hW0.2, rfl⟩
    intro W hW
    apply hmax
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hW.1, hW⟩
  choose lam hlam using h
  exact ⟨lam, hlam⟩

/-- A set of naturals in a window of length `N` with no two consecutive elements has at most
`(N + 1) / 2` elements. -/
private lemma card_nonconsec (T : Finset ℕ) (c N : ℕ) (h1 : ∀ a ∈ T, c ≤ a ∧ a < c + N)
    (h2 : ∀ a ∈ T, ∀ b ∈ T, a + 1 ≠ b) : 2 * T.card ≤ N + 1 := by
  have h : T.card ≤ (Finset.range ((N + 1) / 2)).card := by
    refine Finset.card_le_card_of_injOn (fun a => (a - c) / 2) ?_ ?_
    · intro a ha
      have ha' : a ∈ T := ha
      have := h1 a ha'
      show (a - c) / 2 ∈ Finset.range ((N + 1) / 2)
      rw [Finset.mem_range]
      omega
    · intro a ha b hb hab
      have ha' : a ∈ T := ha
      have hb' : b ∈ T := hb
      have hab' : (a - c) / 2 = (b - c) / 2 := hab
      have := h1 a ha'
      have := h1 b hb'
      have := h2 a ha' b hb'
      have := h2 b hb' a ha'
      omega
  rw [Finset.card_range] at h
  omega

private lemma IP_rev {α : Type} (G : SimpleGraph α) (A : Finset α) (f : ℕ → α) (m : ℕ)
    (hP : IP G A f m) : IP G A (fun i => f (m - 1 - i)) m := by
  obtain ⟨hPA, hinj, hadj⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    show f (m - 1 - i) ∈ A
    exact hPA _ (by omega)
  · intro i j hi hj hij
    have hij' : f (m - 1 - i) = f (m - 1 - j) := hij
    have := hinj _ _ (by omega) (by omega) hij'
    omega
  · intro i j hi hj
    show G.Adj (f (m - 1 - i)) (f (m - 1 - j)) ↔ i + 1 = j ∨ j + 1 = i
    rw [hadj _ _ (by omega) (by omega)]
    omega

/-- The count at the end `f 0` of an induced path: either a vertex of the fan `W` extends the
path at that end, or the path has at least `2 * W.card + 1` vertices. -/
private lemma front {α : Type} (G : SimpleGraph α) (hC4 : NoC4 G) (hC5 : NoC5 G)
    (A : Finset α) (f : ℕ → α) (m : ℕ) (hP : IP G A f m) (hm : 2 ≤ m) (W : Finset α)
    (hW : Fan G A (f 0) W) :
    (∃ g : ℕ → α, IP G A g (m + 1) ∧ g m = f (m - 1)) ∨ W.card ≤ 1 ∨ 2 * W.card + 1 ≤ m := by
  classical
  obtain ⟨hPA, hinj, hadj⟩ := hP
  obtain ⟨hWA, hWadj, hWind⟩ := hW
  have hx1 : G.Adj (f 0) (f 1) := (hadj 0 1 (by omega) (by omega)).2 (Or.inl rfl)
  have hoff : ∀ w ∈ W, w ≠ f 1 → ∀ j, j < m → w ≠ f j := by
    intro w hw hw1 j hj hwj
    have h := hWadj w hw
    rw [hwj] at h
    have h2 := (hadj 0 j (by omega) hj).1 h
    have hj1 : j = 1 := by omega
    rw [hj1] at hwj
    exact hw1 hwj
  by_cases hext : ∃ w ∈ W, w ≠ f 1 ∧ ∀ i, 1 ≤ i → i < m → ¬ G.Adj w (f i)
  · left
    obtain ⟨w, hw, hw1, hfree⟩ := hext
    have hg0 : (fun i => if i = 0 then w else f (i - 1)) 0 = w := by simp
    have hgs : ∀ i, 0 < i → (fun i => if i = 0 then w else f (i - 1)) i = f (i - 1) := by
      intro i hi
      have hi0 : i ≠ 0 := by omega
      simp [hi0]
    generalize (fun i => if i = 0 then w else f (i - 1)) = g at hg0 hgs
    refine ⟨g, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro i hi
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · rw [h0, hg0]
        exact hWA hw
      · rw [hgs i h0]
        exact hPA _ (by omega)
    · intro i j hi hj hij
      rcases Nat.eq_zero_or_pos i with h0 | h0 <;> rcases Nat.eq_zero_or_pos j with h1 | h1
      · omega
      · rw [h0, hg0, hgs j h1] at hij
        exact absurd hij (hoff w hw hw1 (j - 1) (by omega))
      · rw [h1, hg0, hgs i h0] at hij
        exact absurd hij.symm (hoff w hw hw1 (i - 1) (by omega))
      · rw [hgs i h0, hgs j h1] at hij
        have := hinj (i - 1) (j - 1) (by omega) (by omega) hij
        omega
    · intro i j hi hj
      rcases Nat.eq_zero_or_pos i with h0 | h0 <;> rcases Nat.eq_zero_or_pos j with h1 | h1
      · rw [h0, h1]
        constructor
        · intro h
          exact (G.irrefl h).elim
        · intro h
          omega
      · rw [h0, hg0, hgs j h1]
        constructor
        · intro h
          by_contra hne
          exact hfree (j - 1) (by omega) (by omega) h
        · intro h
          have hj1 : j - 1 = 0 := by omega
          rw [hj1]
          exact (hWadj w hw).symm
      · rw [h1, hg0, hgs i h0]
        constructor
        · intro h
          by_contra hne
          exact hfree (i - 1) (by omega) (by omega) h.symm
        · intro h
          have hi1 : i - 1 = 0 := by omega
          rw [hi1]
          exact hWadj w hw
      · rw [hgs i h0, hgs j h1, hadj (i - 1) (j - 1) (by omega) (by omega)]
        omega
    · exact hgs m (by omega)
  · right
    push Not at hext
    have hbad : (W.filter (fun w => ¬ (w ≠ f 1 ∧ ¬ G.Adj w (f 1)))).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      by_contra hab
      have ha' : a = f 1 ∨ G.Adj a (f 1) := by
        by_contra h
        push Not at h
        exact ha.2 ⟨h.1, h.2⟩
      have hb' : b = f 1 ∨ G.Adj b (f 1) := by
        by_contra h
        push Not at h
        exact hb.2 ⟨h.1, h.2⟩
      rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
      · exact hab (ha'.trans hb'.symm)
      · rw [← ha'] at hb'
        exact hWind b hb.1 a ha.1 (Ne.symm hab) hb'
      · rw [← hb'] at ha'
        exact hWind a ha.1 b hb.1 hab ha'
      · exact hC4 (f 0) a (f 1) b (hWadj a ha.1) ha' hb'.symm (hWadj b hb.1).symm hx1.ne hab
    have hclean : ∀ w ∈ W.filter (fun w => w ≠ f 1 ∧ ¬ G.Adj w (f 1)),
        ∃ i, 4 ≤ i ∧ i < m ∧ G.Adj w (f i) := by
      intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨hwW, hw1, hwq⟩ := hw
      obtain ⟨i, hi1, him, hi⟩ := hext w hwW hw1
      refine ⟨i, ?_, him, hi⟩
      by_contra hlt
      have hcases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact hwq hi
      · exact hC4 (f 0) w (f 2) (f 1) (hWadj w hwW) hi
          ((hadj 2 1 (by omega) (by omega)).2 (Or.inr rfl)) hx1.symm
          (fun h => by have := hinj 0 2 (by omega) (by omega) h; omega) hw1
      · exact hC5 (f 0) w (f 3) (f 2) (f 1) (hWadj w hwW) hi
          ((hadj 3 2 (by omega) (by omega)).2 (Or.inr rfl))
          ((hadj 2 1 (by omega) (by omega)).2 (Or.inr rfl)) hx1.symm
          (fun h => by have := hinj 0 3 (by omega) (by omega) h; omega)
          (fun h => by have := hinj 0 2 (by omega) (by omega) h; omega)
          (hoff w hwW hw1 2 (by omega)) hw1
          (fun h => by have := hinj 3 1 (by omega) (by omega) h; omega)
    choose! b hb using hclean
    have hmemC : ∀ w, w ∈ W.filter (fun w => w ≠ f 1 ∧ ¬ G.Adj w (f 1)) → w ∈ W ∧ w ≠ f 1 := by
      intro w hw
      rw [Finset.mem_filter] at hw
      exact ⟨hw.1, hw.2.1⟩
    have hinjb : Set.InjOn b (W.filter (fun w => w ≠ f 1 ∧ ¬ G.Adj w (f 1)) : Finset α) := by
      intro w hw w' hw' hbb
      have hw2 := hmemC w hw
      have hw2' := hmemC w' hw'
      have e := hb w hw
      have e' := hb w' hw'
      by_contra hne
      rw [← hbb] at e'
      exact hC4 (f 0) w (f (b w)) w' (hWadj w hw2.1) e.2.2 e'.2.2.symm (hWadj w' hw2'.1).symm
        (fun h => by have := hinj 0 (b w) (by omega) (by omega) h; omega) hne
    have hTcard := Finset.card_image_of_injOn hinjb
    have h1 : ∀ a ∈ (W.filter (fun w => w ≠ f 1 ∧ ¬ G.Adj w (f 1))).image b,
        4 ≤ a ∧ a < 4 + (m - 4) := by
      intro a ha
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 ha
      have := hb w hw
      omega
    have h2 : ∀ a ∈ (W.filter (fun w => w ≠ f 1 ∧ ¬ G.Adj w (f 1))).image b,
        ∀ a' ∈ (W.filter (fun w => w ≠ f 1 ∧ ¬ G.Adj w (f 1))).image b, a + 1 ≠ a' := by
      intro a ha a' ha' h
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨w', hw', rfl⟩ := Finset.mem_image.1 ha'
      have hw2 := hmemC w hw
      have hw2' := hmemC w' hw'
      have e := hb w hw
      have e' := hb w' hw'
      have e1 := e'.2.2
      rw [← h] at e1
      have hlt : b w + 1 < m := by omega
      exact hC5 (f 0) w (f (b w)) (f (b w + 1)) w' (hWadj w hw2.1) e.2.2
        ((hadj (b w) (b w + 1) (by omega) hlt).2 (Or.inl rfl)) e1.symm (hWadj w' hw2'.1).symm
        (fun h => by have := hinj 0 (b w) (by omega) (by omega) h; omega)
        (fun h => by have := hinj 0 (b w + 1) (by omega) hlt h; omega)
        (hoff w hw2.1 hw2.2 (b w + 1) hlt)
        (fun hww => by rw [hww] at h; omega)
        (fun h => hoff w' hw2'.1 hw2'.2 (b w) (by omega) h.symm)
    have hT := card_nonconsec _ 4 (m - 4) h1 h2
    have hsplit := Finset.card_filter_add_card_filter_not (s := W)
      (fun w => w ≠ f 1 ∧ ¬ G.Adj w (f 1))
    by_cases hW1 : W.card ≤ 1
    · left
      exact hW1
    · right
      have hpos : 0 < (W.filter (fun w => w ≠ f 1 ∧ ¬ G.Adj w (f 1))).card := by omega
      obtain ⟨w, hw⟩ := Finset.card_pos.1 hpos
      have := hb w hw
      omega

/-- Deleting `v` lowers the sum of the local independence numbers by at most `2 * lam v`. -/
private lemma prune {α : Type} [DecidableEq α] (G : SimpleGraph α) (hC4 : NoC4 G)
    (A : Finset α) (v : α) (hv : v ∈ A) (lam lam' : α → ℕ)
    (hlam : IsLam G A lam) (hlam' : IsLam G (A.erase v) lam') :
    ∑ x ∈ A, lam x ≤ ∑ x ∈ A.erase v, lam' x + 2 * lam v := by
  classical
  have hloss : ∀ x ∈ A.erase v, lam x ≤ lam' x + 1 := by
    intro x hx
    obtain ⟨W, hW, hWc⟩ := (hlam x).2
    have hF : Fan G (A.erase v) x (W.erase v) := by
      refine ⟨?_, ?_, ?_⟩
      · intro y hy
        rw [Finset.mem_erase] at hy ⊢
        exact ⟨hy.1, hW.1 hy.2⟩
      · intro y hy
        exact hW.2.1 y (Finset.mem_of_mem_erase hy)
      · intro y hy z hz hyz
        exact hW.2.2 y (Finset.mem_of_mem_erase hy) z (Finset.mem_of_mem_erase hz) hyz
    have h1 := (hlam' x).1 _ hF
    have h2 : W.card - 1 ≤ (W.erase v).card := Finset.pred_card_le_card_erase
    omega
  have hkeep : ∀ x W, Fan G A x W → v ∉ W → W.card ≤ lam' x := by
    intro x W hW hvW
    apply (hlam' x).1
    exact ⟨fun y hy => Finset.mem_erase.2 ⟨fun h => hvW (h ▸ hy), hW.1 hy⟩, hW.2.1, hW.2.2⟩
  have hLadj : ∀ x ∈ (A.erase v).filter (fun x => lam' x < lam x), G.Adj v x := by
    intro x hx
    obtain ⟨-, hlt⟩ := Finset.mem_filter.1 hx
    by_contra hnadj
    obtain ⟨W, hW, hWc⟩ := (hlam x).2
    have := hkeep x W hW (fun h => hnadj (hW.2.1 v h).symm)
    omega
  have hLfan : Fan G A v ((A.erase v).filter (fun x => lam' x < lam x)) := by
    refine ⟨?_, hLadj, ?_⟩
    · intro x hx
      exact Finset.mem_of_mem_erase (Finset.mem_filter.1 hx).1
    · intro x hx y hy hxy hadj
      obtain ⟨-, hlt⟩ := Finset.mem_filter.1 hx
      have hyA := (Finset.mem_filter.1 hy).1
      have hvx := hLadj x hx
      have hvy := hLadj y hy
      obtain ⟨W, hW, hWc⟩ := (hlam x).2
      by_cases hvW : v ∈ W
      · have hyW : y ∉ W := fun h => hW.2.2 v hvW y h hvy.ne hvy
        have hyW' : y ∉ W.erase v := fun h => hyW (Finset.mem_of_mem_erase h)
        have hF : Fan G (A.erase v) x (insert y (W.erase v)) := by
          refine ⟨?_, ?_, ?_⟩
          · intro z hz
            rcases Finset.mem_insert.1 hz with hzy | hz
            · rw [hzy]
              exact hyA
            · rw [Finset.mem_erase] at hz ⊢
              exact ⟨hz.1, hW.1 hz.2⟩
          · intro z hz
            rcases Finset.mem_insert.1 hz with hzy | hz
            · rw [hzy]
              exact hadj
            · exact hW.2.1 z (Finset.mem_of_mem_erase hz)
          · intro z hz z' hz' hne
            rcases Finset.mem_insert.1 hz with hzy | hz <;>
              rcases Finset.mem_insert.1 hz' with hzy' | hz'
            · exact absurd (hzy.trans hzy'.symm) hne
            · rw [hzy]
              intro h
              exact hC4 x v y z' (hW.2.1 v hvW) hvy h
                (hW.2.1 z' (Finset.mem_of_mem_erase hz')).symm hadj.ne
                (Finset.mem_erase.1 hz').1.symm
            · rw [hzy']
              intro h
              exact hC4 x v y z (hW.2.1 v hvW) hvy h.symm
                (hW.2.1 z (Finset.mem_of_mem_erase hz)).symm hadj.ne
                (Finset.mem_erase.1 hz).1.symm
            · exact hW.2.2 z (Finset.mem_of_mem_erase hz) z' (Finset.mem_of_mem_erase hz') hne
        have h1 := (hlam' x).1 _ hF
        have h2 : (insert y (W.erase v)).card = (W.erase v).card + 1 :=
          Finset.card_insert_of_notMem hyW'
        have h3 : (W.erase v).card = W.card - 1 := Finset.card_erase_of_mem hvW
        have h4 : 0 < W.card := Finset.card_pos.2 ⟨v, hvW⟩
        omega
      · have := hkeep x W hW hvW
        omega
  have hLcard := (hlam v).1 _ hLfan
  have hs : ∑ x ∈ A.erase v, lam x ≤
      ∑ x ∈ A.erase v, lam' x + ((A.erase v).filter (fun x => lam' x < lam x)).card := by
    have hpt : ∀ x ∈ A.erase v, lam x ≤ lam' x + (if lam' x < lam x then 1 else 0) := by
      intro x hx
      have := hloss x hx
      split_ifs <;> omega
    calc ∑ x ∈ A.erase v, lam x
        ≤ ∑ x ∈ A.erase v, (lam' x + (if lam' x < lam x then 1 else 0)) := Finset.sum_le_sum hpt
      _ = ∑ x ∈ A.erase v, lam' x + ∑ x ∈ A.erase v, (if lam' x < lam x then 1 else 0) :=
          Finset.sum_add_distrib
      _ = ∑ x ∈ A.erase v, lam' x + ((A.erase v).filter (fun x => lam' x < lam x)).card := by
          rw [Finset.card_filter]
  have hsplit : lam v + ∑ x ∈ A.erase v, lam x = ∑ x ∈ A, lam x := Finset.add_sum_erase A lam hv
  omega

/-- The induced path theorem for graphs with no 4-cycle and no 5-cycle. -/
private theorem core {α : Type} [DecidableEq α] (G : SimpleGraph α) (hC4 : NoC4 G) (hC5 : NoC5 G)
    (d g : ℕ) (hd : 1 ≤ d) (hg : g = 2 * d ∨ g = 2 * d + 1) :
    ∀ (k : ℕ) (A : Finset α), A.card = k → ∀ lam : α → ℕ, IsLam G A lam →
      g * A.card < ∑ v ∈ A, lam v → ∃ (f : ℕ → α) (m : ℕ), IP G A f m ∧ g + 3 ≤ m := by
  classical
  intro k
  induction k with
  | zero =>
    intro A hA lam _ hsum
    rw [Finset.card_eq_zero] at hA
    subst hA
    simp at hsum
  | succ k ih =>
    intro A hA lam hlam hsum
    by_cases hlow : ∃ v ∈ A, lam v ≤ d
    · obtain ⟨v, hv, hvd⟩ := hlow
      obtain ⟨lam', hlam'⟩ := exists_lam G (A.erase v)
      have hcard : (A.erase v).card = k := by
        rw [Finset.card_erase_of_mem hv, hA]
        rfl
      have hpr := prune G hC4 A v hv lam lam' hlam hlam'
      have hsum' : g * (A.erase v).card < ∑ x ∈ A.erase v, lam' x := by
        rw [hcard]
        rw [hA] at hsum
        have h3 : g * (k + 1) = g * k + g := by ring
        rw [h3] at hsum
        rcases hg with hg | hg <;> omega
      obtain ⟨f, m, hP, hm⟩ := ih (A.erase v) hcard lam' hlam' hsum'
      exact ⟨f, m, ⟨fun i hi => Finset.mem_of_mem_erase (hP.1 i hi), hP.2.1, hP.2.2⟩, hm⟩
    · push Not at hlow
      have hy : ∃ y ∈ A, g < lam y := by
        by_contra hno
        push Not at hno
        have h1 := Finset.sum_le_card_nsmul A lam g hno
        rw [smul_eq_mul, Nat.mul_comm] at h1
        exact absurd hsum (not_lt.2 h1)
      obtain ⟨y, hyA, hyg⟩ := hy
      have hQ1 : ∃ f : ℕ → α, IP G A f 1 ∧ f (1 - 1) = y := by
        refine ⟨fun _ => y, ⟨fun _ _ => hyA, ?_, ?_⟩, rfl⟩
        · intro i j hi hj _
          omega
        · intro i j hi hj
          constructor
          · intro h
            exact (G.irrefl h).elim
          · intro h
            omega
      have hQb : ∀ m, (∃ f : ℕ → α, IP G A f m ∧ f (m - 1) = y) → m ≤ A.card := by
        rintro m ⟨f, ⟨hPA, hinj, -⟩, -⟩
        have h := Finset.card_le_card_of_injOn (s := Finset.range m) (t := A) f
          (by
            intro i hi
            have hi' : i < m := by simpa using hi
            show f i ∈ A
            exact hPA i hi')
          (by
            intro i hi j hj hij
            have hi' : i < m := by simpa using hi
            have hj' : j < m := by simpa using hj
            exact hinj i j hi' hj' hij)
        rwa [Finset.card_range] at h
      have hQM := Nat.findGreatest_spec (P := fun m => ∃ f : ℕ → α, IP G A f m ∧ f (m - 1) = y)
        (hQb 1 hQ1) hQ1
      have hmax : ∀ m, (∃ f : ℕ → α, IP G A f m ∧ f (m - 1) = y) →
          m ≤ Nat.findGreatest (fun m => ∃ f : ℕ → α, IP G A f m ∧ f (m - 1) = y) A.card :=
        fun m hm => Nat.le_findGreatest (hQb m hm) hm
      generalize Nat.findGreatest (fun m => ∃ f : ℕ → α, IP G A f m ∧ f (m - 1) = y) A.card = M
        at hQM hmax
      obtain ⟨f, hP, hfy⟩ := hQM
      have hM1 : 1 ≤ M := hmax 1 hQ1
      obtain ⟨W, hW, hWc⟩ := (hlam (f 0)).2
      have hf0 : f 0 ∈ A := hP.1 0 (by omega)
      have hWd : d + 1 ≤ W.card := by
        rw [hWc]
        exact hlow (f 0) hf0
      have hM2 : 2 ≤ M := by
        by_contra hlt
        have hM : M = 1 := by omega
        obtain ⟨w, hw⟩ := Finset.card_pos.1 (by omega : 0 < W.card)
        have hf0y : f 0 = y := by
          rw [← hfy, hM]
        have hwy : G.Adj y w := hf0y ▸ hW.2.1 w hw
        have hQ2 : ∃ f : ℕ → α, IP G A f 2 ∧ f (2 - 1) = y := by
          refine ⟨fun i => if i = 0 then w else y, ⟨?_, ?_, ?_⟩, ?_⟩
          · intro i _
            by_cases h : i = 0
            · simp [h, hW.1 hw]
            · simp [h, hyA]
          · intro i j hi hj hij
            by_cases h : i = 0 <;> by_cases h' : j = 0
            · omega
            · simp [h, h'] at hij
              exact absurd hij hwy.ne'
            · simp [h, h'] at hij
              exact absurd hij hwy.ne
            · omega
          · intro i j hi hj
            by_cases h : i = 0 <;> by_cases h' : j = 0
            · simp [h, h']
            · have hj1 : j = 1 := by omega
              simp [h, hj1, hwy.symm]
            · have hi1 : i = 1 := by omega
              simp [h', hi1, hwy]
            · have hi1 : i = 1 := by omega
              have hj1 : j = 1 := by omega
              simp [hi1, hj1]
          · simp
        have := hmax 2 hQ2
        omega
      rcases front G hC4 hC5 A f M hP hM2 W hW with ⟨g', hg', hg'y⟩ | hW1 | hWM
      · exfalso
        have hQ : ∃ f : ℕ → α, IP G A f (M + 1) ∧ f (M + 1 - 1) = y := by
          refine ⟨g', hg', ?_⟩
          rw [Nat.add_sub_cancel, hg'y, hfy]
        have := hmax _ hQ
        omega
      · omega
      · have hMd : 2 * d + 3 ≤ M := by omega
        rcases hg with hg | hg
        · exact ⟨f, M, hP, by omega⟩
        · by_cases hbig : 2 * d + 4 ≤ M
          · exact ⟨f, M, hP, by omega⟩
          · have hrev := IP_rev G A f M hP
            obtain ⟨Y, hY, hYc⟩ := (hlam y).2
            have hY' : Fan G A ((fun i => f (M - 1 - i)) 0) Y := by
              show Fan G A (f (M - 1 - 0)) Y
              rw [Nat.sub_zero, hfy]
              exact hY
            rcases front G hC4 hC5 A _ M hrev hM2 Y hY' with ⟨g', hg', -⟩ | hY1 | hYM
            · exact ⟨g', M + 1, hg', by omega⟩
            · omega
            · omega

private lemma isLam_univ {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) :
    IsLam G Finset.univ (indepNeighborsCard G) := by
  intro v
  constructor
  · intro W hW
    exact OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.card_le_indepNeighborsCard
      G v W hW.2.1
      (fun x hx y hy hxy => hW.2.2 x (Finset.mem_coe.1 hx) y (Finset.mem_coe.1 hy) hxy)
  · obtain ⟨S, hS, hI, hc⟩ :=
      OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.exists_indepNeighbors G v
    exact ⟨S, ⟨Finset.subset_univ _, hS,
      fun x hx y hy hxy => hI (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) hxy⟩, hc⟩

/-- No 4-cycle, no 5-cycle and an induced path on six vertices: `l G ≤ path G - 2`. -/
private theorem noFive_bound {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    (hC4 : NoC4 G) (hC5 : NoC5 G) (hp : 6 ≤ SimpleGraph.path G) :
    (2 : ℝ) + SimpleGraph.l G ≤ (SimpleGraph.path G : ℝ) := by
  classical
  have key : ∑ v, indepNeighborsCard G v ≤ (SimpleGraph.path G - 2) * Fintype.card α := by
    by_contra hlt
    push Not at hlt
    obtain ⟨f, m, hP, hm⟩ := core G hC4 hC5 ((SimpleGraph.path G - 2) / 2) (SimpleGraph.path G - 2)
      (by omega) (by omega) (Finset.univ.card) Finset.univ rfl (indepNeighborsCard G)
      (isLam_univ G) (by rw [Finset.card_univ]; exact hlt)
    have := OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1.le_path_of_fun
      G f m hP.2.1 hP.2.2
    omega
  have hkey : (∑ v, (indepNeighborsCard G v : ℝ)) ≤
      ((SimpleGraph.path G : ℝ) - 2) * Fintype.card α := by
    have h : ((∑ v, indepNeighborsCard G v : ℕ) : ℝ) ≤
        (((SimpleGraph.path G - 2) * Fintype.card α : ℕ) : ℝ) := by exact_mod_cast key
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ SimpleGraph.path G), Nat.cast_sum] at h
    exact_mod_cast h
  unfold SimpleGraph.l averageIndepNeighbors indepNeighbors
  by_cases hn : Fintype.card α = 0
  · have hp' : (6 : ℝ) ≤ (SimpleGraph.path G : ℝ) := by exact_mod_cast hp
    simp only [hn, Nat.cast_zero, div_zero]
    linarith
  · have hpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [← le_sub_iff_add_le', div_le_iff₀ hpos]
    exact hkey

end OMA.W133NoFive

namespace OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1_H2_R1_H4_R1

open SimpleGraph

/-- The radius-two step for graphs of girth exactly five: a 5-cycle and no triangle. -/
def H1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    (¬ ∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    (∃ a b c d e : α, a ≠ c ∧ a ≠ d ∧ b ≠ d ∧ b ≠ e ∧ c ≠ e ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e a) →
    (¬ ∃ a b c : α, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) →
    G.radius.toNat = 2 → 6 ≤ G.path →
    (∀ c, G.eccent c = G.radius → G.path - 2 ≤ Nat.card (G.neighborSet c)) →
    (∃ v, G.path < G.radius.toNat + G.indepNeighborsCard v) →
    (G.path - G.radius.toNat) * Fintype.card α < 2 * Nat.card G.edgeSet →
    (G.radius.toNat : ℝ) + G.l ≤ (G.path : ℝ)

/-- The radius-two step for graphs with a 5-cycle and a triangle. -/
def H2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    (¬ ∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    (∃ a b c d e : α, a ≠ c ∧ a ≠ d ∧ b ≠ d ∧ b ≠ e ∧ c ≠ e ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e a) →
    (∃ a b c : α, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) →
    G.radius.toNat = 2 → 6 ≤ G.path →
    (∀ c, G.eccent c = G.radius → G.path - 2 ≤ Nat.card (G.neighborSet c)) →
    (∃ v, G.path < G.radius.toNat + G.indepNeighborsCard v) →
    (G.path - G.radius.toNat) * Fintype.card α < 2 * Nat.card G.edgeSet →
    (G.radius.toNat : ℝ) + G.l ≤ (G.path : ℝ)

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1_H2_R1.H4 := by
  intro h1 h2 α _ _ _ G hconn hC4 hr hp hcen hv hdense
  by_cases h5 : ∃ a b c d e : α, a ≠ c ∧ a ≠ d ∧ b ≠ d ∧ b ≠ e ∧ c ≠ e ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e a
  · by_cases h3 : ∃ a b c : α, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a
    · exact h2 G hconn hC4 h5 h3 hr hp hcen hv hdense
    · exact h1 G hconn hC4 h5 h3 hr hp hcen hv hdense
  · have hb := OMA.W133NoFive.noFive_bound G
      (fun a b c d hab hbc hcd hda hac hbd =>
        hC4 ⟨a, b, c, d, hab.ne, hac, hda.ne.symm, hbc.ne, hbd, hcd.ne, hab, hbc, hcd, hda⟩)
      (fun a b c d e hab hbc hcd hde hea hac had hbd hbe hce =>
        h5 ⟨a, b, c, d, e, hac, had, hbd, hbe, hce, hab, hbc, hcd, hde, hea⟩) hp
    rw [hr]
    exact_mod_cast hb

end OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1_H2_R1_H4_R1
