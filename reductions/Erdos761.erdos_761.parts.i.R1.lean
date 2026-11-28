import FormalConjectures.ErdosProblems.«761»
import Mathlib

-- Reduction Erdos761.erdos_761.parts.i.R1 of Erdős Problem 761 — i
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
What `main` proves: graphs with a large clique have large dichromatic number.

Let `T_r` be the `r`-th lexicographic power of the cyclic triangle: its vertices are the words
`x : Fin r → Fin 3`, and `x → y` when, at the first index `i` where they differ,
`y i = x i + 1` in `ZMod 3` style arithmetic on `Fin 3`. It is a tournament (`tr_tournament`). A set
of words with no directed triangle has at most `2 ^ r` elements (`cyc_bound`): if all three first
letters occur, one word of each first letter forms a directed triangle, and each of the two
remaining classes is a copy of `T_(r-1)`.

If `G` contains a clique on `3 ^ r` vertices, orient that clique as `T_r` and every other edge by a
fixed well order. In a colouring with `j` colours and `j 2 ^ r < 3 ^ r`, some colour class holds
more than `2 ^ r` clique vertices, hence a directed triangle (`clique_not_dicolorable`). With
`r = 2 k` (`k 4 ^ k < 9 ^ k`), every finite graph that is not `K_(9^k)`-free has dichromatic number
at least `k`. The remaining graphs have bounded clique number; they are moved to `Fin n` by an
isomorphism, which keeps cliques and the chromatic number, and the dichromatic number of the copy
is a lower bound for that of the original (`dicolorable_comap`).

What is left is the Erdős and Neumann-Lara question for graphs of bounded clique number: H1 is its
first open case, dichromatic number at least 3, and H2 is every `k ≥ 4`.
-/

namespace OMA.R_Erdos761_erdos_761_parts_i_R1

/-- For every `w` there is `m` such that every finite `K_w`-free graph with chromatic number at
least `m` has dichromatic number at least `3`. -/
def H1 : Prop :=
  ∀ w : ℕ, ∃ m : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree w →
    (m : ℕ∞) ≤ G.chromaticNumber → (3 : ℕ∞) ≤ Erdos761.dichromaticNumber G

/-- For every `k ≥ 4` and every `w` there is `m` such that every finite `K_w`-free graph with
chromatic number at least `m` has dichromatic number at least `k`. -/
def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ w : ℕ, ∃ m : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree w →
    (m : ℕ∞) ≤ G.chromaticNumber → (k : ℕ∞) ≤ Erdos761.dichromaticNumber G


/-- Two first-difference indices of the same pair agree. -/
lemma first_diff_unique {r : ℕ} {x y : Fin r → Fin 3} {i i' : Fin r}
    (h1 : ∀ j, j < i → x j = y j) (h1' : x i ≠ y i)
    (h2 : ∀ j, j < i' → x j = y j) (h2' : x i' ≠ y i') : i = i' := by
  rcases lt_trichotomy i i' with h | h | h
  · exact absurd (h2 i h) h1'
  · exact h
  · exact absurd (h1 i' h) h2'

/-- Distinct words have a first index where they differ. -/
lemma exists_first_diff {r : ℕ} {x y : Fin r → Fin 3} (hxy : x ≠ y) :
    ∃ i, (∀ j, j < i → x j = y j) ∧ x i ≠ y i := by
  classical
  have hs : (Finset.univ.filter (fun j => x j ≠ y j)).Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  refine ⟨(Finset.univ.filter (fun j => x j ≠ y j)).min' hs, ?_, ?_⟩
  · intro j hj
    by_contra hne
    have hmem : j ∈ Finset.univ.filter (fun j => x j ≠ y j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    exact absurd (Finset.min'_le _ _ hmem) (not_le.mpr hj)
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hs)).2

/-- The lexicographic power of the cyclic triangle is a tournament. -/
lemma tr_tournament {r : ℕ} {x y : Fin r → Fin 3} (hxy : x ≠ y) :
    (∃ i, (∀ j, j < i → x j = y j) ∧ y i = x i + 1) ↔
      ¬ (∃ i, (∀ j, j < i → y j = x j) ∧ x i = y i + 1) := by
  obtain ⟨i0, h0, h0'⟩ := exists_first_diff hxy
  have hsucc : ∀ a : Fin 3, a + 1 ≠ a := by decide
  have key : ∀ a b : Fin 3, a ≠ b → (b = a + 1 ↔ ¬ a = b + 1) := by decide
  have e1 : (∃ i, (∀ j, j < i → x j = y j) ∧ y i = x i + 1) ↔ y i0 = x i0 + 1 := by
    constructor
    · rintro ⟨i, hi, hi'⟩
      have hne : x i ≠ y i := by
        rw [hi']
        exact fun h => hsucc (x i) h.symm
      rw [← first_diff_unique h0 h0' hi hne] at hi'
      exact hi'
    · intro h
      exact ⟨i0, h0, h⟩
  have e2 : (∃ i, (∀ j, j < i → y j = x j) ∧ x i = y i + 1) ↔ x i0 = y i0 + 1 := by
    constructor
    · rintro ⟨i, hi, hi'⟩
      have hne : x i ≠ y i := by
        rw [hi']
        exact hsucc (y i)
      have hi2 : ∀ j, j < i → x j = y j := fun j hj => (hi j hj).symm
      rw [← first_diff_unique h0 h0' hi2 hne] at hi'
      exact hi'
    · intro h
      exact ⟨i0, fun j hj => (h0 j hj).symm, h⟩
  rw [e1, e2]
  exact key _ _ h0'

/-- No word beats itself. -/
lemma tr_irrefl {r : ℕ} (x : Fin r → Fin 3) :
    ¬ (∃ i, (∀ j, j < i → x j = x j) ∧ x i = x i + 1) := by
  rintro ⟨i, -, hi⟩
  have hsucc : ∀ a : Fin 3, a + 1 ≠ a := by decide
  exact hsucc (x i) hi.symm

/-- Words with the same first letter compare like their tails. -/
lemma tr_cons {r : ℕ} (a : Fin 3) (u v : Fin r → Fin 3) :
    (∃ i, (∀ j, j < i → (Fin.cons a u : Fin (r + 1) → Fin 3) j = (Fin.cons a v : Fin (r + 1) → Fin 3) j) ∧
        (Fin.cons a v : Fin (r + 1) → Fin 3) i = (Fin.cons a u : Fin (r + 1) → Fin 3) i + 1) ↔
      ∃ i, (∀ j, j < i → u j = v j) ∧ v i = u i + 1 := by
  have hsucc : ∀ a : Fin 3, a + 1 ≠ a := by decide
  constructor
  · rintro ⟨i, hi, hi'⟩
    induction i using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero] at hi'
      exact absurd hi'.symm (hsucc a)
    | succ i =>
      simp only [Fin.cons_succ] at hi'
      refine ⟨i, fun j hj => ?_, hi'⟩
      have := hi j.succ (Fin.succ_lt_succ_iff.mpr hj)
      simpa only [Fin.cons_succ] using this
  · rintro ⟨i, hi, hi'⟩
    refine ⟨i.succ, fun j hj => ?_, by simpa only [Fin.cons_succ] using hi'⟩
    induction j using Fin.cases with
    | zero => simp only [Fin.cons_zero]
    | succ j =>
      simp only [Fin.cons_succ]
      exact hi j (Fin.succ_lt_succ_iff.mp hj)

/-- A set of words with no cyclic triangle has at most `2 ^ r` elements. -/
lemma cyc_bound : ∀ (r : ℕ) (X : Finset (Fin r → Fin 3)),
    (∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X,
      ¬ ((∃ i, (∀ j, j < i → x j = y j) ∧ y i = x i + 1) ∧
        (∃ i, (∀ j, j < i → y j = z j) ∧ z i = y i + 1) ∧
        (∃ i, (∀ j, j < i → z j = x j) ∧ x i = z i + 1))) →
    X.card ≤ 2 ^ r := by
  intro r
  induction r with
  | zero =>
    intro X _
    calc X.card ≤ Fintype.card (Fin 0 → Fin 3) := Finset.card_le_univ X
      _ = 2 ^ 0 := by simp
  | succ r ih =>
    intro X hX
    classical
    -- the three classes by first letter
    have hfib : ∀ a : Fin 3, (X.filter (fun x => x 0 = a)).card ≤ 2 ^ r := by
      intro a
      have hinj : Set.InjOn Fin.tail (X.filter (fun x => x 0 = a) : Set (Fin (r + 1) → Fin 3)) := by
        intro x hx y hy hxy
        have hx0 : x 0 = a := (Finset.mem_filter.mp hx).2
        have hy0 : y 0 = a := (Finset.mem_filter.mp hy).2
        rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, hx0, hy0, hxy]
      rw [← Finset.card_image_of_injOn hinj]
      apply ih
      intro u hu v hv w hw htri
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      have hx0 : x 0 = a := (Finset.mem_filter.mp hx).2
      have hy0 : y 0 = a := (Finset.mem_filter.mp hy).2
      have hz0 : z 0 = a := (Finset.mem_filter.mp hz).2
      apply hX x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 z
        (Finset.mem_filter.mp hz).1
      rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, ← Fin.cons_self_tail z, hx0, hy0, hz0,
        tr_cons, tr_cons, tr_cons]
      exact htri
    -- one class is empty
    have hempty : ∃ a : Fin 3, X.filter (fun x => x 0 = a) = ∅ := by
      by_contra hne
      push Not at hne
      obtain ⟨x, hx⟩ := hne 0
      obtain ⟨y, hy⟩ := hne 1
      obtain ⟨z, hz⟩ := hne 2
      have hx0 : x 0 = 0 := (Finset.mem_filter.mp hx).2
      have hy0 : y 0 = 1 := (Finset.mem_filter.mp hy).2
      have hz0 : z 0 = 2 := (Finset.mem_filter.mp hz).2
      apply hX x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 z
        (Finset.mem_filter.mp hz).1
      refine ⟨⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), ?_⟩,
        ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), ?_⟩,
        ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), ?_⟩⟩
      · rw [hx0, hy0]
        decide
      · rw [hy0, hz0]
        decide
      · rw [hz0, hx0]
        decide
    have hsum : X.card = (X.filter (fun x => x 0 = 0)).card + (X.filter (fun x => x 0 = 1)).card +
        (X.filter (fun x => x 0 = 2)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin (r + 1) → Fin 3 => x 0)
        (t := Finset.univ) (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _)), Fin.sum_univ_three]
    obtain ⟨a, ha⟩ := hempty
    have h0 := hfib 0
    have h1 := hfib 1
    have h2 := hfib 2
    rw [pow_succ]
    fin_cases a
    · simp only [Fin.zero_eta] at ha
      rw [ha, Finset.card_empty] at hsum
      omega
    · simp only [Fin.mk_one] at ha
      rw [ha, Finset.card_empty] at hsum
      omega
    · have ha' : X.filter (fun x => x 0 = 2) = ∅ := ha
      rw [ha', Finset.card_empty] at hsum
      omega

/-- A graph that contains the words of length `r` as a clique is not `j`-dicolourable once
`j * 2 ^ r < 3 ^ r`: orient the clique as the lexicographic power of the cyclic triangle. -/
lemma clique_not_dicolorable {V : Type*} (G : SimpleGraph V) (r j : ℕ)
    (e : (Fin r → Fin 3) → V) (he : Function.Injective e)
    (hadj : ∀ x y, x ≠ y → G.Adj (e x) (e y)) (hj : j * 2 ^ r < 3 ^ r) :
    ¬ Erdos761.Dicolorable G j := by
  classical
  intro hdc
  let _ : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  have : Nonempty (Fin r → Fin 3) := ⟨fun _ => 0⟩
  have hinv_e : ∀ x, Function.invFun e (e x) = x := fun x => Function.leftInverse_invFun he x
  let R : V → V → Prop := fun u v =>
    if u ∈ Set.range e ∧ v ∈ Set.range e then
      ∃ i, (∀ j, j < i → Function.invFun e u j = Function.invFun e v j) ∧
        Function.invFun e v i = Function.invFun e u i + 1
    else u < v
  let D : Digraph V := ⟨fun u v => G.Adj u v ∧ R u v⟩
  have hD : D.IsOrientation G := by
    refine ⟨fun u v h => h.1, fun u v huv => ?_⟩
    have hvu : G.Adj v u := huv.symm
    have hne : u ≠ v := huv.ne
    show (G.Adj u v ∧ R u v) ↔ ¬ (G.Adj v u ∧ R v u)
    simp only [huv, hvu, true_and]
    by_cases hr : u ∈ Set.range e ∧ v ∈ Set.range e
    · have hr' : v ∈ Set.range e ∧ u ∈ Set.range e := ⟨hr.2, hr.1⟩
      simp only [R, if_pos hr, if_pos hr']
      obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hr
      rw [hinv_e, hinv_e]
      exact tr_tournament (fun h => hne (congrArg e h))
    · have hr' : ¬ (v ∈ Set.range e ∧ u ∈ Set.range e) := fun h => hr ⟨h.2, h.1⟩
      simp only [R, if_neg hr, if_neg hr']
      constructor
      · intro h h'
        exact lt_asymm h h'
      · intro h
        rcases lt_or_gt_of_ne hne with h1 | h1
        · exact h1
        · exact absurd h1 h
  have dstep : ∀ a b : Fin r → Fin 3, (∃ i, (∀ j, j < i → a j = b j) ∧ b i = a i + 1) →
      D.Adj (e a) (e b) := by
    intro a b hab
    have hne : a ≠ b := by
      rintro rfl
      exact tr_irrefl a hab
    refine ⟨hadj a b hne, ?_⟩
    show R (e a) (e b)
    simp only [R, if_pos (⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ : e a ∈ Set.range e ∧ e b ∈ Set.range e)]
    rw [hinv_e, hinv_e]
    exact hab
  obtain ⟨c, hc⟩ := hdc D hD
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := (Finset.univ : Finset (Fin r → Fin 3))) (t := (Finset.univ : Finset (Fin j)))
    (f := fun x => c (e x)) (n := 2 ^ r) (fun _ _ => Finset.mem_univ _)
    (by rw [Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin]; exact hj)
  refine absurd (cyc_bound r (Finset.univ.filter (fun x => c (e x) = i)) ?_) (not_le.mpr hi)
  intro x hx y hy z hz htri
  obtain ⟨hxy, hyz, hzx⟩ := htri
  have hxc : c (e x) = i := (Finset.mem_filter.mp hx).2
  have hyc : c (e y) = i := (Finset.mem_filter.mp hy).2
  have hzc : c (e z) = i := (Finset.mem_filter.mp hz).2
  apply hc i (e x)
  exact Relation.TransGen.tail (Relation.TransGen.tail
    (Relation.TransGen.single ⟨hxc, hyc, dstep x y hxy⟩) ⟨hyc, hzc, dstep y z hyz⟩)
    ⟨hzc, hxc, dstep z x hzx⟩

/-- Dicolourability passes to an isomorphic copy on `Fin n`. -/
lemma dicolorable_comap {V : Type*} (G : SimpleGraph V) {n : ℕ} (e : Fin n ≃ V) {j : ℕ}
    (h : Erdos761.Dicolorable G j) : Erdos761.Dicolorable (G.comap e) j := by
  intro D' hD'
  let D : Digraph V := ⟨fun u v => D'.Adj (e.symm u) (e.symm v)⟩
  have hD : D.IsOrientation G := by
    refine ⟨fun u v huv => ?_, fun u v huv => ?_⟩
    · have := hD'.1 _ _ huv
      simpa [SimpleGraph.comap_adj] using this
    · exact hD'.2 (e.symm u) (e.symm v) (by simpa [SimpleGraph.comap_adj] using huv)
  obtain ⟨c, hc⟩ := h D hD
  refine ⟨fun x => c (e x), fun i x hx => ?_⟩
  apply hc i (e x)
  have hlift : ∀ a b : Fin n, Relation.TransGen
      (fun a b => a ∈ {v | c (e v) = i} ∧ b ∈ {v | c (e v) = i} ∧ D'.Adj a b) a b →
      Relation.TransGen (fun u v => u ∈ {v | c v = i} ∧ v ∈ {v | c v = i} ∧ D.Adj u v)
        (e a) (e b) := by
    intro a b hab
    induction hab with
    | single h =>
      refine Relation.TransGen.single ⟨h.1, h.2.1, ?_⟩
      show D'.Adj (e.symm (e _)) (e.symm (e _))
      simpa using h.2.2
    | tail _ h ih =>
      refine ih.tail ⟨h.1, h.2.1, ?_⟩
      show D'.Adj (e.symm (e _)) (e.symm (e _))
      simpa using h.2.2
  exact hlift x x hx

/-- The dichromatic number of an isomorphic copy on `Fin n` is a lower bound. -/
lemma dichromatic_of_comap {V : Type*} (G : SimpleGraph V) {n : ℕ} (e : Fin n ≃ V) {k : ℕ}
    (h : (k : ℕ∞) ≤ Erdos761.dichromaticNumber (G.comap e)) :
    (k : ℕ∞) ≤ Erdos761.dichromaticNumber G := by
  unfold Erdos761.dichromaticNumber at h ⊢
  exact le_iInf₂ fun j hj => h.trans (iInf₂_le j (dicolorable_comap G e hj))

/-- `k 4 ^ k < 9 ^ k`, written with `2 ^ (2 k)` and `3 ^ (2 k)`. -/
lemma pow_bound (k : ℕ) : k * 2 ^ (2 * k) < 3 ^ (2 * k) := by
  rw [pow_mul, pow_mul]
  norm_num
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      norm_num
    · have h4 : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by norm_num)
      nlinarith

/-- A graph that is not `K_(3^r)`-free contains the words of length `r` as a clique. -/
lemma exists_clique_map {V : Type*} (G : SimpleGraph V) (r : ℕ) (h : ¬ G.CliqueFree (3 ^ r)) :
    ∃ e : (Fin r → Fin 3) → V, Function.Injective e ∧ ∀ x y, x ≠ y → G.Adj (e x) (e y) := by
  classical
  unfold SimpleGraph.CliqueFree at h
  push Not at h
  obtain ⟨t, ht⟩ := h
  have hcard : Fintype.card (Fin r → Fin 3) = Fintype.card t := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_coe, ht.card_eq]
  let eq := Fintype.equivOfCardEq hcard
  refine ⟨fun x => (eq x : V), fun x y hxy => eq.injective (Subtype.ext hxy), fun x y hxy => ?_⟩
  exact ht.isClique (eq x).2 (eq y).2 (fun h => hxy (eq.injective (Subtype.ext h)))

theorem main : H1 → H2 → type_of% @Erdos761.erdos_761.parts.i := by
  intro h1 h2 k
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree (3 ^ (2 * k)) →
      (m : ℕ∞) ≤ G.chromaticNumber → (k : ℕ∞) ≤ Erdos761.dichromaticNumber G := by
    by_cases hk3 : k ≤ 3
    · obtain ⟨m, hm⟩ := h1 (3 ^ (2 * k))
      exact ⟨m, fun n G hG hχ => le_trans (by exact_mod_cast hk3) (hm n G hG hχ)⟩
    · exact h2 k (by omega) (3 ^ (2 * k))
  refine ⟨m, fun V _ G hχ => ?_⟩
  by_cases hfree : G.CliqueFree (3 ^ (2 * k))
  · let e : Fin (Nat.card V) ≃ V := (Finite.equivFin V).symm
    apply dichromatic_of_comap G e
    refine hm _ (G.comap e) ?_ ?_
    · exact hfree.comap ⟨(SimpleGraph.Embedding.comap e.toEmbedding G).toCopy⟩
    · let f : G →g G.comap e := ⟨e.symm, fun {u v} huv => by simpa [SimpleGraph.comap_adj] using huv⟩
      exact hχ.trans (SimpleGraph.chromaticNumber_mono_of_hom f)
  · obtain ⟨e, he, hadj⟩ := exists_clique_map G (2 * k) hfree
    unfold Erdos761.dichromaticNumber
    refine le_iInf₂ fun j hj => ?_
    have hkj : k ≤ j := by
      by_contra hlt
      push Not at hlt
      exact clique_not_dicolorable G (2 * k) j e he hadj
        (lt_of_le_of_lt (Nat.mul_le_mul_right _ hlt.le) (pow_bound k)) hj
    exact_mod_cast hkj

end OMA.R_Erdos761_erdos_761_parts_i_R1
