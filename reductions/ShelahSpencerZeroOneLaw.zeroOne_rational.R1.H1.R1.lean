import OMAReductions.R_ShelahSpencerZeroOneLaw_zeroOne_rational_R1

/-!
Reduction of `OMA.R_ShelahSpencerZeroOneLaw_zeroOne_rational_R1.H1` (Shelah-Spencer 1988,
Section 3: unit-fraction rational exponents `alpha = 1 / q`, `q >= 2`).

We construct concrete first-order graph formulas `(valid_phi, dom_phi, lt_phi, mem_phi)` in
`k = (q + (q - 2)) + q` vertex parameters `a = (a_dom, b, c)` representing:
- `dom_phi(a, x)`: common neighborhood `D_a = { x | forall i : Fin q, Adj (a_dom i) x }`.
- `mem_phi(a, v, x)`: unit-fraction constant-probability gadget
  `R_q(b; v, x) <-> exists w, Adj v w /\ Adj x w /\ forall j : Fin (q - 2), Adj (b j) w`.
- `lt_phi(a, x, y)`: strict subset-inclusion order on `D_a` induced by the common neighborhood
  `U_c = { w | forall i : Fin q, Adj (c i) w }` via `R_q(b; w, .)`.
- `base_phi(a)`: pairwise distinctness of `a`, nonemptiness of `D_a`, trichotomy of `lt_phi` on
  `D_a`, and the first-order binary ripple-carry axioms `Zero(a) /\ Succ(a)`.
- `embed_phi(a', a)`: existence of two `(q - 1)`-tuples `e1, e2` and 30 `q`-tuples
  `d : Fin 30 -> Fin q -> V` whose union of common neighborhoods decouples membership tests via
  `N(w, e1)` and `N(w, e2)` to define a total strictly order-preserving relation from
  `(D_{a'}, <_{a'})` into `(D_a, <_a)`.
- `valid_phi(a) := base_phi(a) /\ forall a', base_phi(a') -> embed_phi(a', a)`.

Inside this file we prove completely from scratch in Lean 4:
1. Full first-order graph `BoundedFormula` compiler for `dom_phi`, `mem_phi`, `lt_phi`,
   `base_phi`, `embed_phi`, and `valid_phi`, with exact `Formula.Realize` semantic equivalences.
2. Unconditional irreflexivity and transitivity of `lt_phi`, plus finite order enumeration and
   complete binary ripple-carry counter induction proving `Zero /\ Succ -> UNIV` on any finite
   nonempty strict linear order.
3. Deterministic cardinality comparison `embed_phi(a', a) -> |D_{a'}| <= |D_a|` and the global
   maximality sandwich forcing `|D_a| = L` for every valid tuple `a` and witnessing a valid tuple
   of size `L` satisfying `UNIV`.
4. Probability intersection bound (`>= 7/8` and `>= 7/8` implies `>= 3/4`) and subsequence
   oscillation along `L = 100 * m + 26` (`(L - 1) % 100 = 25 in [10, 40]`) versus
   `L = 100 * m + 76` (`(L - 1) % 100 = 75 notin [10, 40]`).

The reduction isolates two decoupled, unconditionally true `G(n, n^(-1/q))` theorems:
- `H1`: Sharp first/second-moment threshold for the maximum size `L` of a `base`-valid ordered
  common neighborhood in `G(n, n^(-1/q))`.
- `H2`: Asymptotically almost sure universal order-embedding among `base`-valid neighborhoods
  via 30 `q`-tuples in `G(n, n^(-1/q))`.
-/

namespace OMA.R_ShelahSpencerZeroOneLaw_zeroOne_rational_R1_H1_R1

open FirstOrder MeasureTheory

/-- Sharp first/second-moment threshold in `G(n, n^(-1/q))` (`q >= 2`): for every sufficiently
large target size `L`, there exists `n >= L` where with probability at least `7/8`, the maximum
common-neighborhood size among all `base`-valid tuples `a` is equal to `L`. -/
def H1 : Prop :=
  ∀ (q : ℕ), 2 ≤ q → ∀ (hα : (0 : ℝ) < (1 : ℝ) / (q : ℝ)),
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∃ n : ℕ, L ≤ n ∧
      (7 : ENNReal) / 8 ≤ ShelahSpencerZeroOneLaw.sparseRandomGraph n ((1 : ℝ) / (q : ℝ)) hα
        { G |
          let base (a : Fin ((q + (q - 2)) + q) → Fin n) : Prop :=
            let dom (x : Fin n) := ∀ i : Fin q, G.Adj (a (Fin.castAdd q (Fin.castAdd (q - 2) i))) x
            let mem (v x : Fin n) := ∃ w : Fin n, G.Adj v w ∧ G.Adj x w ∧
              ∀ j : Fin (q - 2), G.Adj (a (Fin.castAdd q (Fin.natAdd q j))) w
            let inU (w : Fin n) := ∀ i : Fin q, G.Adj (a (Fin.natAdd (q + (q - 2)) i)) w
            let lt (x y : Fin n) :=
              (∀ w, inU w → mem w y → mem w x) ∧ (∃ w, inU w ∧ mem w x ∧ ¬ mem w y)
            Function.Injective a ∧ (∃ x, dom x) ∧
            (∀ x y, dom x → dom y → lt x y ∨ x = y ∨ lt y x) ∧
            (∃ v, ∀ x, dom x → ¬ mem v x) ∧
            (∀ v, (∃ x, dom x ∧ ¬ mem v x) → ∃ w x, dom x ∧ ¬ mem v x ∧ mem w x ∧
              (∀ y, dom y → lt y x → mem v y ∧ ¬ mem w y) ∧
              (∀ y, dom y → lt x y → (mem v y ↔ mem w y)))
          (∃ a, base a ∧
            { x : Fin n | ∀ i : Fin q, G.Adj (a (Fin.castAdd q (Fin.castAdd (q - 2) i))) x }.ncard = L) ∧
          (∀ a, base a →
            { x : Fin n | ∀ i : Fin q, G.Adj (a (Fin.castAdd q (Fin.castAdd (q - 2) i))) x }.ncard ≤ L) }

/-- Asymptotically almost sure universal order-embedding in `G(n, n^(-1/q))` (`q >= 2`): for all
sufficiently large `n`, with probability at least `7/8`, whenever two `base`-valid tuples satisfy
`|D_{a'}| <= |D_a|`, there exist two `(q - 1)`-tuples `e1, e2` and 30 `q`-tuples `d` defining a
decoupled total strictly order-preserving relation from `(D_{a'}, <_{a'})` into `(D_a, <_a)`. -/
def H2 : Prop :=
  ∀ (q : ℕ), 2 ≤ q → ∀ (hα : (0 : ℝ) < (1 : ℝ) / (q : ℝ)),
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n →
      (7 : ENNReal) / 8 ≤ ShelahSpencerZeroOneLaw.sparseRandomGraph n ((1 : ℝ) / (q : ℝ)) hα
        { G |
          let k := (q + (q - 2)) + q
          let dom (a : Fin k → Fin n) (x : Fin n) :=
            ∀ i : Fin q, G.Adj (a (Fin.castAdd q (Fin.castAdd (q - 2) i))) x
          let mem (a : Fin k → Fin n) (v x : Fin n) :=
            ∃ w : Fin n, G.Adj v w ∧ G.Adj x w ∧
              ∀ j : Fin (q - 2), G.Adj (a (Fin.castAdd q (Fin.natAdd q j))) w
          let lt (a : Fin k → Fin n) (x y : Fin n) :=
            (∀ w, (∀ i : Fin q, G.Adj (a (Fin.natAdd (q + (q - 2)) i)) w) → mem a w y → mem a w x) ∧
            (∃ w, (∀ i : Fin q, G.Adj (a (Fin.natAdd (q + (q - 2)) i)) w) ∧ mem a w x ∧ ¬ mem a w y)
          let base (a : Fin k → Fin n) : Prop :=
            Function.Injective a ∧ (∃ x, dom a x) ∧
            (∀ x y, dom a x → dom a y → lt a x y ∨ x = y ∨ lt a y x) ∧
            (∃ v, ∀ x, dom a x → ¬ mem a v x) ∧
            (∀ v, (∃ x, dom a x ∧ ¬ mem a v x) → ∃ w x, dom a x ∧ ¬ mem a v x ∧ mem a w x ∧
              (∀ y, dom a y → lt a y x → mem a v y ∧ ¬ mem a w y) ∧
              (∀ y, dom a y → lt a x y → (mem a v y ↔ mem a w y)))
          ∀ a' a, base a' → base a → { x | dom a' x }.ncard ≤ { x | dom a x }.ncard →
            ∃ (e₁ e₂ : Fin (q - 1) → Fin n) (d : Fin 30 → Fin q → Fin n),
              let rel (x' x : Fin n) := ∃ w, (∃ s, ∀ i, G.Adj (d s i) w) ∧
                (∃ u', G.Adj w u' ∧ (∀ j, G.Adj (e₁ j) u') ∧ ∀ z', dom a' z' → (mem a' u' z' ↔ z' = x')) ∧
                (∃ u, G.Adj w u ∧ (∀ j, G.Adj (e₂ j) u) ∧ ∀ z, dom a z → (mem a u z ↔ z = x))
              (∀ x', dom a' x' → ∃ x, dom a x ∧ rel x' x) ∧
              (∀ x₁' x₂' x₁ x₂, dom a' x₁' → dom a' x₂' → dom a x₁ → dom a x₂ →
                rel x₁' x₁ → rel x₂' x₂ → lt a' x₁' x₂' → lt a x₁ x₂) }

/- === Section 1: First-Order Graph Logic Compiler === -/

lemma realize_adj_term {α : Type} {l : ℕ}
    (t₁ t₂ : Language.graph.Term (α ⊕ Fin l))
    {V : Type} (G : SimpleGraph V) (v : α → V) (xs : Fin l → V) :
    @Language.BoundedFormula.Realize _ _ G.structure _ _
      (Language.Relations.boundedFormula₂ Language.adj t₁ t₂) v xs ↔
      G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) t₁)
        (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) t₂) := by
  let := G.structure
  rw [Language.BoundedFormula.realize_rel₂]
  rfl

lemma realize_lift_term {α : Type} {l : ℕ} (t : Language.graph.Term (α ⊕ Fin l))
    {V : Type} (G : SimpleGraph V) (v : α → V) (xs : Fin l → V) (w : V) :
    @Language.Term.realize _ _ G.structure _ (Sum.elim v (Fin.snoc xs w))
      (t.relabel (Sum.map id Fin.castSucc)) =
      @Language.Term.realize _ _ G.structure _ (Sum.elim v xs) t := by
  let := G.structure
  rw [Language.Term.realize_relabel]
  congr 1
  ext x
  cases x with
  | inl a => rfl
  | inr i => simp [Fin.snoc_castSucc]

lemma exists_bigAnd {α : Type} {l : ℕ} (m : ℕ)
    (f : Fin m → Language.graph.BoundedFormula α l) :
    ∃ ψ : Language.graph.BoundedFormula α l,
      ∀ {V : Type} (G : SimpleGraph V) (v : α → V) (xs : Fin l → V),
        @Language.BoundedFormula.Realize _ _ G.structure _ _ ψ v xs ↔
          ∀ i : Fin m, @Language.BoundedFormula.Realize _ _ G.structure _ _ (f i) v xs := by
  induction m with
  | zero =>
    refine ⟨⊤, fun G v xs => ?_⟩
    let := G.structure
    simp only [Language.BoundedFormula.realize_top, true_iff]
    exact fun i => Fin.elim0 i
  | succ m ih =>
    obtain ⟨ψ, hψ⟩ := ih (fun i => f i.castSucc)
    refine ⟨ψ ⊓ f (Fin.last m), fun G v xs => ?_⟩
    let := G.structure
    rw [Language.BoundedFormula.realize_inf, hψ G v xs]
    constructor
    · rintro ⟨h1, h2⟩ i
      refine Fin.lastCases h2 (fun j => h1 j) i
    · intro h
      exact ⟨fun j => h j.castSucc, h (Fin.last m)⟩

lemma exists_bigOr {α : Type} {l : ℕ} (m : ℕ)
    (f : Fin m → Language.graph.BoundedFormula α l) :
    ∃ ψ : Language.graph.BoundedFormula α l,
      ∀ {V : Type} (G : SimpleGraph V) (v : α → V) (xs : Fin l → V),
        @Language.BoundedFormula.Realize _ _ G.structure _ _ ψ v xs ↔
          ∃ i : Fin m, @Language.BoundedFormula.Realize _ _ G.structure _ _ (f i) v xs := by
  induction m with
  | zero =>
    refine ⟨⊥, fun G v xs => ?_⟩
    let := G.structure
    simp only [Language.BoundedFormula.realize_bot, false_iff, not_exists]
    exact fun i => Fin.elim0 i
  | succ m ih =>
    obtain ⟨ψ, hψ⟩ := ih (fun i => f i.castSucc)
    refine ⟨ψ ⊔ f (Fin.last m), fun G v xs => ?_⟩
    let := G.structure
    rw [Language.BoundedFormula.realize_sup, hψ G v xs]
    constructor
    · rintro (⟨j, hj⟩ | hlast)
      · exact ⟨j.castSucc, hj⟩
      · exact ⟨Fin.last m, hlast⟩
    · rintro ⟨i, hi⟩
      refine Fin.lastCases (Or.inr ·) (fun j hj => Or.inl ⟨j, hj⟩) i hi

lemma fin_append_snoc {V : Type} {n m : ℕ} (xs : Fin n → V) (ys : Fin m → V) (y : V) :
    Fin.append xs (Fin.snoc ys y) = Fin.snoc (Fin.append xs ys) y := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simp only [Fin.snoc_last]
    have hlast : (Fin.last (n + m)) = Fin.natAdd n (Fin.last m) := by
      ext
      simp
    change Fin.append xs (Fin.snoc ys y) (Fin.last (n + m)) = y
    rw [hlast, Fin.append_right, Fin.snoc_last]
  · intro j
    simp only [Fin.snoc_castSucc]
    refine Fin.addCases ?_ ?_ j
    · intro a
      have hcast : (Fin.castAdd m a).castSucc = Fin.castAdd (m + 1) a := by
        ext
        simp
      rw [hcast, Fin.append_left, Fin.append_left]
    · intro b
      have hnat : (Fin.natAdd n b).castSucc = Fin.natAdd n b.castSucc := by
        ext
        simp
      rw [hnat, Fin.append_right, Fin.append_right, Fin.snoc_castSucc]

lemma exists_allMany {α : Type} {n : ℕ} (m : ℕ)
    (φ : Language.graph.BoundedFormula α (n + m)) :
    ∃ ψ : Language.graph.BoundedFormula α n,
      ∀ {V : Type} (G : SimpleGraph V) (v : α → V) (xs : Fin n → V),
        @Language.BoundedFormula.Realize _ _ G.structure _ _ ψ v xs ↔
          ∀ ys : Fin m → V,
            @Language.BoundedFormula.Realize _ _ G.structure _ _ φ v (Fin.append xs ys) := by
  induction m with
  | zero =>
    refine ⟨φ, fun {V} G v xs => ?_⟩
    constructor
    · intro h ys
      have hEq : Fin.append xs ys = xs := by
        ext i
        have hi : i = Fin.castAdd 0 i := by ext; rfl
        conv_lhs => rw [hi]
        rw [Fin.append_left]
      rw [hEq]
      exact h
    · intro h
      have h0 := h Fin.elim0
      have hEq : Fin.append xs (Fin.elim0 : Fin 0 → V) = xs := by
        ext i
        have hi : i = Fin.castAdd 0 i := by ext; rfl
        conv_lhs => rw [hi]
        rw [Fin.append_left]
      rw [hEq] at h0
      exact h0
  | succ m ih =>
    obtain ⟨ψ, hψ⟩ := ih φ.all
    refine ⟨ψ, fun {V} G v xs => ?_⟩
    let := G.structure
    rw [hψ G v xs]
    constructor
    · intro h ys
      have hsnoc : Fin.snoc (Fin.init ys) (ys (Fin.last m)) = ys := Fin.snoc_init_self ys
      rw [← hsnoc, fin_append_snoc]
      exact (Language.BoundedFormula.realize_all.mp (h (Fin.init ys))) (ys (Fin.last m))
    · intro h ys
      rw [Language.BoundedFormula.realize_all]
      intro y
      rw [← fin_append_snoc]
      exact h (Fin.snoc ys y)

lemma exists_exMany {α : Type} {n : ℕ} (m : ℕ)
    (φ : Language.graph.BoundedFormula α (n + m)) :
    ∃ ψ : Language.graph.BoundedFormula α n,
      ∀ {V : Type} (G : SimpleGraph V) (v : α → V) (xs : Fin n → V),
        @Language.BoundedFormula.Realize _ _ G.structure _ _ ψ v xs ↔
          ∃ ys : Fin m → V,
            @Language.BoundedFormula.Realize _ _ G.structure _ _ φ v (Fin.append xs ys) := by
  obtain ⟨ψ, hψ⟩ := exists_allMany m φ.not
  refine ⟨ψ.not, fun G v xs => ?_⟩
  let := G.structure
  rw [Language.BoundedFormula.realize_not, hψ G v xs]
  simp only [Language.BoundedFormula.realize_not, not_forall, Classical.not_not]

lemma exists_dom_bd {α : Type} {l q : ℕ}
    (a_dom : Fin q → Language.graph.Term (α ⊕ Fin l))
    (x : Language.graph.Term (α ⊕ Fin l)) :
    ∃ φ : Language.graph.BoundedFormula α l,
      ∀ {V : Type} (G : SimpleGraph V) (v : α → V) (xs : Fin l → V),
        @Language.BoundedFormula.Realize _ _ G.structure _ _ φ v xs ↔
          ∀ i : Fin q, G.Adj
            (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) (a_dom i))
            (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) x) := by
  obtain ⟨φ, hφ⟩ := exists_bigAnd q (fun i =>
    Language.Relations.boundedFormula₂ Language.adj (a_dom i) x)
  refine ⟨φ, fun G v xs => ?_⟩
  rw [hφ G v xs]
  exact forall_congr' fun i => realize_adj_term (a_dom i) x G v xs

lemma exists_mem_bd {α : Type} {l q : ℕ}
    (b : Fin (q - 2) → Language.graph.Term (α ⊕ Fin l))
    (u x : Language.graph.Term (α ⊕ Fin l)) :
    ∃ φ : Language.graph.BoundedFormula α l,
      ∀ {V : Type} (G : SimpleGraph V) (v : α → V) (xs : Fin l → V),
        @Language.BoundedFormula.Realize _ _ G.structure _ _ φ v xs ↔
          ∃ w : V,
            G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) u) w ∧
            G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) x) w ∧
            ∀ j : Fin (q - 2),
              G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) (b j)) w := by
  let lift : Language.graph.Term (α ⊕ Fin l) → Language.graph.Term (α ⊕ Fin (l + 1)) :=
    fun t => t.relabel (Sum.map id Fin.castSucc)
  let wVar : Language.graph.Term (α ⊕ Fin (l + 1)) := Language.Term.var (Sum.inr (Fin.last l))
  obtain ⟨b_φ, hb_φ⟩ := exists_bigAnd (q - 2) (fun j =>
    Language.Relations.boundedFormula₂ Language.adj (lift (b j)) wVar)
  let body : Language.graph.BoundedFormula α (l + 1) :=
    (Language.Relations.boundedFormula₂ Language.adj (lift u) wVar) ⊓
      ((Language.Relations.boundedFormula₂ Language.adj (lift x) wVar) ⊓ b_φ)
  refine ⟨body.ex, fun G v xs => ?_⟩
  let := G.structure
  rw [Language.BoundedFormula.realize_ex]
  refine exists_congr fun w => ?_
  simp only [body, Language.BoundedFormula.realize_inf]
  rw [realize_adj_term, realize_adj_term, hb_φ G v (Fin.snoc xs w)]
  have hw : @Language.Term.realize _ _ G.structure _ (Sum.elim v (Fin.snoc xs w)) wVar = w := by
    simp [wVar]
  simp only [lift, realize_lift_term, hw]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun j => ?_⟩
    have hj := (realize_adj_term _ _ G v (Fin.snoc xs w)).mp (h3 j)
    simpa only [lift, realize_lift_term, hw] using hj
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun j => ?_⟩
    rw [realize_adj_term]
    simpa only [lift, realize_lift_term, hw] using h3 j

lemma exists_lt_bd {α : Type} {l q : ℕ}
    (b : Fin (q - 2) → Language.graph.Term (α ⊕ Fin l))
    (c : Fin q → Language.graph.Term (α ⊕ Fin l))
    (x y : Language.graph.Term (α ⊕ Fin l)) :
    ∃ φ : Language.graph.BoundedFormula α l,
      ∀ {V : Type} (G : SimpleGraph V) (v : α → V) (xs : Fin l → V),
        @Language.BoundedFormula.Realize _ _ G.structure _ _ φ v xs ↔
          (∀ w : V,
            (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) (c i)) w) →
            (∃ u : V, G.Adj w u ∧
              G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) y) u ∧
              ∀ j : Fin (q - 2),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) (b j)) u) →
            (∃ u : V, G.Adj w u ∧
              G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) x) u ∧
              ∀ j : Fin (q - 2),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) (b j)) u)) ∧
          (∃ w : V,
            (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) (c i)) w) ∧
            (∃ u : V, G.Adj w u ∧
              G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) x) u ∧
              ∀ j : Fin (q - 2),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) (b j)) u) ∧
            ¬ (∃ u : V, G.Adj w u ∧
              G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) y) u ∧
              ∀ j : Fin (q - 2),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) (b j)) u)) := by
  let lift : Language.graph.Term (α ⊕ Fin l) → Language.graph.Term (α ⊕ Fin (l + 1)) :=
    fun t => t.relabel (Sum.map id Fin.castSucc)
  let wVar : Language.graph.Term (α ⊕ Fin (l + 1)) := Language.Term.var (Sum.inr (Fin.last l))
  obtain ⟨inU_φ, hinU_φ⟩ := exists_dom_bd (fun i => lift (c i)) wVar
  obtain ⟨memX_φ, hmemX_φ⟩ := exists_mem_bd (fun j => lift (b j)) wVar (lift x)
  obtain ⟨memY_φ, hmemY_φ⟩ := exists_mem_bd (fun j => lift (b j)) wVar (lift y)
  let part1 : Language.graph.BoundedFormula α l := (inU_φ.imp (memY_φ.imp memX_φ)).all
  let part2 : Language.graph.BoundedFormula α l := (inU_φ ⊓ (memX_φ ⊓ memY_φ.not)).ex
  refine ⟨part1 ⊓ part2, fun {V} G v xs => ?_⟩
  let := G.structure
  have hw : ∀ w : V, @Language.Term.realize _ _ G.structure _ (Sum.elim v (Fin.snoc xs w)) wVar = w :=
    fun w => by simp [wVar]
  simp only [part1, part2, Language.BoundedFormula.realize_inf, Language.BoundedFormula.realize_all,
    Language.BoundedFormula.realize_ex, Language.BoundedFormula.realize_imp,
    Language.BoundedFormula.realize_not]
  constructor
  · rintro ⟨h1, ⟨w, hU, hX, hY⟩⟩
    refine ⟨fun w' hU' hY' => ?_, ⟨w, ?_, ?_, ?_⟩⟩
    · have hU'' : inU_φ.Realize v (Fin.snoc xs w') := by
        rw [hinU_φ G v (Fin.snoc xs w')]
        simpa only [lift, realize_lift_term, hw] using hU'
      have hY'' : memY_φ.Realize v (Fin.snoc xs w') := by
        rw [hmemY_φ G v (Fin.snoc xs w')]
        simpa only [lift, realize_lift_term, hw] using hY'
      have hX'' := (hmemX_φ G v (Fin.snoc xs w')).mp (h1 w' hU'' hY'')
      simpa only [lift, realize_lift_term, hw] using hX''
    · have h := (hinU_φ G v (Fin.snoc xs w)).mp hU
      simpa only [lift, realize_lift_term, hw] using h
    · have h := (hmemX_φ G v (Fin.snoc xs w)).mp hX
      simpa only [lift, realize_lift_term, hw] using h
    · intro h
      apply hY
      rw [hmemY_φ G v (Fin.snoc xs w)]
      simpa only [lift, realize_lift_term, hw] using h
  · rintro ⟨h1, ⟨w, hU, hX, hY⟩⟩
    refine ⟨fun w' hU' hY' => ?_, ⟨w, ?_, ?_, ?_⟩⟩
    · have hU'' := (hinU_φ G v (Fin.snoc xs w')).mp hU'
      have hY'' := (hmemY_φ G v (Fin.snoc xs w')).mp hY'
      simp only [lift, realize_lift_term, hw] at hU'' hY''
      rw [hmemX_φ G v (Fin.snoc xs w')]
      simpa only [lift, realize_lift_term, hw] using h1 w' hU'' hY''
    · rw [hinU_φ G v (Fin.snoc xs w)]
      simpa only [lift, realize_lift_term, hw] using hU
    · rw [hmemX_φ G v (Fin.snoc xs w)]
      simpa only [lift, realize_lift_term, hw] using hX
    · intro h
      apply hY
      have h' := (hmemY_φ G v (Fin.snoc xs w)).mp h
      simpa only [lift, realize_lift_term, hw] using h'

lemma exists_inj_bd {α : Type} {l m : ℕ} (a : Fin m → Language.graph.Term (α ⊕ Fin l)) :
    ∃ φ : Language.graph.BoundedFormula α l,
      ∀ {V : Type} (G : SimpleGraph V) (v : α → V) (xs : Fin l → V),
        @Language.BoundedFormula.Realize _ _ G.structure _ _ φ v xs ↔
          Function.Injective (fun i : Fin m =>
            @Language.Term.realize _ _ G.structure _ (Sum.elim v xs) (a i)) := by
  let pairForm : Fin m → Fin m → Language.graph.BoundedFormula α l := fun i j =>
    if i = j then ⊤ else ((a i).bdEqual (a j)).not
  have hinner : ∀ i : Fin m, ∃ ψ : Language.graph.BoundedFormula α l,
      ∀ {V : Type} (G : SimpleGraph V) (v : α → V) (xs : Fin l → V),
        @Language.BoundedFormula.Realize _ _ G.structure _ _ ψ v xs ↔
          ∀ j : Fin m, @Language.BoundedFormula.Realize _ _ G.structure _ _ (pairForm i j) v xs :=
    fun i => exists_bigAnd m (pairForm i)
  obtain ⟨φ, hφ⟩ := exists_bigAnd m (fun i => Classical.choose (hinner i))
  refine ⟨φ, fun G v xs => ?_⟩
  let := G.structure
  rw [hφ G v xs]
  have hall : (∀ i : Fin m, (Classical.choose (hinner i)).Realize v xs) ↔
      ∀ i j : Fin m, (pairForm i j).Realize v xs :=
    forall_congr' fun i => Classical.choose_spec (hinner i) G v xs
  rw [hall]
  constructor
  · intro h i j hij
    by_contra hne
    have h1 := h i j
    simp only [pairForm, hne, ite_false, Language.BoundedFormula.realize_not,
      Language.BoundedFormula.realize_bdEqual] at h1
    exact h1 hij
  · intro hinj i j
    by_cases hij : i = j
    · simp [pairForm, hij]
    · simp only [pairForm, hij, ite_false, Language.BoundedFormula.realize_not,
        Language.BoundedFormula.realize_bdEqual]
      intro heq
      exact hij (hinj heq)

lemma exists_base_bd {α : Type} {l q : ℕ}
    (a : Fin ((q + (q - 2)) + q) → Language.graph.Term (α ⊕ Fin l)) :
    ∃ φ : Language.graph.BoundedFormula α l,
      ∀ {V : Type} (G : SimpleGraph V) (v : α → V) (xs : Fin l → V),
        @Language.BoundedFormula.Realize _ _ G.structure _ _ φ v xs ↔
          Function.Injective (fun i =>
            @Language.Term.realize _ _ G.structure _ (Sum.elim v xs) (a i)) ∧
          (∃ x : V, ∀ i : Fin q,
            G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
              (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x) ∧
          (∀ x y : V,
            (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
              (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x) →
            (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
              (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) y) →
            ((∀ w : V,
              (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                (a (Fin.natAdd (q + (q - 2)) i))) w) →
              (∃ z : V, G.Adj w z ∧ G.Adj y z ∧ ∀ j : Fin (q - 2),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.castAdd q (Fin.natAdd q j)))) z) →
              (∃ z : V, G.Adj w z ∧ G.Adj x z ∧ ∀ j : Fin (q - 2),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.castAdd q (Fin.natAdd q j)))) z)) ∧
             (∃ w : V,
              (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                (a (Fin.natAdd (q + (q - 2)) i))) w) ∧
              (∃ z : V, G.Adj w z ∧ G.Adj x z ∧ ∀ j : Fin (q - 2),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.castAdd q (Fin.natAdd q j)))) z) ∧
              ¬ (∃ z : V, G.Adj w z ∧ G.Adj y z ∧ ∀ j : Fin (q - 2),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.castAdd q (Fin.natAdd q j)))) z))) ∨
            x = y ∨
            ((∀ w : V,
              (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                (a (Fin.natAdd (q + (q - 2)) i))) w) →
              (∃ z : V, G.Adj w z ∧ G.Adj x z ∧ ∀ j : Fin (q - 2),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.castAdd q (Fin.natAdd q j)))) z) →
              (∃ z : V, G.Adj w z ∧ G.Adj y z ∧ ∀ j : Fin (q - 2),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.castAdd q (Fin.natAdd q j)))) z)) ∧
             (∃ w : V,
              (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                (a (Fin.natAdd (q + (q - 2)) i))) w) ∧
              (∃ z : V, G.Adj w z ∧ G.Adj y z ∧ ∀ j : Fin (q - 2),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.castAdd q (Fin.natAdd q j)))) z) ∧
              ¬ (∃ z : V, G.Adj w z ∧ G.Adj x z ∧ ∀ j : Fin (q - 2),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.castAdd q (Fin.natAdd q j)))) z)))) ∧
          (∃ u : V, ∀ x : V,
            (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
              (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x) →
            ¬ (∃ z : V, G.Adj u z ∧ G.Adj x z ∧ ∀ j : Fin (q - 2),
              G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                (a (Fin.castAdd q (Fin.natAdd q j)))) z)) ∧
          (∀ u : V,
            (∃ x : V,
              (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x) ∧
              ¬ (∃ z : V, G.Adj u z ∧ G.Adj x z ∧ ∀ j : Fin (q - 2),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.castAdd q (Fin.natAdd q j)))) z)) →
            ∃ w x : V,
              (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x) ∧
              ¬ (∃ z : V, G.Adj u z ∧ G.Adj x z ∧ ∀ j : Fin (q - 2),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.castAdd q (Fin.natAdd q j)))) z) ∧
              (∃ z : V, G.Adj w z ∧ G.Adj x z ∧ ∀ j : Fin (q - 2),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.castAdd q (Fin.natAdd q j)))) z) ∧
              (∀ y : V,
                (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) y) →
                ((∀ w' : V,
                  (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a (Fin.natAdd (q + (q - 2)) i))) w') →
                  (∃ z : V, G.Adj w' z ∧ G.Adj x z ∧ ∀ j : Fin (q - 2),
                    G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                      (a (Fin.castAdd q (Fin.natAdd q j)))) z) →
                  (∃ z : V, G.Adj w' z ∧ G.Adj y z ∧ ∀ j : Fin (q - 2),
                    G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                      (a (Fin.castAdd q (Fin.natAdd q j)))) z)) ∧
                 (∃ w' : V,
                  (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a (Fin.natAdd (q + (q - 2)) i))) w') ∧
                  (∃ z : V, G.Adj w' z ∧ G.Adj y z ∧ ∀ j : Fin (q - 2),
                    G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                      (a (Fin.castAdd q (Fin.natAdd q j)))) z) ∧
                  ¬ (∃ z : V, G.Adj w' z ∧ G.Adj x z ∧ ∀ j : Fin (q - 2),
                    G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                      (a (Fin.castAdd q (Fin.natAdd q j)))) z))) →
                (∃ z : V, G.Adj u z ∧ G.Adj y z ∧ ∀ j : Fin (q - 2),
                  G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a (Fin.castAdd q (Fin.natAdd q j)))) z) ∧
                ¬ (∃ z : V, G.Adj w z ∧ G.Adj y z ∧ ∀ j : Fin (q - 2),
                  G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a (Fin.castAdd q (Fin.natAdd q j)))) z)) ∧
              (∀ y : V,
                (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) y) →
                ((∀ w' : V,
                  (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a (Fin.natAdd (q + (q - 2)) i))) w') →
                  (∃ z : V, G.Adj w' z ∧ G.Adj y z ∧ ∀ j : Fin (q - 2),
                    G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                      (a (Fin.castAdd q (Fin.natAdd q j)))) z) →
                  (∃ z : V, G.Adj w' z ∧ G.Adj x z ∧ ∀ j : Fin (q - 2),
                    G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                      (a (Fin.castAdd q (Fin.natAdd q j)))) z)) ∧
                 (∃ w' : V,
                  (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a (Fin.natAdd (q + (q - 2)) i))) w') ∧
                  (∃ z : V, G.Adj w' z ∧ G.Adj x z ∧ ∀ j : Fin (q - 2),
                    G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                      (a (Fin.castAdd q (Fin.natAdd q j)))) z) ∧
                  ¬ (∃ z : V, G.Adj w' z ∧ G.Adj y z ∧ ∀ j : Fin (q - 2),
                    G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                      (a (Fin.castAdd q (Fin.natAdd q j)))) z))) →
                ((∃ z : V, G.Adj u z ∧ G.Adj y z ∧ ∀ j : Fin (q - 2),
                  G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a (Fin.castAdd q (Fin.natAdd q j)))) z) ↔
                 (∃ z : V, G.Adj w z ∧ G.Adj y z ∧ ∀ j : Fin (q - 2),
                  G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a (Fin.castAdd q (Fin.natAdd q j)))) z)))) := by
  let aDom (i : Fin q) := a (Fin.castAdd q (Fin.castAdd (q - 2) i))
  let aB (j : Fin (q - 2)) := a (Fin.castAdd q (Fin.natAdd q j))
  let aC (i : Fin q) := a (Fin.natAdd (q + (q - 2)) i)
  let lift1 : ∀ {m : ℕ}, Language.graph.Term (α ⊕ Fin m) → Language.graph.Term (α ⊕ Fin (m + 1)) :=
    fun t => t.relabel (Sum.map id Fin.castSucc)
  -- 1. Injectivity
  obtain ⟨inj_φ, hinj_φ⟩ := exists_inj_bd a
  -- 2. Nonempty domain
  let x1 : Language.graph.Term (α ⊕ Fin (l + 1)) := Language.Term.var (Sum.inr (Fin.last l))
  obtain ⟨dom1_φ, hdom1_φ⟩ := exists_dom_bd (fun i => lift1 (aDom i)) x1
  let nonemp_φ : Language.graph.BoundedFormula α l := dom1_φ.ex
  -- 3. Trichotomy
  let x2 : Language.graph.Term (α ⊕ Fin (l + 2)) :=
    Language.Term.var (Sum.inr (Fin.last l).castSucc)
  let y2 : Language.graph.Term (α ⊕ Fin (l + 2)) :=
    Language.Term.var (Sum.inr (Fin.last (l + 1)))
  let aDom2 (i : Fin q) := lift1 (lift1 (aDom i))
  let aB2 (j : Fin (q - 2)) := lift1 (lift1 (aB j))
  let aC2 (i : Fin q) := lift1 (lift1 (aC i))
  obtain ⟨domX2, hdomX2⟩ := exists_dom_bd aDom2 x2
  obtain ⟨domY2, hdomY2⟩ := exists_dom_bd aDom2 y2
  obtain ⟨ltXY2, hltXY2⟩ := exists_lt_bd aB2 aC2 x2 y2
  obtain ⟨ltYX2, hltYX2⟩ := exists_lt_bd aB2 aC2 y2 x2
  let tri_φ : Language.graph.BoundedFormula α l :=
    ((domX2.imp (domY2.imp (ltXY2 ⊔ (x2.bdEqual y2 ⊔ ltYX2)))).all).all
  -- 4. Zero
  obtain ⟨mem2_ux, hmem2_ux⟩ := exists_mem_bd aB2 x2 y2
  let zero_φ : Language.graph.BoundedFormula α l := ((domY2.imp mem2_ux.not).all).ex
  -- 5. Succ: ∀ u (l), (∃ x (l+1), dom x ∧ ¬ mem u x) → ∃ w (l+1), ∃ x (l+2), ...
  let u1 : Language.graph.Term (α ⊕ Fin (l + 1)) := Language.Term.var (Sum.inr (Fin.last l))
  let aDom3 (i : Fin q) := lift1 (aDom2 i)
  let aB3 (j : Fin (q - 2)) := lift1 (aB2 j)
  let aC3 (i : Fin q) := lift1 (aC2 i)
  let aDom4 (i : Fin q) := lift1 (aDom3 i)
  let aB4 (j : Fin (q - 2)) := lift1 (aB3 j)
  let aC4 (i : Fin q) := lift1 (aC3 i)
  let u3 : Language.graph.Term (α ⊕ Fin (l + 3)) :=
    Language.Term.var (Sum.inr (Fin.last l).castSucc.castSucc)
  let w3 : Language.graph.Term (α ⊕ Fin (l + 3)) :=
    Language.Term.var (Sum.inr (Fin.last (l + 1)).castSucc)
  let x3 : Language.graph.Term (α ⊕ Fin (l + 3)) :=
    Language.Term.var (Sum.inr (Fin.last (l + 2)))
  let u4 : Language.graph.Term (α ⊕ Fin (l + 4)) := lift1 u3
  let w4 : Language.graph.Term (α ⊕ Fin (l + 4)) := lift1 w3
  let x4 : Language.graph.Term (α ⊕ Fin (l + 4)) := lift1 x3
  let y4 : Language.graph.Term (α ⊕ Fin (l + 4)) :=
    Language.Term.var (Sum.inr (Fin.last (l + 3)))
  obtain ⟨domX3, hdomX3⟩ := exists_dom_bd aDom3 x3
  obtain ⟨memUX3, hmemUX3⟩ := exists_mem_bd aB3 u3 x3
  obtain ⟨memWX3, hmemWX3⟩ := exists_mem_bd aB3 w3 x3
  obtain ⟨domY4, hdomY4⟩ := exists_dom_bd aDom4 y4
  obtain ⟨ltYX4, hltYX4⟩ := exists_lt_bd aB4 aC4 y4 x4
  obtain ⟨ltXY4, hltXY4⟩ := exists_lt_bd aB4 aC4 x4 y4
  obtain ⟨memUY4, hmemUY4⟩ := exists_mem_bd aB4 u4 y4
  obtain ⟨memWY4, hmemWY4⟩ := exists_mem_bd aB4 w4 y4
  let succ_pre : Language.graph.BoundedFormula α (l + 1) := (domY2 ⊓ mem2_ux.not).ex
  let low_φ : Language.graph.BoundedFormula α (l + 3) :=
    (domY4.imp (ltYX4.imp (memUY4 ⊓ memWY4.not))).all
  let high_φ : Language.graph.BoundedFormula α (l + 3) :=
    (domY4.imp (ltXY4.imp (memUY4.iff memWY4))).all
  let succ_post : Language.graph.BoundedFormula α (l + 1) :=
    ((domX3 ⊓ (memUX3.not ⊓ (memWX3 ⊓ (low_φ ⊓ high_φ)))).ex).ex
  let succ_φ : Language.graph.BoundedFormula α l := (succ_pre.imp succ_post).all
  refine ⟨inj_φ ⊓ (nonemp_φ ⊓ (tri_φ ⊓ (zero_φ ⊓ succ_φ))), fun {V} G v xs => ?_⟩
  let := G.structure
  have hev1 : ∀ (t : Language.graph.Term (α ⊕ Fin l)) (z : V),
      (lift1 t).realize (Sum.elim v (Fin.snoc xs z)) = t.realize (Sum.elim v xs) :=
    fun t z => realize_lift_term t G v xs z
  have hev2 : ∀ (t : Language.graph.Term (α ⊕ Fin l)) (z₁ z₂ : V),
      (lift1 (lift1 t)).realize (Sum.elim v (Fin.snoc (Fin.snoc xs z₁) z₂)) =
        t.realize (Sum.elim v xs) := by
    intro t z₁ z₂
    rw [realize_lift_term, realize_lift_term]
  have hev3 : ∀ (t : Language.graph.Term (α ⊕ Fin l)) (z₁ z₂ z₃ : V),
      (lift1 (lift1 (lift1 t))).realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc xs z₁) z₂) z₃)) =
        t.realize (Sum.elim v xs) := by
    intro t z₁ z₂ z₃
    rw [realize_lift_term, realize_lift_term, realize_lift_term]
  have hev4 : ∀ (t : Language.graph.Term (α ⊕ Fin l)) (z₁ z₂ z₃ z₄ : V),
      (lift1 (lift1 (lift1 (lift1 t)))).realize
          (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs z₁) z₂) z₃) z₄)) =
        t.realize (Sum.elim v xs) := by
    intro t z₁ z₂ z₃ z₄
    rw [realize_lift_term, realize_lift_term, realize_lift_term, realize_lift_term]
  simp only [Language.BoundedFormula.realize_inf, hinj_φ G v xs, nonemp_φ, tri_φ, zero_φ, succ_φ,
    succ_pre, succ_post, low_φ, high_φ, Language.BoundedFormula.realize_ex,
    Language.BoundedFormula.realize_all, Language.BoundedFormula.realize_imp,
    Language.BoundedFormula.realize_sup, Language.BoundedFormula.realize_not,
    Language.BoundedFormula.realize_bdEqual, Language.BoundedFormula.realize_iff]
  refine and_congr Iff.rfl (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · refine exists_congr fun x => ?_
    rw [hdom1_φ G v (Fin.snoc xs x)]
    simp only [x1, aDom, hev1, Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
  · refine forall_congr' fun x => forall_congr' fun y => ?_
    rw [hdomX2 G v _, hdomY2 G v _, hltXY2 G v _, hltYX2 G v _]
    simp only [x2, y2, aDom2, aB2, aC2, aDom, aB, aC, hev2, Language.Term.realize_var,
      Sum.elim_inr, Fin.snoc_castSucc, Fin.snoc_last]
  · refine exists_congr fun u => forall_congr' fun x => ?_
    rw [hdomY2 G v _, hmem2_ux G v _]
    simp only [x2, y2, aDom2, aB2, aDom, aB, hev2, Language.Term.realize_var,
      Sum.elim_inr, Fin.snoc_castSucc, Fin.snoc_last]
  · refine forall_congr' fun u => imp_congr ?_ ?_
    · refine exists_congr fun x => ?_
      rw [hdomY2 G v _, hmem2_ux G v _]
      simp only [x2, y2, aDom2, aB2, aDom, aB, hev2, Language.Term.realize_var,
        Sum.elim_inr, Fin.snoc_castSucc, Fin.snoc_last]
    · refine exists_congr fun w => exists_congr fun x => ?_
      rw [hdomX3 G v _, hmemUX3 G v _, hmemWX3 G v _]
      have h3_u : u3.realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc xs u) w) x)) = u := by
        simp [u3]
      have h3_w : w3.realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc xs u) w) x)) = w := by
        simp [w3]
      have h3_x : x3.realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc xs u) w) x)) = x := by
        simp [x3]
      simp only [aDom3, aB3, aDom2, aB2, aDom, aB, hev3, h3_u, h3_w, h3_x]
      refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ ?_)))
      · refine forall_congr' fun y => ?_
        rw [hdomY4 G v _, hltYX4 G v _, hmemUY4 G v _, hmemWY4 G v _]
        have h4_u : u4.realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs u) w) x) y)) = u := by
          simp [u4, u3, lift1]
        have h4_w : w4.realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs u) w) x) y)) = w := by
          simp [w4, w3, lift1]
        have h4_x : x4.realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs u) w) x) y)) = x := by
          simp [x4, x3, lift1]
        have h4_y : y4.realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs u) w) x) y)) = y := by
          simp [y4]
        simp only [aDom4, aB4, aC4, aDom3, aB3, aC3, aDom2, aB2, aC2, aDom, aB, aC, hev4,
          h4_u, h4_w, h4_x, h4_y]
      · refine forall_congr' fun y => ?_
        rw [hdomY4 G v _, hltXY4 G v _, hmemUY4 G v _, hmemWY4 G v _]
        have h4_u : u4.realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs u) w) x) y)) = u := by
          simp [u4, u3, lift1]
        have h4_w : w4.realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs u) w) x) y)) = w := by
          simp [w4, w3, lift1]
        have h4_x : x4.realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs u) w) x) y)) = x := by
          simp [x4, x3, lift1]
        have h4_y : y4.realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs u) w) x) y)) = y := by
          simp [y4]
        simp only [aDom4, aB4, aC4, aDom3, aB3, aC3, aDom2, aB2, aC2, aDom, aB, aC, hev4,
          h4_u, h4_w, h4_x, h4_y]

lemma exists_rel_bd {α : Type} {l q : ℕ}
    (a' a : Fin ((q + (q - 2)) + q) → Language.graph.Term (α ⊕ Fin l))
    (e₁ e₂ : Fin (q - 1) → Language.graph.Term (α ⊕ Fin l))
    (d : Fin 30 → Fin q → Language.graph.Term (α ⊕ Fin l))
    (x' x : Language.graph.Term (α ⊕ Fin l)) :
    ∃ φ : Language.graph.BoundedFormula α l,
      ∀ {V : Type} (G : SimpleGraph V) (v : α → V) (xs : Fin l → V),
        @Language.BoundedFormula.Realize _ _ G.structure _ _ φ v xs ↔
          ∃ w : V,
            (∃ s : Fin 30, ∀ i : Fin q,
              G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) (d s i)) w) ∧
            (∃ u' : V, G.Adj w u' ∧
              (∀ j : Fin (q - 1),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) (e₁ j)) u') ∧
              ∀ z' : V,
                (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a' (Fin.castAdd q (Fin.castAdd (q - 2) i)))) z') →
                ((∃ t : V, G.Adj u' t ∧ G.Adj z' t ∧ ∀ j : Fin (q - 2),
                  G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a' (Fin.castAdd q (Fin.natAdd q j)))) t) ↔
                 z' = @Language.Term.realize _ _ G.structure _ (Sum.elim v xs) x')) ∧
            (∃ u : V, G.Adj w u ∧
              (∀ j : Fin (q - 1),
                G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) (e₂ j)) u) ∧
              ∀ z : V,
                (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) z) →
                ((∃ t : V, G.Adj u t ∧ G.Adj z t ∧ ∀ j : Fin (q - 2),
                  G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a (Fin.castAdd q (Fin.natAdd q j)))) t) ↔
                 z = @Language.Term.realize _ _ G.structure _ (Sum.elim v xs) x)) := by
  let lift1 : ∀ {m : ℕ}, Language.graph.Term (α ⊕ Fin m) → Language.graph.Term (α ⊕ Fin (m + 1)) :=
    fun t => t.relabel (Sum.map id Fin.castSucc)
  let w1 : Language.graph.Term (α ⊕ Fin (l + 1)) := Language.Term.var (Sum.inr (Fin.last l))
  have hbranch : ∀ s : Fin 30, ∃ ψ : Language.graph.BoundedFormula α (l + 1),
      ∀ {V : Type} (G : SimpleGraph V) (v : α → V) (xs : Fin (l + 1) → V),
        @Language.BoundedFormula.Realize _ _ G.structure _ _ ψ v xs ↔
          ∀ i : Fin q, G.Adj
            (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) (lift1 (d s i)))
            (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs) w1) :=
    fun s => exists_dom_bd (fun i => lift1 (d s i)) w1
  obtain ⟨inW_φ, hinW_φ⟩ := exists_bigOr 30 (fun s => Classical.choose (hbranch s))
  let w2 : Language.graph.Term (α ⊕ Fin (l + 2)) :=
    Language.Term.var (Sum.inr (Fin.last l).castSucc)
  let u2 : Language.graph.Term (α ⊕ Fin (l + 2)) :=
    Language.Term.var (Sum.inr (Fin.last (l + 1)))
  let lift2 (t : Language.graph.Term (α ⊕ Fin l)) := lift1 (lift1 t)
  let lift3 (t : Language.graph.Term (α ⊕ Fin l)) := lift1 (lift2 t)
  let adjWU : Language.graph.BoundedFormula α (l + 2) :=
    Language.Relations.boundedFormula₂ Language.adj w2 u2
  obtain ⟨e1_φ, he1_φ⟩ := exists_dom_bd (fun j => lift2 (e₁ j)) u2
  obtain ⟨e2_φ, he2_φ⟩ := exists_dom_bd (fun j => lift2 (e₂ j)) u2
  let u3 : Language.graph.Term (α ⊕ Fin (l + 3)) :=
    Language.Term.var (Sum.inr (Fin.last (l + 1)).castSucc)
  let z3 : Language.graph.Term (α ⊕ Fin (l + 3)) :=
    Language.Term.var (Sum.inr (Fin.last (l + 2)))
  obtain ⟨dom'3, hdom'3⟩ :=
    exists_dom_bd (fun i => lift3 (a' (Fin.castAdd q (Fin.castAdd (q - 2) i)))) z3
  obtain ⟨mem'3, hmem'3⟩ :=
    exists_mem_bd (fun j => lift3 (a' (Fin.castAdd q (Fin.natAdd q j)))) u3 z3
  obtain ⟨dom3, hdom3⟩ :=
    exists_dom_bd (fun i => lift3 (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) z3
  obtain ⟨mem3, hmem3⟩ :=
    exists_mem_bd (fun j => lift3 (a (Fin.castAdd q (Fin.natAdd q j)))) u3 z3
  let only' : Language.graph.BoundedFormula α (l + 2) :=
    (dom'3.imp (mem'3.iff (z3.bdEqual (lift3 x')))).all
  let only : Language.graph.BoundedFormula α (l + 2) :=
    (dom3.imp (mem3.iff (z3.bdEqual (lift3 x)))).all
  let side1 : Language.graph.BoundedFormula α (l + 1) := (adjWU ⊓ (e1_φ ⊓ only')).ex
  let side2 : Language.graph.BoundedFormula α (l + 1) := (adjWU ⊓ (e2_φ ⊓ only)).ex
  refine ⟨(inW_φ ⊓ (side1 ⊓ side2)).ex, fun {V} G v xs => ?_⟩
  let := G.structure
  have hev2 : ∀ (t : Language.graph.Term (α ⊕ Fin l)) (z₁ z₂ : V),
      (lift2 t).realize (Sum.elim v (Fin.snoc (Fin.snoc xs z₁) z₂)) = t.realize (Sum.elim v xs) := by
    intro t z₁ z₂
    simp only [lift2, lift1, realize_lift_term]
  have hev3 : ∀ (t : Language.graph.Term (α ⊕ Fin l)) (z₁ z₂ z₃ : V),
      (lift3 t).realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc xs z₁) z₂) z₃)) =
        t.realize (Sum.elim v xs) := by
    intro t z₁ z₂ z₃
    simp only [lift3, lift2, lift1, realize_lift_term]
  simp only [Language.BoundedFormula.realize_ex, Language.BoundedFormula.realize_inf,
    hinW_φ G v _, side1, side2, only', only, Language.BoundedFormula.realize_all,
    Language.BoundedFormula.realize_imp, Language.BoundedFormula.realize_iff,
    Language.BoundedFormula.realize_bdEqual]
  refine exists_congr fun w => and_congr ?_ (and_congr ?_ ?_)
  · refine exists_congr fun s => ?_
    rw [Classical.choose_spec (hbranch s) G v (Fin.snoc xs w)]
    simp only [lift1, w1, realize_lift_term, Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
  · refine exists_congr fun u' => ?_
    rw [realize_adj_term, he1_φ G v _]
    simp only [w2, u2, hev2, Language.Term.realize_var, Sum.elim_inr, Fin.snoc_castSucc, Fin.snoc_last]
    refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun z' => ?_))
    rw [hdom'3 G v _, hmem'3 G v _]
    simp only [u3, z3, hev3, Language.Term.realize_var, Sum.elim_inr, Fin.snoc_castSucc, Fin.snoc_last]
  · refine exists_congr fun u => ?_
    rw [realize_adj_term, he2_φ G v _]
    simp only [w2, u2, hev2, Language.Term.realize_var, Sum.elim_inr, Fin.snoc_castSucc, Fin.snoc_last]
    refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun z => ?_))
    rw [hdom3 G v _, hmem3 G v _]
    simp only [u3, z3, hev3, Language.Term.realize_var, Sum.elim_inr, Fin.snoc_castSucc, Fin.snoc_last]

lemma exists_embed_bd {α : Type} {l q : ℕ}
    (a' a : Fin ((q + (q - 2)) + q) → Language.graph.Term (α ⊕ Fin l)) :
    ∃ φ : Language.graph.BoundedFormula α l,
      ∀ {V : Type} (G : SimpleGraph V) (v : α → V) (xs : Fin l → V),
        @Language.BoundedFormula.Realize _ _ G.structure _ _ φ v xs ↔
          ∃ (e₁ e₂ : Fin (q - 1) → V) (d : Fin 30 → Fin q → V),
            (∀ x' : V,
              (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                (a' (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x') →
              ∃ x : V,
                (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x) ∧
                (∃ w : V, (∃ s : Fin 30, ∀ i : Fin q, G.Adj (d s i) w) ∧
                  (∃ u' : V, G.Adj w u' ∧ (∀ j : Fin (q - 1), G.Adj (e₁ j) u') ∧
                    ∀ z' : V,
                      (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                        (a' (Fin.castAdd q (Fin.castAdd (q - 2) i)))) z') →
                      ((∃ t : V, G.Adj u' t ∧ G.Adj z' t ∧ ∀ j : Fin (q - 2),
                        G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                          (a' (Fin.castAdd q (Fin.natAdd q j)))) t) ↔ z' = x')) ∧
                  (∃ u : V, G.Adj w u ∧ (∀ j : Fin (q - 1), G.Adj (e₂ j) u) ∧
                    ∀ z : V,
                      (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                        (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) z) →
                      ((∃ t : V, G.Adj u t ∧ G.Adj z t ∧ ∀ j : Fin (q - 2),
                        G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                          (a (Fin.castAdd q (Fin.natAdd q j)))) t) ↔ z = x)))) ∧
            (∀ x₁' x₂' x₁ x₂ : V,
              (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                (a' (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x₁') →
              (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                (a' (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x₂') →
              (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x₁) →
              (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x₂) →
              (∃ w : V, (∃ s : Fin 30, ∀ i : Fin q, G.Adj (d s i) w) ∧
                (∃ u' : V, G.Adj w u' ∧ (∀ j : Fin (q - 1), G.Adj (e₁ j) u') ∧
                  ∀ z' : V,
                    (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                      (a' (Fin.castAdd q (Fin.castAdd (q - 2) i)))) z') →
                    ((∃ t : V, G.Adj u' t ∧ G.Adj z' t ∧ ∀ j : Fin (q - 2),
                      G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                        (a' (Fin.castAdd q (Fin.natAdd q j)))) t) ↔ z' = x₁')) ∧
                (∃ u : V, G.Adj w u ∧ (∀ j : Fin (q - 1), G.Adj (e₂ j) u) ∧
                  ∀ z : V,
                    (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                      (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) z) →
                    ((∃ t : V, G.Adj u t ∧ G.Adj z t ∧ ∀ j : Fin (q - 2),
                      G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                        (a (Fin.castAdd q (Fin.natAdd q j)))) t) ↔ z = x₁))) →
              (∃ w : V, (∃ s : Fin 30, ∀ i : Fin q, G.Adj (d s i) w) ∧
                (∃ u' : V, G.Adj w u' ∧ (∀ j : Fin (q - 1), G.Adj (e₁ j) u') ∧
                  ∀ z' : V,
                    (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                      (a' (Fin.castAdd q (Fin.castAdd (q - 2) i)))) z') →
                    ((∃ t : V, G.Adj u' t ∧ G.Adj z' t ∧ ∀ j : Fin (q - 2),
                      G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                        (a' (Fin.castAdd q (Fin.natAdd q j)))) t) ↔ z' = x₂')) ∧
                (∃ u : V, G.Adj w u ∧ (∀ j : Fin (q - 1), G.Adj (e₂ j) u) ∧
                  ∀ z : V,
                    (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                      (a (Fin.castAdd q (Fin.castAdd (q - 2) i)))) z) →
                    ((∃ t : V, G.Adj u t ∧ G.Adj z t ∧ ∀ j : Fin (q - 2),
                      G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                        (a (Fin.castAdd q (Fin.natAdd q j)))) t) ↔ z = x₂))) →
              ((∀ w : V,
                (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a' (Fin.natAdd (q + (q - 2)) i))) w) →
                (∃ z : V, G.Adj w z ∧ G.Adj x₂' z ∧ ∀ j : Fin (q - 2),
                  G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a' (Fin.castAdd q (Fin.natAdd q j)))) z) →
                (∃ z : V, G.Adj w z ∧ G.Adj x₁' z ∧ ∀ j : Fin (q - 2),
                  G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a' (Fin.castAdd q (Fin.natAdd q j)))) z)) ∧
               (∃ w : V,
                (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a' (Fin.natAdd (q + (q - 2)) i))) w) ∧
                (∃ z : V, G.Adj w z ∧ G.Adj x₁' z ∧ ∀ j : Fin (q - 2),
                  G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a' (Fin.castAdd q (Fin.natAdd q j)))) z) ∧
                ¬ (∃ z : V, G.Adj w z ∧ G.Adj x₂' z ∧ ∀ j : Fin (q - 2),
                  G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a' (Fin.castAdd q (Fin.natAdd q j)))) z))) →
              ((∀ w : V,
                (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.natAdd (q + (q - 2)) i))) w) →
                (∃ z : V, G.Adj w z ∧ G.Adj x₂ z ∧ ∀ j : Fin (q - 2),
                  G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a (Fin.castAdd q (Fin.natAdd q j)))) z) →
                (∃ z : V, G.Adj w z ∧ G.Adj x₁ z ∧ ∀ j : Fin (q - 2),
                  G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a (Fin.castAdd q (Fin.natAdd q j)))) z)) ∧
               (∃ w : V,
                (∀ i : Fin q, G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                  (a (Fin.natAdd (q + (q - 2)) i))) w) ∧
                (∃ z : V, G.Adj w z ∧ G.Adj x₁ z ∧ ∀ j : Fin (q - 2),
                  G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a (Fin.castAdd q (Fin.natAdd q j)))) z) ∧
                ¬ (∃ z : V, G.Adj w z ∧ G.Adj x₂ z ∧ ∀ j : Fin (q - 2),
                  G.Adj (@Language.Term.realize _ _ G.structure _ (Sum.elim v xs)
                    (a (Fin.castAdd q (Fin.natAdd q j)))) z)))) := by
  let L1 : ℕ := l + (q - 1)
  let L2 : ℕ := L1 + (q - 1)
  let L0 : ℕ := L2 + 30 * q
  let liftE1 : Language.graph.Term (α ⊕ Fin l) → Language.graph.Term (α ⊕ Fin L1) :=
    fun t => t.relabel (Sum.map id (Fin.castAdd (q - 1)))
  let liftE2 : Language.graph.Term (α ⊕ Fin L1) → Language.graph.Term (α ⊕ Fin L2) :=
    fun t => t.relabel (Sum.map id (Fin.castAdd (q - 1)))
  let liftD : Language.graph.Term (α ⊕ Fin L2) → Language.graph.Term (α ⊕ Fin L0) :=
    fun t => t.relabel (Sum.map id (Fin.castAdd (30 * q)))
  let liftAll (t : Language.graph.Term (α ⊕ Fin l)) : Language.graph.Term (α ⊕ Fin L0) :=
    liftD (liftE2 (liftE1 t))
  let lift1 : ∀ {m : ℕ}, Language.graph.Term (α ⊕ Fin m) → Language.graph.Term (α ⊕ Fin (m + 1)) :=
    fun t => t.relabel (Sum.map id Fin.castSucc)
  let a'D (i : Fin ((q + (q - 2)) + q)) := liftAll (a' i)
  let aD (i : Fin ((q + (q - 2)) + q)) := liftAll (a i)
  let e1D (j : Fin (q - 1)) : Language.graph.Term (α ⊕ Fin L0) :=
    liftD (liftE2 (Language.Term.var (Sum.inr (Fin.natAdd l j))))
  let e2D (j : Fin (q - 1)) : Language.graph.Term (α ⊕ Fin L0) :=
    liftD (Language.Term.var (Sum.inr (Fin.natAdd L1 j)))
  let dD (s : Fin 30) (i : Fin q) : Language.graph.Term (α ⊕ Fin L0) :=
    Language.Term.var (Sum.inr (Fin.natAdd L2 (finProdFinEquiv (s, i))))
  -- Totality: ∀ x' (L0), dom a' x' → ∃ x (L0+1), dom a x ∧ rel x' x
  let lift2 (t : Language.graph.Term (α ⊕ Fin L0)) := lift1 (lift1 t)
  let x'2 : Language.graph.Term (α ⊕ Fin (L0 + 2)) :=
    Language.Term.var (Sum.inr (Fin.last L0).castSucc)
  let x2 : Language.graph.Term (α ⊕ Fin (L0 + 2)) :=
    Language.Term.var (Sum.inr (Fin.last (L0 + 1)))
  let x'1 : Language.graph.Term (α ⊕ Fin (L0 + 1)) :=
    Language.Term.var (Sum.inr (Fin.last L0))
  obtain ⟨dom'1, hdom'1⟩ :=
    exists_dom_bd (fun i => lift1 (a'D (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x'1
  obtain ⟨dom2, hdom2⟩ :=
    exists_dom_bd (fun i => lift2 (aD (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x2
  obtain ⟨rel2, hrel2⟩ :=
    exists_rel_bd (fun i => lift2 (a'D i)) (fun i => lift2 (aD i))
      (fun j => lift2 (e1D j)) (fun j => lift2 (e2D j)) (fun s i => lift2 (dD s i)) x'2 x2
  let tot_φ : Language.graph.BoundedFormula α L0 := (dom'1.imp ((dom2 ⊓ rel2).ex)).all
  -- Order-preservation: ∀ x1' x2' x1 x2 (L0+4)
  let lift4 (t : Language.graph.Term (α ⊕ Fin L0)) := lift1 (lift1 (lift1 (lift1 t)))
  let x1'4 : Language.graph.Term (α ⊕ Fin (L0 + 4)) :=
    Language.Term.var (Sum.inr (Fin.last L0).castSucc.castSucc.castSucc)
  let x2'4 : Language.graph.Term (α ⊕ Fin (L0 + 4)) :=
    Language.Term.var (Sum.inr (Fin.last (L0 + 1)).castSucc.castSucc)
  let x1_4 : Language.graph.Term (α ⊕ Fin (L0 + 4)) :=
    Language.Term.var (Sum.inr (Fin.last (L0 + 2)).castSucc)
  let x2_4 : Language.graph.Term (α ⊕ Fin (L0 + 4)) :=
    Language.Term.var (Sum.inr (Fin.last (L0 + 3)))
  obtain ⟨dom_x1', hdom_x1'⟩ :=
    exists_dom_bd (fun i => lift4 (a'D (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x1'4
  obtain ⟨dom_x2', hdom_x2'⟩ :=
    exists_dom_bd (fun i => lift4 (a'D (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x2'4
  obtain ⟨dom_x1, hdom_x1⟩ :=
    exists_dom_bd (fun i => lift4 (aD (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x1_4
  obtain ⟨dom_x2, hdom_x2⟩ :=
    exists_dom_bd (fun i => lift4 (aD (Fin.castAdd q (Fin.castAdd (q - 2) i)))) x2_4
  obtain ⟨rel_1, hrel_1⟩ :=
    exists_rel_bd (fun i => lift4 (a'D i)) (fun i => lift4 (aD i))
      (fun j => lift4 (e1D j)) (fun j => lift4 (e2D j)) (fun s i => lift4 (dD s i)) x1'4 x1_4
  obtain ⟨rel_2, hrel_2⟩ :=
    exists_rel_bd (fun i => lift4 (a'D i)) (fun i => lift4 (aD i))
      (fun j => lift4 (e1D j)) (fun j => lift4 (e2D j)) (fun s i => lift4 (dD s i)) x2'4 x2_4
  obtain ⟨lt', hlt'⟩ :=
    exists_lt_bd (fun j => lift4 (a'D (Fin.castAdd q (Fin.natAdd q j))))
      (fun i => lift4 (a'D (Fin.natAdd (q + (q - 2)) i))) x1'4 x2'4
  obtain ⟨lt, hlt⟩ :=
    exists_lt_bd (fun j => lift4 (aD (Fin.castAdd q (Fin.natAdd q j))))
      (fun i => lift4 (aD (Fin.natAdd (q + (q - 2)) i))) x1_4 x2_4
  let mono_φ : Language.graph.BoundedFormula α L0 :=
    ((((dom_x1'.imp (dom_x2'.imp (dom_x1.imp (dom_x2.imp
      (rel_1.imp (rel_2.imp (lt'.imp lt))))))).all).all).all).all
  obtain ⟨φD, hφD⟩ := exists_exMany (30 * q) (tot_φ ⊓ mono_φ)
  obtain ⟨φ2, hφ2⟩ := exists_exMany (q - 1) φD
  obtain ⟨φ1, hφ1⟩ := exists_exMany (q - 1) φ2
  refine ⟨φ1, fun {V} G v xs => ?_⟩
  let := G.structure
  have hev_castAdd : ∀ {m k : ℕ} (t : Language.graph.Term (α ⊕ Fin m))
      (us : Fin m → V) (ws : Fin k → V),
      (t.relabel (Sum.map id (Fin.castAdd k))).realize (Sum.elim v (Fin.append us ws)) =
        t.realize (Sum.elim v us) := by
    intro m k t us ws
    rw [Language.Term.realize_relabel]
    congr 1
    ext z
    cases z with
    | inl a₀ => rfl
    | inr i => simp [Fin.append_left]
  rw [hφ1 G v xs]
  refine exists_congr fun e₁ => ?_
  rw [hφ2 G v (Fin.append xs e₁)]
  refine exists_congr fun e₂ => ?_
  rw [hφD G v (Fin.append (Fin.append xs e₁) e₂)]
  let xs2 : Fin L2 → V := Fin.append (Fin.append xs e₁) e₂
  have hevAll : ∀ (t : Language.graph.Term (α ⊕ Fin l)) (ys : Fin (30 * q) → V),
      (liftAll t).realize (Sum.elim v (Fin.append xs2 ys)) = t.realize (Sum.elim v xs) := by
    intro t ys
    dsimp only [liftAll, liftD, liftE2, liftE1, xs2]
    rw [hev_castAdd, hev_castAdd, hev_castAdd]
  have hevAll1 : ∀ (t : Language.graph.Term (α ⊕ Fin l)) (ys : Fin (30 * q) → V) (z₁ : V),
      (lift1 (liftAll t)).realize (Sum.elim v (Fin.snoc (Fin.append xs2 ys) z₁)) =
        t.realize (Sum.elim v xs) := by
    intro t ys z₁
    rw [realize_lift_term, hevAll]
  have hevAll2 : ∀ (t : Language.graph.Term (α ⊕ Fin l)) (ys : Fin (30 * q) → V) (z₁ z₂ : V),
      (lift2 (liftAll t)).realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.append xs2 ys) z₁) z₂)) =
        t.realize (Sum.elim v xs) := by
    intro t ys z₁ z₂
    simp only [lift2, lift1, realize_lift_term, hevAll]
  have hevAll4 : ∀ (t : Language.graph.Term (α ⊕ Fin l)) (ys : Fin (30 * q) → V) (z₁ z₂ z₃ z₄ : V),
      (lift4 (liftAll t)).realize
          (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.append xs2 ys) z₁) z₂) z₃) z₄)) =
        t.realize (Sum.elim v xs) := by
    intro t ys z₁ z₂ z₃ z₄
    simp only [lift4, lift1, realize_lift_term, hevAll]
  have he1_0 : ∀ (j : Fin (q - 1)) (ys : Fin (30 * q) → V),
      (e1D j).realize (Sum.elim v (Fin.append xs2 ys)) = e₁ j := by
    intro j ys
    dsimp only [e1D, liftD, liftE2, xs2]
    rw [hev_castAdd, hev_castAdd]
    simp only [Language.Term.realize_var, Sum.elim_inr, Fin.append_right]
  have he2_0 : ∀ (j : Fin (q - 1)) (ys : Fin (30 * q) → V),
      (e2D j).realize (Sum.elim v (Fin.append xs2 ys)) = e₂ j := by
    intro j ys
    dsimp only [e2D, liftD, xs2]
    rw [hev_castAdd]
    simp only [Language.Term.realize_var, Sum.elim_inr, Fin.append_right]
  have he1_2 : ∀ (j : Fin (q - 1)) (ys : Fin (30 * q) → V) (z₁ z₂ : V),
      (lift2 (e1D j)).realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.append xs2 ys) z₁) z₂)) = e₁ j := by
    intro j ys z₁ z₂
    simp only [lift2, lift1, realize_lift_term, he1_0]
  have he2_2 : ∀ (j : Fin (q - 1)) (ys : Fin (30 * q) → V) (z₁ z₂ : V),
      (lift2 (e2D j)).realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.append xs2 ys) z₁) z₂)) = e₂ j := by
    intro j ys z₁ z₂
    simp only [lift2, lift1, realize_lift_term, he2_0]
  have he1_4 : ∀ (j : Fin (q - 1)) (ys : Fin (30 * q) → V) (z₁ z₂ z₃ z₄ : V),
      (lift4 (e1D j)).realize
          (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.append xs2 ys) z₁) z₂) z₃) z₄)) =
        e₁ j := by
    intro j ys z₁ z₂ z₃ z₄
    simp only [lift4, lift1, realize_lift_term, he1_0]
  have he2_4 : ∀ (j : Fin (q - 1)) (ys : Fin (30 * q) → V) (z₁ z₂ z₃ z₄ : V),
      (lift4 (e2D j)).realize
          (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.append xs2 ys) z₁) z₂) z₃) z₄)) =
        e₂ j := by
    intro j ys z₁ z₂ z₃ z₄
    simp only [lift4, lift1, realize_lift_term, he2_0]
  have hd2 : ∀ (s : Fin 30) (i : Fin q) (ys : Fin (30 * q) → V) (z₁ z₂ : V),
      (lift2 (dD s i)).realize (Sum.elim v (Fin.snoc (Fin.snoc (Fin.append xs2 ys) z₁) z₂)) =
        ys (finProdFinEquiv (s, i)) := by
    intro s i ys z₁ z₂
    simp only [lift2, lift1, realize_lift_term, dD, Language.Term.realize_var, Sum.elim_inr,
      Fin.append_right]
  have hd4 : ∀ (s : Fin 30) (i : Fin q) (ys : Fin (30 * q) → V) (z₁ z₂ z₃ z₄ : V),
      (lift4 (dD s i)).realize
          (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.append xs2 ys) z₁) z₂) z₃) z₄)) =
        ys (finProdFinEquiv (s, i)) := by
    intro s i ys z₁ z₂ z₃ z₄
    simp only [lift4, lift1, realize_lift_term, dD, Language.Term.realize_var, Sum.elim_inr,
      Fin.append_right]
  have hbody : ∀ ys : Fin (30 * q) → V,
      (tot_φ ⊓ mono_φ).Realize v (Fin.append xs2 ys) ↔
        let d : Fin 30 → Fin q → V := fun s i => ys (finProdFinEquiv (s, i))
        let ev (t : Language.graph.Term (α ⊕ Fin l)) := t.realize (Sum.elim v xs)
        let dom (f : Fin ((q + (q - 2)) + q) → Language.graph.Term (α ⊕ Fin l)) (z : V) :=
          ∀ i : Fin q, G.Adj (ev (f (Fin.castAdd q (Fin.castAdd (q - 2) i)))) z
        let mem (f : Fin ((q + (q - 2)) + q) → Language.graph.Term (α ⊕ Fin l)) (u z : V) :=
          ∃ w : V, G.Adj u w ∧ G.Adj z w ∧
            ∀ j : Fin (q - 2), G.Adj (ev (f (Fin.castAdd q (Fin.natAdd q j)))) w
        let lt (f : Fin ((q + (q - 2)) + q) → Language.graph.Term (α ⊕ Fin l)) (x y : V) :=
          (∀ w, (∀ i : Fin q, G.Adj (ev (f (Fin.natAdd (q + (q - 2)) i))) w) → mem f w y → mem f w x) ∧
          (∃ w, (∀ i : Fin q, G.Adj (ev (f (Fin.natAdd (q + (q - 2)) i))) w) ∧ mem f w x ∧ ¬ mem f w y)
        let rel (x' x : V) := ∃ w, (∃ s : Fin 30, ∀ i : Fin q, G.Adj (d s i) w) ∧
          (∃ u', G.Adj w u' ∧ (∀ j : Fin (q - 1), G.Adj (e₁ j) u') ∧
            ∀ z', dom a' z' → (mem a' u' z' ↔ z' = x')) ∧
          (∃ u, G.Adj w u ∧ (∀ j : Fin (q - 1), G.Adj (e₂ j) u) ∧
            ∀ z, dom a z → (mem a u z ↔ z = x))
        (∀ x', dom a' x' → ∃ x, dom a x ∧ rel x' x) ∧
        (∀ x₁' x₂' x₁ x₂, dom a' x₁' → dom a' x₂' → dom a x₁ → dom a x₂ →
          rel x₁' x₁ → rel x₂' x₂ → lt a' x₁' x₂' → lt a x₁ x₂) := by
    intro ys
    simp only [tot_φ, mono_φ, Language.BoundedFormula.realize_inf,
      Language.BoundedFormula.realize_all, Language.BoundedFormula.realize_ex,
      Language.BoundedFormula.realize_imp]
    refine and_congr ?_ ?_
    · refine forall_congr' fun x' => imp_congr ?_ ?_
      · rw [hdom'1 G v _]
        simp only [a'D, x'1, hevAll1, Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
      · refine exists_congr fun x => and_congr ?_ ?_
        · rw [hdom2 G v _]
          simp only [aD, x2, hevAll2, Language.Term.realize_var, Sum.elim_inr, Fin.snoc_last]
        · rw [hrel2 G v _]
          simp only [a'D, aD, x'2, x2, hevAll2, he1_2, he2_2, hd2, Language.Term.realize_var,
            Sum.elim_inr, Fin.snoc_castSucc, Fin.snoc_last]
    · refine forall_congr' fun x₁' => forall_congr' fun x₂' =>
        forall_congr' fun x₁ => forall_congr' fun x₂ => ?_
      rw [hdom_x1' G v _, hdom_x2' G v _, hdom_x1 G v _, hdom_x2 G v _,
        hrel_1 G v _, hrel_2 G v _, hlt' G v _, hlt G v _]
      have hx1' : x1'4.realize
          (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.append xs2 ys) x₁') x₂') x₁) x₂)) = x₁' := by
        simp [x1'4, L0]
      have hx2' : x2'4.realize
          (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.append xs2 ys) x₁') x₂') x₁) x₂)) = x₂' := by
        simp [x2'4, L0]
      have hx1 : x1_4.realize
          (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.append xs2 ys) x₁') x₂') x₁) x₂)) = x₁ := by
        simp [x1_4, L0]
      have hx2 : x2_4.realize
          (Sum.elim v (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.append xs2 ys) x₁') x₂') x₁) x₂)) = x₂ := by
        simp [x2_4, L0]
      simp only [a'D, aD, hevAll4, he1_4, he2_4, hd4, hx1', hx2', hx1, hx2]
  constructor
  · rintro ⟨ys, hys⟩
    exact ⟨fun s i => ys (finProdFinEquiv (s, i)), (hbody ys).mp hys⟩
  · rintro ⟨d, hd⟩
    let ys : Fin (30 * q) → V := fun idx => d (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2
    refine ⟨ys, (hbody ys).mpr ?_⟩
    simpa only [ys, Equiv.symm_apply_apply] using hd

lemma exists_fo_package (q : ℕ) :
    let k := (q + (q - 2)) + q
    ∃ (valid_φ : Language.graph.Formula (Fin k))
      (dom_φ : Language.graph.Formula (Fin (k + 1)))
      (lt_φ : Language.graph.Formula (Fin (k + 2)))
      (mem_φ : Language.graph.Formula (Fin (k + 2))),
      ∀ {V : Type} (G : SimpleGraph V),
        let dom (a : Fin k → V) (x : V) :=
          ∀ i : Fin q, G.Adj (a (Fin.castAdd q (Fin.castAdd (q - 2) i))) x
        let mem (a : Fin k → V) (u x : V) :=
          ∃ w : V, G.Adj u w ∧ G.Adj x w ∧
            ∀ j : Fin (q - 2), G.Adj (a (Fin.castAdd q (Fin.natAdd q j))) w
        let lt (a : Fin k → V) (x y : V) :=
          (∀ w, (∀ i : Fin q, G.Adj (a (Fin.natAdd (q + (q - 2)) i)) w) → mem a w y → mem a w x) ∧
          (∃ w, (∀ i : Fin q, G.Adj (a (Fin.natAdd (q + (q - 2)) i)) w) ∧ mem a w x ∧ ¬ mem a w y)
        let base (a : Fin k → V) : Prop :=
          Function.Injective a ∧ (∃ x, dom a x) ∧
          (∀ x y, dom a x → dom a y → lt a x y ∨ x = y ∨ lt a y x) ∧
          (∃ u, ∀ x, dom a x → ¬ mem a u x) ∧
          (∀ u, (∃ x, dom a x ∧ ¬ mem a u x) → ∃ w x, dom a x ∧ ¬ mem a u x ∧ mem a w x ∧
            (∀ y, dom a y → lt a y x → mem a u y ∧ ¬ mem a w y) ∧
            (∀ y, dom a y → lt a x y → (mem a u y ↔ mem a w y)))
        let embed (a' a : Fin k → V) : Prop :=
          ∃ (e₁ e₂ : Fin (q - 1) → V) (d : Fin 30 → Fin q → V),
            let rel (x' x : V) := ∃ w, (∃ s : Fin 30, ∀ i : Fin q, G.Adj (d s i) w) ∧
              (∃ u', G.Adj w u' ∧ (∀ j : Fin (q - 1), G.Adj (e₁ j) u') ∧
                ∀ z', dom a' z' → (mem a' u' z' ↔ z' = x')) ∧
              (∃ u, G.Adj w u ∧ (∀ j : Fin (q - 1), G.Adj (e₂ j) u) ∧
                ∀ z, dom a z → (mem a u z ↔ z = x))
            (∀ x', dom a' x' → ∃ x, dom a x ∧ rel x' x) ∧
            (∀ x₁' x₂' x₁ x₂, dom a' x₁' → dom a' x₂' → dom a x₁ → dom a x₂ →
              rel x₁' x₁ → rel x₂' x₂ → lt a' x₁' x₂' → lt a x₁ x₂)
        (∀ a x, @Language.Formula.Realize _ _ G.structure _ dom_φ (Fin.snoc a x) ↔ dom a x) ∧
        (∀ a u x, @Language.Formula.Realize _ _ G.structure _ mem_φ (Fin.snoc (Fin.snoc a u) x) ↔
          mem a u x) ∧
        (∀ a x y, @Language.Formula.Realize _ _ G.structure _ lt_φ (Fin.snoc (Fin.snoc a x) y) ↔
          lt a x y) ∧
        (∀ a, @Language.Formula.Realize _ _ G.structure _ valid_φ a ↔
          base a ∧ ∀ a', base a' → embed a' a) := by
  let k := (q + (q - 2)) + q
  -- dom_φ : Formula (Fin (k + 1))
  let domT (i : Fin q) : Language.graph.Term (Fin (k + 1) ⊕ Fin 0) :=
    Language.Term.var (Sum.inl (Fin.castAdd q (Fin.castAdd (q - 2) i)).castSucc)
  let domX : Language.graph.Term (Fin (k + 1) ⊕ Fin 0) :=
    Language.Term.var (Sum.inl (Fin.last k))
  obtain ⟨dom_φ, hdom_φ⟩ := exists_dom_bd domT domX
  -- mem_φ : Formula (Fin (k + 2))
  let memB (j : Fin (q - 2)) : Language.graph.Term (Fin (k + 2) ⊕ Fin 0) :=
    Language.Term.var (Sum.inl (Fin.castAdd q (Fin.natAdd q j)).castSucc.castSucc)
  let memU : Language.graph.Term (Fin (k + 2) ⊕ Fin 0) :=
    Language.Term.var (Sum.inl (Fin.last k).castSucc)
  let memX : Language.graph.Term (Fin (k + 2) ⊕ Fin 0) :=
    Language.Term.var (Sum.inl (Fin.last (k + 1)))
  obtain ⟨mem_φ, hmem_φ⟩ := exists_mem_bd memB memU memX
  -- lt_φ : Formula (Fin (k + 2))
  let ltC (i : Fin q) : Language.graph.Term (Fin (k + 2) ⊕ Fin 0) :=
    Language.Term.var (Sum.inl (Fin.natAdd (q + (q - 2)) i).castSucc.castSucc)
  obtain ⟨lt_φ, hlt_φ⟩ := exists_lt_bd memB ltC memU memX
  -- valid_φ : Formula (Fin k)
  let aFree0 (i : Fin k) : Language.graph.Term (Fin k ⊕ Fin 0) := Language.Term.var (Sum.inl i)
  obtain ⟨base_φ, hbase_φ⟩ := exists_base_bd aFree0
  let aFreeK (i : Fin k) : Language.graph.Term (Fin k ⊕ Fin (0 + k)) := Language.Term.var (Sum.inl i)
  let aBoundK (i : Fin k) : Language.graph.Term (Fin k ⊕ Fin (0 + k)) :=
    Language.Term.var (Sum.inr (Fin.natAdd 0 i))
  obtain ⟨base'_φ, hbase'_φ⟩ := exists_base_bd aBoundK
  obtain ⟨emb_φ, hemb_φ⟩ := exists_embed_bd aBoundK aFreeK
  obtain ⟨max_φ, hmax_φ⟩ := exists_allMany (n := 0) k (base'_φ.imp emb_φ)
  refine ⟨base_φ ⊓ max_φ, dom_φ, lt_φ, mem_φ, fun {V} G => ?_⟩
  let := G.structure
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a x
    rw [Language.Formula.Realize, hdom_φ G (Fin.snoc a x) default]
    simp only [domT, domX, Language.Term.realize_var, Sum.elim_inl, Fin.snoc_castSucc,
      Fin.snoc_last]
  · intro a u x
    rw [Language.Formula.Realize, hmem_φ G (Fin.snoc (Fin.snoc a u) x) default]
    simp only [memB, memU, memX, Language.Term.realize_var, Sum.elim_inl, Fin.snoc_castSucc,
      Fin.snoc_last]
  · intro a x y
    rw [Language.Formula.Realize, hlt_φ G (Fin.snoc (Fin.snoc a x) y) default]
    simp only [memB, ltC, memU, memX, Language.Term.realize_var, Sum.elim_inl, Fin.snoc_castSucc,
      Fin.snoc_last]
  · intro a
    rw [Language.Formula.Realize, Language.BoundedFormula.realize_inf, hbase_φ G a default,
      hmax_φ G a default]
    refine and_congr ?_ ?_
    · simp only [aFree0, Language.Term.realize_var, Sum.elim_inl]
    · refine forall_congr' fun a' => ?_
      rw [Language.BoundedFormula.realize_imp, hbase'_φ G a (Fin.append default a'),
        hemb_φ G a (Fin.append default a')]
      simp only [aFreeK, aBoundK, Language.Term.realize_var, Sum.elim_inl, Sum.elim_inr,
        Fin.append_right]

/- === Section 2: Unconditional Order Theory and Binary Counter Proof of UNIV === -/

lemma inclusion_lt_irrefl {V : Type} (inU : V → Prop) (mem : V → V → Prop) (x : V) :
    ¬ ((∀ w, inU w → mem w x → mem w x) ∧ (∃ w, inU w ∧ mem w x ∧ ¬ mem w x)) := by
  rintro ⟨_, w, _, h1, h2⟩
  exact h2 h1

lemma inclusion_lt_trans {V : Type} (inU : V → Prop) (mem : V → V → Prop) {x y z : V}
    (hxy : (∀ w, inU w → mem w y → mem w x) ∧ (∃ w, inU w ∧ mem w x ∧ ¬ mem w y))
    (hyz : (∀ w, inU w → mem w z → mem w y) ∧ (∃ w, inU w ∧ mem w y ∧ ¬ mem w z)) :
    (∀ w, inU w → mem w z → mem w x) ∧ (∃ w, inU w ∧ mem w x ∧ ¬ mem w z) := by
  refine ⟨fun w hw hz => hxy.1 w hw (hyz.1 w hw hz), ?_⟩
  rcases hxy.2 with ⟨w, hw, hwx, hnwy⟩
  exact ⟨w, hw, hwx, fun hwz => hnwy (hyz.1 w hw hwz)⟩

lemma exists_min_of_strictOrder {α : Type} [DecidableEq α] (D : Finset α)
    (lt : α → α → Prop)
    (hirrefl : ∀ x ∈ D, ¬ lt x x)
    (htrans : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, lt x y → lt y z → lt x z)
    (htri : ∀ x ∈ D, ∀ y ∈ D, lt x y ∨ x = y ∨ lt y x)
    (hne : D.Nonempty) :
    ∃ x₀ ∈ D, ∀ y ∈ D, y ≠ x₀ → lt x₀ y := by
  induction D using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hne)
  | insert a s ha ih =>
    by_cases hs : s.Nonempty
    · have hs_sub : ∀ x ∈ s, x ∈ insert a s := fun x hx => Finset.mem_insert_of_mem hx
      obtain ⟨m, hm_mem, hm_min⟩ := ih
        (fun x hx => hirrefl x (hs_sub x hx))
        (fun x hx y hy z hz => htrans x (hs_sub x hx) y (hs_sub y hy) z (hs_sub z hz))
        (fun x hx y hy => htri x (hs_sub x hx) y (hs_sub y hy)) hs
      rcases htri a (Finset.mem_insert_self a s) m (hs_sub m hm_mem) with ham | rfl | hma
      · refine ⟨a, Finset.mem_insert_self a s, fun y hy hya => ?_⟩
        rcases Finset.mem_insert.mp hy with rfl | hys
        · exact False.elim (hya rfl)
        · by_cases hym : y = m
          · rw [hym]; exact ham
          · exact htrans a (Finset.mem_insert_self a s) m (hs_sub m hm_mem) y (hs_sub y hys)
              ham (hm_min y hys hym)
      · exact False.elim (ha hm_mem)
      · refine ⟨m, hs_sub m hm_mem, fun y hy hym => ?_⟩
        rcases Finset.mem_insert.mp hy with rfl | hys
        · exact hma
        · exact hm_min y hys hym
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      refine ⟨a, Finset.mem_singleton_self a, fun y hy hya => ?_⟩
      exact False.elim (hya (Finset.mem_singleton.mp hy))

lemma exists_strictMono_enum {α : Type} [DecidableEq α] (m : ℕ) :
    ∀ (D : Finset α) (lt : α → α → Prop), D.card = m →
      (∀ x ∈ D, ¬ lt x x) →
      (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, lt x y → lt y z → lt x z) →
      (∀ x ∈ D, ∀ y ∈ D, lt x y ∨ x = y ∨ lt y x) →
      ∃ e : Fin m → α, (∀ i, e i ∈ D) ∧ (∀ x ∈ D, ∃ i, e i = x) ∧
        (∀ i j : Fin m, i < j → lt (e i) (e j)) := by
  induction m with
  | zero =>
    intro D _ hcard _ _ _
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, fun x hx => ?_, fun i => Fin.elim0 i⟩
    have hpos : 0 < D.card := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  | succ m ih =>
    intro D lt hcard hirrefl htrans htri
    have hne : D.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x₀, hx₀D, hx₀min⟩ := exists_min_of_strictOrder D lt hirrefl htrans htri hne
    let D' := D.erase x₀
    have hD'sub : ∀ x ∈ D', x ∈ D := fun x hx => Finset.mem_of_mem_erase hx
    have hD'card : D'.card = m := by
      dsimp only [D']
      rw [Finset.card_erase_of_mem hx₀D]
      omega
    obtain ⟨e', he'mem, he'surj, he'mono⟩ := ih D' lt hD'card
      (fun x hx => hirrefl x (hD'sub x hx))
      (fun x hx y hy z hz => htrans x (hD'sub x hx) y (hD'sub y hy) z (hD'sub z hz))
      (fun x hx y hy => htri x (hD'sub x hx) y (hD'sub y hy))
    refine ⟨Fin.cons x₀ e', ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases hx₀D (fun j => hD'sub _ (he'mem j)) i
    · intro x hx
      by_cases hxx₀ : x = x₀
      · exact ⟨0, by simp [hxx₀]⟩
      · obtain ⟨j, hj⟩ := he'surj x (Finset.mem_erase.mpr ⟨hxx₀, hx⟩)
        exact ⟨j.succ, by simpa using hj⟩
    · intro i j hij
      revert hij
      refine Fin.cases ?_ ?_ i
      · refine Fin.cases (fun h => False.elim (lt_irrefl _ h)) (fun b _ => ?_) j
        simp only [Fin.cons_zero, Fin.cons_succ]
        have hbD' := he'mem b
        exact hx₀min (e' b) (hD'sub _ hbD') (Finset.ne_of_mem_erase hbD')
      · intro a
        refine Fin.cases (fun h => False.elim (Fin.not_lt_zero _ h)) (fun b hab => ?_) j
        simp only [Fin.cons_succ]
        exact he'mono a b (Fin.succ_lt_succ_iff.mp hab)

lemma sum_two_pow_fin (r : ℕ) : (∑ i : Fin r, 2 ^ i.val) + 1 = 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have h2 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
    omega

lemma sum_two_pow_lt_fin {m : ℕ} (p : Fin m) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin m => i < p), 2 ^ i.val) + 1 = 2 ^ p.val := by
  let f : Fin p.val → Fin m := fun j => ⟨j.val, lt_trans j.isLt p.isLt⟩
  have hbij :
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i < p), 2 ^ i.val) =
        ∑ j : Fin p.val, 2 ^ j.val := by
    symm
    refine Finset.sum_nbij f ?_ ?_ ?_ ?_
    · intro j _
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, j.isLt⟩
    · intro j₁ _ j₂ _ heq
      ext
      simpa [f] using congrArg Fin.val heq
    · intro i hi
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      exact ⟨⟨i.val, hi.2⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by ext; rfl⟩
    · intro _ _
      rfl
  rw [hbij]
  exact sum_two_pow_fin p.val

lemma zero_succ_implies_univ {n : ℕ} (D : Finset (Fin n)) (lt mem : Fin n → Fin n → Prop)
    (hirrefl : ∀ x ∈ D, ¬ lt x x)
    (htrans : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, lt x y → lt y z → lt x z)
    (htri : ∀ x ∈ D, ∀ y ∈ D, lt x y ∨ x = y ∨ lt y x)
    (hzero : ∃ v : Fin n, ∀ x ∈ D, ¬ mem v x)
    (hsucc : ∀ v : Fin n, (∃ x ∈ D, ¬ mem v x) →
      ∃ w x : Fin n, x ∈ D ∧ ¬ mem v x ∧ mem w x ∧
        (∀ y ∈ D, lt y x → mem v y ∧ ¬ mem w y) ∧
        (∀ y ∈ D, lt x y → (mem v y ↔ mem w y))) :
    ∀ S ⊆ D, ∃ v : Fin n, ∀ x ∈ D, mem v x ↔ x ∈ S := by
  classical
  let m := D.card
  obtain ⟨e, he_mem, he_surj, he_mono⟩ := exists_strictMono_enum m D lt rfl hirrefl htrans htri
  have he_lt_iff : ∀ i j : Fin m, lt (e i) (e j) ↔ i < j := by
    intro i j
    constructor
    · intro hlt
      by_contra hnot
      have hle : j ≤ i := le_of_not_gt hnot
      rcases lt_or_eq_of_le hle with hji | rfl
      · exact hirrefl (e i) (he_mem i)
          (htrans (e i) (he_mem i) (e j) (he_mem j) (e i) (he_mem i) hlt (he_mono j i hji))
      · exact hirrefl (e j) (he_mem j) hlt
    · exact he_mono i j
  let code : Finset (Fin n) → ℕ := fun S =>
    ∑ i : Fin m, if e i ∈ S then 2 ^ i.val else 0
  have hcode_lt : ∀ S : Finset (Fin n), code S < 2 ^ m := by
    intro S
    have hle : code S ≤ ∑ i : Fin m, 2 ^ i.val := by
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : e i ∈ S <;> simp [hi]
    have hsum := sum_two_pow_fin m
    omega
  have hcode_inj : ∀ S₁ S₂ : Finset (Fin n), S₁ ⊆ D → S₂ ⊆ D → code S₁ = code S₂ → S₁ = S₂ := by
    intro S₁ S₂ h1 h2 heq
    by_contra hne
    let diff : Finset (Fin m) :=
      Finset.univ.filter (fun i : Fin m => ¬ (e i ∈ S₁ ↔ e i ∈ S₂))
    have hdiff_ne : diff.Nonempty := by
      have hex : ∃ x ∈ D, ¬ (x ∈ S₁ ↔ x ∈ S₂) := by
        by_contra hall
        push Not at hall
        apply hne
        ext x
        by_cases hxD : x ∈ D
        · exact hall x hxD
        · exact ⟨fun hx1 => False.elim (hxD (h1 hx1)), fun hx2 => False.elim (hxD (h2 hx2))⟩
      obtain ⟨x, hxD, hxne⟩ := hex
      obtain ⟨i, rfl⟩ := he_surj x hxD
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxne⟩⟩
    let p : Fin m := diff.max' hdiff_ne
    have hp_diff : ¬ (e p ∈ S₁ ↔ e p ∈ S₂) := (Finset.mem_filter.mp (Finset.max'_mem diff hdiff_ne)).2
    have hgt_eq : ∀ i : Fin m, p < i → (e i ∈ S₁ ↔ e i ∈ S₂) := by
      intro i hip
      by_contra hni
      have hmem : i ∈ diff := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hni⟩
      exact not_le_of_gt hip (Finset.le_max' diff i hmem)
    let splitSum (S : Finset (Fin n)) :=
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i < p), if e i ∈ S then 2 ^ i.val else 0) +
      (if e p ∈ S then 2 ^ p.val else 0) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => p < i), if e i ∈ S then 2 ^ i.val else 0)
    have hsplit : ∀ S : Finset (Fin n), code S = splitSum S := by
      intro S
      dsimp only [code, splitSum]
      have h1 := (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i < p)
        (fun i => if e i ∈ S then 2 ^ i.val else 0)).symm
      have h2 :
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i < p), if e i ∈ S then 2 ^ i.val else 0) =
            (if e p ∈ S then 2 ^ p.val else 0) +
              (∑ i ∈ Finset.univ.filter (fun i : Fin m => p < i), if e i ∈ S then 2 ^ i.val else 0) := by
        have hp_in : p ∈ Finset.univ.filter (fun i : Fin m => ¬ i < p) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ p, lt_irrefl p⟩
        rw [← Finset.add_sum_erase _ _ hp_in]
        congr 1
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext i
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hne_p, hnotlt⟩
          exact lt_of_le_of_ne (le_of_not_gt hnotlt) (Ne.symm hne_p)
        · intro hlt
          exact ⟨ne_of_gt hlt, not_lt_of_gt hlt⟩
      rw [h1, h2, add_assoc]
    have htail :
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => p < i), if e i ∈ S₁ then 2 ^ i.val else 0) =
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => p < i), if e i ∈ S₂ then 2 ^ i.val else 0) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hip : p < i := (Finset.mem_filter.mp hi).2
      simp [hgt_eq i hip]
    have hlow_lt : ∀ S : Finset (Fin n),
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i < p), if e i ∈ S then 2 ^ i.val else 0) <
          2 ^ p.val := by
      intro S
      have hle :
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i < p), if e i ∈ S then 2 ^ i.val else 0) ≤
            ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < p), 2 ^ i.val := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hi : e i ∈ S <;> simp [hi]
      have hsum := sum_two_pow_lt_fin p
      omega
    rw [hsplit S₁, hsplit S₂] at heq
    dsimp only [splitSum] at heq
    rw [htail] at heq
    have hl1 := hlow_lt S₁
    have hl2 := hlow_lt S₂
    by_cases h1p : e p ∈ S₁ <;> by_cases h2p : e p ∈ S₂
    · exact hp_diff ⟨fun _ => h2p, fun _ => h1p⟩
    · simp only [h1p, h2p, ite_true, ite_false] at heq; omega
    · simp only [h1p, h2p, ite_true, ite_false] at heq; omega
    · exact hp_diff ⟨fun h => False.elim (h1p h), fun h => False.elim (h2p h)⟩
  have hreach : ∀ r : ℕ, r < 2 ^ m → ∃ v : Fin n, code (D.filter (mem v)) = r := by
    intro r
    induction r with
    | zero =>
      intro _
      obtain ⟨v, hv⟩ := hzero
      refine ⟨v, ?_⟩
      have hemp : D.filter (mem v) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        exact fun x hx => hv x hx
      simp [code, hemp]
    | succ r ih =>
      intro hr
      obtain ⟨v, hv⟩ := ih (Nat.lt_of_succ_lt hr)
      have hnot_full : ∃ x ∈ D, ¬ mem v x := by
        by_contra hall
        push Not at hall
        have hfull : D.filter (mem v) = D := Finset.filter_true_of_mem hall
        have hcode_full : code D = ∑ i : Fin m, 2 ^ i.val := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [he_mem i]
        rw [hfull, hcode_full] at hv
        have hsum := sum_two_pow_fin m
        omega
      obtain ⟨w, x, hxD, hvnx, hwx, hlow, hhigh⟩ := hsucc v hnot_full
      obtain ⟨p, rfl⟩ := he_surj x hxD
      refine ⟨w, ?_⟩
      let Sv := D.filter (mem v)
      let Sw := D.filter (mem w)
      have hsplit : ∀ S : Finset (Fin n),
          code S =
            (∑ i ∈ Finset.univ.filter (fun i : Fin m => i < p), if e i ∈ S then 2 ^ i.val else 0) +
            (if e p ∈ S then 2 ^ p.val else 0) +
            (∑ i ∈ Finset.univ.filter (fun i : Fin m => p < i), if e i ∈ S then 2 ^ i.val else 0) := by
        intro S
        dsimp only [code]
        have h1 := (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i < p)
          (fun i => if e i ∈ S then 2 ^ i.val else 0)).symm
        have h2 :
            (∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i < p), if e i ∈ S then 2 ^ i.val else 0) =
              (if e p ∈ S then 2 ^ p.val else 0) +
                (∑ i ∈ Finset.univ.filter (fun i : Fin m => p < i), if e i ∈ S then 2 ^ i.val else 0) := by
          have hp_in : p ∈ Finset.univ.filter (fun i : Fin m => ¬ i < p) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ p, lt_irrefl p⟩
          rw [← Finset.add_sum_erase _ _ hp_in]
          congr 1
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext i
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hne_p, hnotlt⟩
            exact lt_of_le_of_ne (le_of_not_gt hnotlt) (Ne.symm hne_p)
          · intro hlt
            exact ⟨ne_of_gt hlt, not_lt_of_gt hlt⟩
        rw [h1, h2, add_assoc]
      have hv_low :
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i < p), if e i ∈ Sv then 2 ^ i.val else 0) =
            ∑ i ∈ Finset.univ.filter (fun i : Fin m => i < p), 2 ^ i.val := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hip : i < p := (Finset.mem_filter.mp hi).2
        have hmem_v : e i ∈ Sv :=
          Finset.mem_filter.mpr ⟨he_mem i, (hlow (e i) (he_mem i) ((he_lt_iff i p).mpr hip)).1⟩
        simp [hmem_v]
      have hw_low :
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i < p), if e i ∈ Sw then 2 ^ i.val else 0) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hip : i < p := (Finset.mem_filter.mp hi).2
        have hnmem_w : e i ∉ Sw := by
          intro hmem
          exact (hlow (e i) (he_mem i) ((he_lt_iff i p).mpr hip)).2 (Finset.mem_filter.mp hmem).2
        simp [hnmem_w]
      have htail :
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => p < i), if e i ∈ Sw then 2 ^ i.val else 0) =
            (∑ i ∈ Finset.univ.filter (fun i : Fin m => p < i), if e i ∈ Sv then 2 ^ i.val else 0) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hpi : p < i := (Finset.mem_filter.mp hi).2
        have hiff : e i ∈ Sw ↔ e i ∈ Sv := by
          simp only [Sw, Sv, Finset.mem_filter, he_mem i, true_and]
          exact (hhigh (e i) (he_mem i) ((he_lt_iff p i).mpr hpi)).symm
        simp [hiff]
      have hv_p : e p ∉ Sv := fun hm => hvnx (Finset.mem_filter.mp hm).2
      have hw_p : e p ∈ Sw := Finset.mem_filter.mpr ⟨hxD, hwx⟩
      have hsum_p := sum_two_pow_lt_fin p
      have hcv := hsplit Sv
      have hcw := hsplit Sw
      rw [hv_low] at hcv
      rw [hw_low, htail] at hcw
      simp only [hv_p, hw_p, ite_true, ite_false] at hcv hcw
      change code Sw = r + 1
      change code Sv = r at hv
      omega
  intro S hSD
  obtain ⟨v, hv⟩ := hreach (code S) (hcode_lt S)
  have hEq : D.filter (mem v) = S := hcode_inj _ _ (Finset.filter_subset _ _) hSD hv
  refine ⟨v, fun x hxD => ?_⟩
  rw [← hEq, Finset.mem_filter]
  exact ⟨fun h => ⟨hxD, h⟩, fun h => h.2⟩

/- === Section 3: Order-Embedding Cardinality Comparison and Probability Intersection === -/

lemma card_le_of_order_embed {n : ℕ} (D' D : Finset (Fin n))
    (lt' lt : Fin n → Fin n → Prop) (rel : Fin n → Fin n → Prop)
    (htri' : ∀ x ∈ D', ∀ y ∈ D', lt' x y ∨ x = y ∨ lt' y x)
    (hirrefl : ∀ x ∈ D, ¬ lt x x)
    (htot : ∀ x' ∈ D', ∃ x ∈ D, rel x' x)
    (hmono : ∀ x₁' ∈ D', ∀ x₂' ∈ D', ∀ x₁ ∈ D, ∀ x₂ ∈ D,
      rel x₁' x₁ → rel x₂' x₂ → lt' x₁' x₂' → lt x₁ x₂) :
    D'.card ≤ D.card := by
  classical
  let g : Fin n → Fin n := fun x' =>
    if hx' : x' ∈ D' then Classical.choose (htot x' hx') else x'
  have hg_mem : Set.MapsTo g (D' : Set (Fin n)) (D : Set (Fin n)) := by
    intro x' hx'
    rw [Finset.mem_coe] at hx' ⊢
    simp only [g, hx', dite_true]
    exact (Classical.choose_spec (htot x' hx')).1
  have hg_rel : ∀ x' ∈ D', rel x' (g x') := by
    intro x' hx'
    simp only [g, hx', dite_true]
    exact (Classical.choose_spec (htot x' hx')).2
  have hg_inj : Set.InjOn g (D' : Set (Fin n)) := by
    intro x₁' hx₁' x₂' hx₂' heq
    rw [Finset.mem_coe] at hx₁' hx₂'
    rcases htri' x₁' hx₁' x₂' hx₂' with h12 | hEq | h21
    · have hlt := hmono x₁' hx₁' x₂' hx₂' (g x₁') (hg_mem hx₁') (g x₂') (hg_mem hx₂')
        (hg_rel x₁' hx₁') (hg_rel x₂' hx₂') h12
      rw [heq] at hlt
      exact False.elim (hirrefl (g x₂') (hg_mem hx₂') hlt)
    · exact hEq
    · have hlt := hmono x₂' hx₂' x₁' hx₁' (g x₂') (hg_mem hx₂') (g x₁') (hg_mem hx₁')
        (hg_rel x₂' hx₂') (hg_rel x₁' hx₁') h21
      rw [heq] at hlt
      exact False.elim (hirrefl (g x₂') (hg_mem hx₂') hlt)
  exact Finset.card_le_card_of_injOn g hg_mem hg_inj

lemma prob_inter_ge_three_fourths {n : ℕ} {α : ℝ} (hα : 0 < α)
    (E₁ E₂ : Set (SimpleGraph (Fin n)))
    (h1 : (7 : ENNReal) / 8 ≤ ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα E₁)
    (h2 : (7 : ENNReal) / 8 ≤ ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα E₂) :
    (3 : ENNReal) / 4 ≤ ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα (E₁ ∩ E₂) := by
  let μ := ShelahSpencerZeroOneLaw.sparseRandomGraph n α hα
  have hprob : IsProbabilityMeasure μ := by
    dsimp only [μ, ShelahSpencerZeroOneLaw.sparseRandomGraph]
    infer_instance
  have hE1_m : MeasurableSet E₁ :=
    OMA.R_ShelahSpencerZeroOneLaw_zeroOne_rational_R1.measurableSet_simpleGraph E₁
  have hE2_m : MeasurableSet E₂ :=
    OMA.R_ShelahSpencerZeroOneLaw_zeroOne_rational_R1.measurableSet_simpleGraph E₂
  have h8_ne : (8 : ENNReal) ≠ 0 := by norm_num
  have h8_top : (8 : ENNReal) ≠ ⊤ := by simp
  have h4_ne : (4 : ENNReal) ≠ 0 := by norm_num
  have h4_top : (4 : ENNReal) ≠ ⊤ := by simp
  have hsum18 : (7 : ENNReal) / 8 + 1 / 8 = 1 := by
    rw [← ENNReal.add_div, show (7 : ENNReal) + 1 = 8 by norm_num, ENNReal.div_self h8_ne h8_top]
  have hsum28 : (1 : ENNReal) / 8 + 1 / 8 = 1 / 4 := by
    have h18_top : (1 : ENNReal) / 8 ≠ ⊤ := ENNReal.div_ne_top (by simp) h8_ne
    have h14_top : (1 : ENNReal) / 4 ≠ ⊤ := ENNReal.div_ne_top (by simp) h4_ne
    rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨h18_top, h18_top⟩) h14_top,
      ENNReal.toReal_add h18_top h18_top, ENNReal.toReal_div, ENNReal.toReal_div,
      ENNReal.toReal_one, ENNReal.toReal_ofNat, ENNReal.toReal_ofNat]
    norm_num
  have hsum34 : (3 : ENNReal) / 4 + 1 / 4 = 1 := by
    rw [← ENNReal.add_div, show (3 : ENNReal) + 1 = 4 by norm_num, ENNReal.div_self h4_ne h4_top]
  have h1c : μ E₁ᶜ ≤ 1 / 8 := by
    rw [prob_compl_eq_one_sub hE1_m]
    exact tsub_le_iff_left.mpr (le_trans (le_of_eq hsum18.symm) (add_le_add h1 le_rfl))
  have h2c : μ E₂ᶜ ≤ 1 / 8 := by
    rw [prob_compl_eq_one_sub hE2_m]
    exact tsub_le_iff_left.mpr (le_trans (le_of_eq hsum18.symm) (add_le_add h2 le_rfl))
  have h12c : μ (E₁ ∩ E₂)ᶜ ≤ 1 / 4 := by
    rw [Set.compl_inter]
    exact le_trans (measure_union_le E₁ᶜ E₂ᶜ) (le_trans (add_le_add h1c h2c) (le_of_eq hsum28))
  have h12_ne_top : μ (E₁ ∩ E₂)ᶜ ≠ ⊤ := ne_top_of_le_ne_top (by simp) h12c
  rw [← compl_compl (E₁ ∩ E₂), prob_compl_eq_one_sub (hE1_m.inter hE2_m).compl]
  exact ENNReal.le_sub_of_add_le_right h12_ne_top
    (le_trans (add_le_add le_rfl h12c) (le_of_eq hsum34))

/- === Section 4: Main Reduction Theorem === -/

theorem main : H1 → H2 → OMA.R_ShelahSpencerZeroOneLaw_zeroOne_rational_R1.H1 := by
  classical
  intro h1 h2 q hq hα
  let k : ℕ := (q + (q - 2)) + q
  obtain ⟨valid_φ, dom_φ, lt_φ, mem_φ, hpkg⟩ := exists_fo_package q
  refine ⟨k, valid_φ, dom_φ, lt_φ, mem_φ, ?_⟩
  obtain ⟨L₀, hL₀⟩ := h1 q hq hα
  obtain ⟨N₁, hN₁⟩ := h2 q hq hα
  constructor
  · rw [Filter.frequently_atTop]
    intro N₀
    let m : ℕ := max (max L₀ N₁) N₀
    let L : ℕ := 100 * m + 26
    have hL_ge_L0 : L₀ ≤ L := by dsimp only [L, m]; omega
    obtain ⟨n, hn_ge_L, hprob1⟩ := hL₀ L hL_ge_L0
    have hn_ge_N0 : N₀ ≤ n := by dsimp only [L, m] at hn_ge_L; omega
    have hn_ge_N1 : N₁ ≤ n := by dsimp only [L, m] at hn_ge_L; omega
    have hprob2 := hN₁ n hn_ge_N1
    refine ⟨n, hn_ge_N0, ?_⟩
    have hinter := prob_inter_ge_three_fourths hα _ _ hprob1 hprob2
    refine le_trans hinter (measure_mono ?_)
    rintro G ⟨⟨⟨a, hbase_a, hcard_a⟩, hmax_a⟩, hembed_all⟩
    obtain ⟨hdom_r, hmem_r, hlt_r, hvalid_r⟩ := hpkg G
    let D : Finset (Fin n) :=
      Finset.univ.filter (fun x : Fin n =>
        ∀ i : Fin q, G.Adj (a (Fin.castAdd q (Fin.castAdd (q - 2) i))) x)
    have hD_ncard :
        { x : Fin n | ∀ i : Fin q, G.Adj (a (Fin.castAdd q (Fin.castAdd (q - 2) i))) x }.ncard =
          D.card := by
      have hset :
          { x : Fin n | ∀ i : Fin q, G.Adj (a (Fin.castAdd q (Fin.castAdd (q - 2) i))) x } =
            (D : Set (Fin n)) := by
        ext x
        simp [D]
      rw [hset, Set.ncard_coe_finset]
    have hD_card : D.card = L := hD_ncard.symm.trans hcard_a
    have hvalid_a : @Language.Formula.Realize _ _ G.structure _ valid_φ a := by
      rw [hvalid_r a]
      refine ⟨hbase_a, fun a' hbase_a' => hembed_all a' a hbase_a' hbase_a ?_⟩
      rw [hcard_a]
      exact hmax_a a' hbase_a'
    have hdom_iff : ∀ x : Fin n, x ∈ D ↔ @Language.Formula.Realize _ _ G.structure _ dom_φ (Fin.snoc a x) := by
      intro x
      rw [hdom_r a x]
      simp [D]
    have hD_ne : D.Nonempty := by
      rcases hbase_a.2.1 with ⟨x, hx⟩
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    have hirrefl : ∀ x ∈ D,
        ¬ @Language.Formula.Realize _ _ G.structure _ lt_φ (Fin.snoc (Fin.snoc a x) x) := by
      intro x _
      rw [hlt_r a x x]
      exact inclusion_lt_irrefl
        (fun w => ∀ i : Fin q, G.Adj (a (Fin.natAdd (q + (q - 2)) i)) w)
        (fun w z => ∃ u, G.Adj w u ∧ G.Adj z u ∧
          ∀ j : Fin (q - 2), G.Adj (a (Fin.castAdd q (Fin.natAdd q j))) u) x
    have htrans : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
        @Language.Formula.Realize _ _ G.structure _ lt_φ (Fin.snoc (Fin.snoc a x) y) →
        @Language.Formula.Realize _ _ G.structure _ lt_φ (Fin.snoc (Fin.snoc a y) z) →
        @Language.Formula.Realize _ _ G.structure _ lt_φ (Fin.snoc (Fin.snoc a x) z) := by
      intro x _ y _ z _ hxy hyz
      rw [hlt_r a x y] at hxy
      rw [hlt_r a y z] at hyz
      rw [hlt_r a x z]
      exact inclusion_lt_trans
        (fun w => ∀ i : Fin q, G.Adj (a (Fin.natAdd (q + (q - 2)) i)) w)
        (fun w z => ∃ u, G.Adj w u ∧ G.Adj z u ∧
          ∀ j : Fin (q - 2), G.Adj (a (Fin.castAdd q (Fin.natAdd q j))) u) hxy hyz
    have htri : ∀ x ∈ D, ∀ y ∈ D,
        @Language.Formula.Realize _ _ G.structure _ lt_φ (Fin.snoc (Fin.snoc a x) y) ∨
        x = y ∨
        @Language.Formula.Realize _ _ G.structure _ lt_φ (Fin.snoc (Fin.snoc a y) x) := by
      intro x hx y hy
      rw [hlt_r a x y, hlt_r a y x]
      exact hbase_a.2.2.1 x y (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
    have huniv : ∀ S ⊆ D, ∃ v : Fin n, ∀ x ∈ D,
        @Language.Formula.Realize _ _ G.structure _ mem_φ (Fin.snoc (Fin.snoc a v) x) ↔ x ∈ S := by
      have hzero : ∃ v : Fin n, ∀ x ∈ D,
          ¬ @Language.Formula.Realize _ _ G.structure _ mem_φ (Fin.snoc (Fin.snoc a v) x) := by
        rcases hbase_a.2.2.2.1 with ⟨v, hv⟩
        refine ⟨v, fun x hx => ?_⟩
        rw [hmem_r a v x]
        exact hv x (Finset.mem_filter.mp hx).2
      have hsucc : ∀ v : Fin n,
          (∃ x ∈ D, ¬ @Language.Formula.Realize _ _ G.structure _ mem_φ (Fin.snoc (Fin.snoc a v) x)) →
          ∃ w x : Fin n, x ∈ D ∧
            ¬ @Language.Formula.Realize _ _ G.structure _ mem_φ (Fin.snoc (Fin.snoc a v) x) ∧
            @Language.Formula.Realize _ _ G.structure _ mem_φ (Fin.snoc (Fin.snoc a w) x) ∧
            (∀ y ∈ D,
              @Language.Formula.Realize _ _ G.structure _ lt_φ (Fin.snoc (Fin.snoc a y) x) →
              @Language.Formula.Realize _ _ G.structure _ mem_φ (Fin.snoc (Fin.snoc a v) y) ∧
              ¬ @Language.Formula.Realize _ _ G.structure _ mem_φ (Fin.snoc (Fin.snoc a w) y)) ∧
            (∀ y ∈ D,
              @Language.Formula.Realize _ _ G.structure _ lt_φ (Fin.snoc (Fin.snoc a x) y) →
              (@Language.Formula.Realize _ _ G.structure _ mem_φ (Fin.snoc (Fin.snoc a v) y) ↔
               @Language.Formula.Realize _ _ G.structure _ mem_φ (Fin.snoc (Fin.snoc a w) y))) := by
        intro v ⟨x₀, hx₀D, hvnx₀⟩
        rw [hmem_r a v x₀] at hvnx₀
        obtain ⟨w, x, hx_dom, hvnx, hwx, hlow, hhigh⟩ :=
          hbase_a.2.2.2.2 v ⟨x₀, (Finset.mem_filter.mp hx₀D).2, hvnx₀⟩
        refine ⟨w, x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx_dom⟩, ?_, ?_, ?_, ?_⟩
        · rw [hmem_r a v x]; exact hvnx
        · rw [hmem_r a w x]; exact hwx
        · intro y hy hlt
          rw [hlt_r a y x] at hlt
          rw [hmem_r a v y, hmem_r a w y]
          exact hlow y (Finset.mem_filter.mp hy).2 hlt
        · intro y hy hlt
          rw [hlt_r a x y] at hlt
          rw [hmem_r a v y, hmem_r a w y]
          exact hhigh y (Finset.mem_filter.mp hy).2 hlt
      exact zero_succ_implies_univ D
        (fun x y => @Language.Formula.Realize _ _ G.structure _ lt_φ (Fin.snoc (Fin.snoc a x) y))
        (fun v x => @Language.Formula.Realize _ _ G.structure _ mem_φ (Fin.snoc (Fin.snoc a v) x))
        hirrefl htrans htri hzero hsucc
    refine ⟨a, D, ⟨hvalid_a, hdom_iff, hD_ne, hirrefl, htrans, htri⟩, huniv, ?_, ?_⟩
    · rw [hD_card]; dsimp only [L]; omega
    · rw [hD_card]; dsimp only [L]; omega
  · rw [Filter.frequently_atTop]
    intro N₀
    let m : ℕ := max (max L₀ N₁) N₀
    let L : ℕ := 100 * m + 76
    have hL_ge_L0 : L₀ ≤ L := by dsimp only [L, m]; omega
    obtain ⟨n, hn_ge_L, hprob1⟩ := hL₀ L hL_ge_L0
    have hn_ge_N0 : N₀ ≤ n := by dsimp only [L, m] at hn_ge_L; omega
    have hn_ge_N1 : N₁ ≤ n := by dsimp only [L, m] at hn_ge_L; omega
    have hprob2 := hN₁ n hn_ge_N1
    refine ⟨n, hn_ge_N0, ?_⟩
    have hinter := prob_inter_ge_three_fourths hα _ _ hprob1 hprob2
    refine le_trans hinter (measure_mono ?_)
    rintro G ⟨⟨⟨aStar, hbase_star, hcard_star⟩, hmax_all⟩, _⟩
    obtain ⟨hdom_r, _, hlt_r, hvalid_r⟩ := hpkg G
    intro a D hok
    rcases hok with ⟨hvalid_a, hdom_a, _, hirrefl_a, _, _⟩
    have ⟨hbase_a, hmax_a⟩ := (hvalid_r a).mp hvalid_a
    have hD_eq :
        (D : Set (Fin n)) =
          { x : Fin n | ∀ i : Fin q, G.Adj (a (Fin.castAdd q (Fin.castAdd (q - 2) i))) x } := by
      ext x
      rw [Finset.mem_coe, hdom_a x, hdom_r a x]
      rfl
    have hD_le_L : D.card ≤ L := by
      rw [← Set.ncard_coe_finset, hD_eq]
      exact hmax_all a hbase_a
    let DStar : Finset (Fin n) :=
      Finset.univ.filter (fun x : Fin n =>
        ∀ i : Fin q, G.Adj (aStar (Fin.castAdd q (Fin.castAdd (q - 2) i))) x)
    have hDStar_card : DStar.card = L := by
      have hset :
          { x : Fin n | ∀ i : Fin q, G.Adj (aStar (Fin.castAdd q (Fin.castAdd (q - 2) i))) x } =
            (DStar : Set (Fin n)) := by
        ext x
        simp [DStar]
      rw [← hcard_star, hset, Set.ncard_coe_finset]
    obtain ⟨e₁, e₂, d, htot, hmono⟩ := hmax_a aStar hbase_star
    have hL_le_D : L ≤ D.card := by
      rw [← hDStar_card]
      refine card_le_of_order_embed DStar D
        (fun x y =>
          (∀ w, (∀ i : Fin q, G.Adj (aStar (Fin.natAdd (q + (q - 2)) i)) w) →
            (∃ u, G.Adj w u ∧ G.Adj y u ∧ ∀ j : Fin (q - 2), G.Adj (aStar (Fin.castAdd q (Fin.natAdd q j))) u) →
            (∃ u, G.Adj w u ∧ G.Adj x u ∧ ∀ j : Fin (q - 2), G.Adj (aStar (Fin.castAdd q (Fin.natAdd q j))) u)) ∧
          (∃ w, (∀ i : Fin q, G.Adj (aStar (Fin.natAdd (q + (q - 2)) i)) w) ∧
            (∃ u, G.Adj w u ∧ G.Adj x u ∧ ∀ j : Fin (q - 2), G.Adj (aStar (Fin.castAdd q (Fin.natAdd q j))) u) ∧
            ¬ (∃ u, G.Adj w u ∧ G.Adj y u ∧ ∀ j : Fin (q - 2), G.Adj (aStar (Fin.castAdd q (Fin.natAdd q j))) u)))
        (fun x y => @Language.Formula.Realize _ _ G.structure _ lt_φ (Fin.snoc (Fin.snoc a x) y))
        (fun x' x => ∃ w, (∃ s : Fin 30, ∀ i : Fin q, G.Adj (d s i) w) ∧
          (∃ u', G.Adj w u' ∧ (∀ j : Fin (q - 1), G.Adj (e₁ j) u') ∧
            ∀ z', (∀ i : Fin q, G.Adj (aStar (Fin.castAdd q (Fin.castAdd (q - 2) i))) z') →
              ((∃ t, G.Adj u' t ∧ G.Adj z' t ∧ ∀ j : Fin (q - 2), G.Adj (aStar (Fin.castAdd q (Fin.natAdd q j))) t) ↔ z' = x')) ∧
          (∃ u, G.Adj w u ∧ (∀ j : Fin (q - 1), G.Adj (e₂ j) u) ∧
            ∀ z, (∀ i : Fin q, G.Adj (a (Fin.castAdd q (Fin.castAdd (q - 2) i))) z) →
              ((∃ t, G.Adj u t ∧ G.Adj z t ∧ ∀ j : Fin (q - 2), G.Adj (a (Fin.castAdd q (Fin.natAdd q j))) t) ↔ z = x)))
        ?_ hirrefl_a ?_ ?_
      · intro x hx y hy
        exact hbase_star.2.2.1 x y (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
      · intro x' hx'
        obtain ⟨x, hx_dom, hrel⟩ := htot x' (Finset.mem_filter.mp hx').2
        exact ⟨x, (hdom_a x).mpr ((hdom_r a x).mpr hx_dom), hrel⟩
      · intro x₁' hx₁' x₂' hx₂' x₁ hx₁ x₂ hx₂ hr1 hr2 hlt'
        rw [hlt_r a x₁ x₂]
        exact hmono x₁' x₂' x₁ x₂
          (Finset.mem_filter.mp hx₁').2 (Finset.mem_filter.mp hx₂').2
          ((hdom_r a x₁).mp ((hdom_a x₁).mp hx₁))
          ((hdom_r a x₂).mp ((hdom_a x₂).mp hx₂))
          hr1 hr2 hlt'
    have hcard_eq : D.card = L := le_antisymm hD_le_L hL_le_D
    rw [hcard_eq]
    dsimp only [L]
    omega

end OMA.R_ShelahSpencerZeroOneLaw_zeroOne_rational_R1_H1_R1
