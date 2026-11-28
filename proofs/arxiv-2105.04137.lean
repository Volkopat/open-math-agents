import OMAStatements.S_arxiv_2105_04137

/-!
Disproof of the dijoin conjecture of Bang-Jensen, da Silva and Havet (arXiv:2105.04137).

Counterexample of Alon, Powierski, Savery, Scott and Wilmer (Invertibility of digraphs and
tournaments, arXiv:2212.11969, Theorem 1.3 and its proof): `L` is the directed triangle and `R`
is the tournament on nine vertices `0, …, 8` (the paper's `1, …, 9`) obtained from the transitive
order by reversing the arcs between two different classes among `A = {0, 2}`, `B = {3, 5}`,
`C = {6, 8}`. Then `inv(L → R) ≤ 3` (invert `A ∪ B`, `A ∪ C`, `B ∪ C`, each with two vertices of
the triangle), `inv(L) ≥ 1` and `inv(R) ≥ 3`, so `inv(L → R) < inv(L) + inv(R)`.

The bound `inv(R) ≥ 3` is a finite check: after inverting at most two sets, the arc between two
vertices only depends on which of the sets contain them (a colour in `Bool × Bool`), and a
pruned search over the colourings, run by the kernel, finds a directed triangle in each case.
-/

open OMA.S_arxiv_2105_04137

namespace OMADisproofAux

/-- A digraph given by a Boolean adjacency function. -/
def ofBool {V : Type} (b : V → V → Bool) : Digraph V where
  Adj u v := b u v = true

/-- Boolean form of an inversion: reverse the arcs between two vertices where `x` holds. -/
def invB {V : Type} (b : V → V → Bool) (x : V → Bool) : V → V → Bool :=
  fun u v => if x u && x v then b v u else b u v

theorem invert_ofBool {V : Type} (b : V → V → Bool) (X : Set V) [DecidablePred (· ∈ X)] :
    invert (ofBool b) X = ofBool (invB b (fun v => decide (v ∈ X))) := by
  ext u v
  simp only [invert, ofBool, invB]
  by_cases hu : u ∈ X <;> by_cases hv : v ∈ X <;> simp [hu, hv]

theorem invert_ofBool_setOf {V : Type} (b : V → V → Bool) (x : V → Bool) :
    invert (ofBool b) {v | x v = true} = ofBool (invB b x) := by
  ext u v
  simp only [invert, ofBool, invB, Set.mem_setOf_eq]
  cases x u <;> cases x v <;> simp

theorem acyclic_of_rank {V : Type} (D : Digraph V) (f : V → ℕ)
    (h : ∀ u v, D.Adj u v → f u < f v) : IsAcyclic D := by
  intro v hv
  have key : ∀ a b, Relation.TransGen D.Adj a b → f a < f b := by
    intro a b hab
    induction hab with
    | single h1 => exact h _ _ h1
    | tail _ h2 ih => exact lt_trans ih (h _ _ h2)
  exact lt_irrefl _ (key v v hv)

theorem not_acyclic_of_triangle {V : Type} (D : Digraph V) (a b c : V) (h1 : D.Adj a b)
    (h2 : D.Adj b c) (h3 : D.Adj c a) : ¬ IsAcyclic D := fun hD =>
  hD a (Relation.TransGen.tail (Relation.TransGen.tail (Relation.TransGen.single h1) h2) h3)

/-! The two oriented graphs. -/

/-- The directed triangle `0 → 1 → 2 → 0`. -/
def lB (i j : Fin 3) : Bool := decide (j = i + 1)

def L : Digraph (Fin 3) := ofBool lB

/-- The classes `A = {0, 2}`, `B = {3, 5}`, `C = {6, 8}` (labelled 1, 2, 3); 0 for no class. -/
def cls (i : Fin 9) : ℕ :=
  match i.val with
  | 0 => 1 | 2 => 1 | 3 => 2 | 5 => 2 | 6 => 3 | 8 => 3 | _ => 0

/-- The arc `i → j` of `R`: the order arc `i < j`, reversed when `i` and `j` lie in two
different classes. -/
def rB (i j : Fin 9) : Bool :=
  decide (i ≠ j) && (decide (i < j) != (decide (cls i ≠ 0) && decide (cls j ≠ 0) &&
    decide (cls i ≠ cls j)))

def R : Digraph (Fin 9) := ofBool rB

theorem L_oriented : IsOriented L := by
  refine ⟨?_, ?_⟩ <;> simp only [L, ofBool] <;> decide

theorem R_oriented : IsOriented R := by
  refine ⟨?_, ?_⟩ <;> simp only [R, ofBool] <;> decide

/-! `inv(L) ≥ 1`. -/

theorem L_not_acyclic : ¬ IsAcyclic L :=
  not_acyclic_of_triangle L 0 1 2 (show lB 0 1 = true by decide) (show lB 1 2 = true by decide)
    (show lB 2 0 = true by decide)

theorem L_mem : ∃ X : Fin 1 → Set (Fin 3), IsAcyclic ((List.ofFn X).foldl invert L) := by
  refine ⟨fun _ => {v | decide (v.val ≤ 1) = true}, ?_⟩
  simp only [List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil, L,
    invert_ofBool_setOf]
  refine acyclic_of_rank _ (fun v => [2, 0, 1].getD v.val 0) ?_
  simp only [ofBool]
  decide

theorem one_le_inv_L : 1 ≤ inv L := by
  refine le_csInf ⟨1, L_mem⟩ ?_
  rintro k ⟨X, hX⟩
  by_contra hk
  have h0 : k = 0 := by omega
  subst h0
  exact L_not_acyclic (by simpa using hX)

/-! `inv(R) ≥ 3`: a kernel-checked search over the colourings of the vertices. -/

/-- Adjacency in `R` after inverting `{v | (col v).1}` and then `{v | (col v).2}`. -/
def adjC (col : Fin 9 → Bool × Bool) : Fin 9 → Fin 9 → Bool :=
  invB (invB rB (fun v => (col v).1)) (fun v => (col v).2)

theorem adjC_congr (col col' : Fin 9 → Bool × Bool) (u v : Fin 9) (hu : col' u = col u)
    (hv : col' v = col v) : adjC col' u v = adjC col u v := by
  simp only [adjC, invB, hu, hv]

/-- A directed triangle `k → a → b → k` under `col` whose vertices `a`, `b` are not in `ks`. -/
def tri (col : Fin 9 → Bool × Bool) (k : Fin 9) (ks : List (Fin 9)) : Bool :=
  (List.finRange 9).any fun a => decide (a ∉ ks) && adjC col k a &&
    (List.finRange 9).any fun b => decide (b ∉ ks) && adjC col a b && adjC col b k

/-- Colour the vertices of `ks` in turn (all four colours each); every branch must close with a
directed triangle among the vertices coloured so far. -/
def search (col : Fin 9 → Bool × Bool) : List (Fin 9) → Bool
  | [] => false
  | k :: ks => [(false, false), (false, true), (true, false), (true, true)].all fun c =>
      tri (Function.update col k c) k ks || search (Function.update col k c) ks

theorem search_sound (ks : List (Fin 9)) : ∀ col : Fin 9 → Bool × Bool, search col ks = true →
    ∀ col' : Fin 9 → Bool × Bool, (∀ i, i ∉ ks → col' i = col i) →
      ∃ a b c, adjC col' a b = true ∧ adjC col' b c = true ∧ adjC col' c a = true := by
  induction ks with
  | nil => intro col h; simp [search] at h
  | cons k ks ih =>
    intro col h col' hcol
    simp only [search, List.all_eq_true] at h
    have hc := h (col' k) (by rcases col' k with ⟨_ | _, _ | _⟩ <;> simp)
    have hag : ∀ i, i ∉ ks → col' i = Function.update col k (col' k) i := by
      intro i hi
      by_cases hik : i = k
      · subst hik; simp
      · rw [Function.update_of_ne hik]
        exact hcol i (by simp [hik, hi])
    rcases Bool.or_eq_true_iff.mp hc with ht | hr
    · simp only [tri, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ht
      obtain ⟨a, -, ⟨⟨ha, hka⟩, b, -, ⟨hb, hab⟩, hbk⟩⟩ := ht
      have ek : col' k = Function.update col k (col' k) k := by simp
      refine ⟨k, a, b, ?_, ?_, ?_⟩
      · rw [adjC_congr _ _ k a ek (hag a ha)]; exact hka
      · rw [adjC_congr _ _ a b (hag a ha) (hag b hb)]; exact hab
      · rw [adjC_congr _ _ b k (hag b hb) ek]; exact hbk
    · exact ih _ hr col' hag

theorem search_ok : search (fun _ => (false, false)) (List.finRange 9) = true := by
  decide

theorem triangle_all (col : Fin 9 → Bool × Bool) :
    ∃ a b c, adjC col a b = true ∧ adjC col b c = true ∧ adjC col c a = true :=
  search_sound _ _ search_ok col (fun i hi => absurd (List.mem_finRange i) hi)

theorem not_acyclic_adjC (col : Fin 9 → Bool × Bool) : ¬ IsAcyclic (ofBool (adjC col)) := by
  obtain ⟨a, b, c, h1, h2, h3⟩ := triangle_all col
  exact not_acyclic_of_triangle _ a b c h1 h2 h3

theorem R_lt_three (k : ℕ) (hk : k < 3) (X : Fin k → Set (Fin 9)) :
    ¬ IsAcyclic ((List.ofFn X).foldl invert R) := by
  classical
  interval_cases k
  · have e : R = ofBool (adjC (fun _ => (false, false))) := by
      simp only [R]; congr 1
    simpa [e] using not_acyclic_adjC (fun _ => (false, false))
  · have e : (List.ofFn X).foldl invert R =
        ofBool (adjC (fun v => (decide (v ∈ X 0), false))) := by
      simp only [List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil, R,
        invert_ofBool]
      congr 1
    rw [e]; exact not_acyclic_adjC _
  · have e : (List.ofFn X).foldl invert R =
        ofBool (adjC (fun v => (decide (v ∈ X 0), decide (v ∈ X 1)))) := by
      simp only [List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil, R,
        invert_ofBool]
      rfl
    rw [e]; exact not_acyclic_adjC _

theorem R_mem : ∃ X : Fin 3 → Set (Fin 9), IsAcyclic ((List.ofFn X).foldl invert R) := by
  refine ⟨![{v | decide (cls v = 1 ∨ cls v = 2) = true}, {v | decide (cls v = 1 ∨ cls v = 3) = true},
    {v | decide (cls v = 2 ∨ cls v = 3) = true}], ?_⟩
  simp only [List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil, R,
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    invert_ofBool_setOf]
  refine acyclic_of_rank _ (fun v => v.val) ?_
  simp only [ofBool]
  decide

theorem three_le_inv_R : 3 ≤ inv R := by
  refine le_csInf ⟨3, R_mem⟩ ?_
  rintro k ⟨X, hX⟩
  by_contra hk
  exact R_lt_three k (by omega) X hX

/-! `inv(L → R) ≤ 3`. -/

/-- Boolean adjacency of the dijoin `L → R`. -/
def dB : Fin 3 ⊕ Fin 9 → Fin 3 ⊕ Fin 9 → Bool
  | .inl a, .inl b => lB a b
  | .inr a, .inr b => rB a b
  | .inl _, .inr _ => true
  | .inr _, .inl _ => false

theorem dijoin_eq : dijoin L R = ofBool dB := by
  ext x y
  cases x <;> cases y <;> simp [dijoin, ofBool, dB, L, R]

/-- The decycling family of the proof of Theorem 1.3 of arXiv:2212.11969: `A ∪ B`, `A ∪ C`,
`B ∪ C`, each together with the vertices `0` and `1` of the triangle. -/
def xd (s t : ℕ) : Fin 3 ⊕ Fin 9 → Bool
  | .inl a => decide (a.val ≤ 1)
  | .inr v => decide (cls v = s ∨ cls v = t)

/-- A rank strictly increasing along every arc after the three inversions. -/
def rd : Fin 3 ⊕ Fin 9 → ℕ
  | .inl a => [2, 0, 1].getD a.val 0
  | .inr v => v.val + 3

theorem dijoin_mem :
    ∃ X : Fin 3 → Set (Fin 3 ⊕ Fin 9), IsAcyclic ((List.ofFn X).foldl invert (dijoin L R)) := by
  refine ⟨![{v | xd 1 2 v = true}, {v | xd 1 3 v = true}, {v | xd 2 3 v = true}], ?_⟩
  simp only [List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil, dijoin_eq,
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    invert_ofBool_setOf]
  refine acyclic_of_rank _ rd ?_
  simp only [ofBool]
  decide

theorem inv_dijoin_le : inv (dijoin L R) ≤ 3 :=
  Nat.sInf_le dijoin_mem

end OMADisproofAux

open OMADisproofAux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2105_04137.main) := by
  intro h
  have e := h (Fin 3) (Fin 9) L R L_oriented R_oriented
  have h1 := one_le_inv_L
  have h2 := three_le_inv_R
  have h3 := inv_dijoin_le
  omega
