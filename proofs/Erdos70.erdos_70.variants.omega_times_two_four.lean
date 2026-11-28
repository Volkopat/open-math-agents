import FormalConjectures.ErdosProblems.«70»

/-!
# An increasing red ω·2 or four blue points in a triple coloring of the reals

G1 supplied the two-case argument and the countably supported ultrafilter argument for
pairs. This formalization uses g5's interleaved selection on two finite lists. For pairs
it uses countably many tests at once, sampling their finite profiles over rational intervals.
The final selection theorem also gives the five tests in the round-2 reduction.
-/

namespace OMA.Erdos70Rows

open Set Ordinal Cardinal Filter
open scoped Topology

/-- Binary finite-color partition on an uncountable set of reals, allowing a prescribed
countable set of exceptions above each point. Colors only need to cover the other pairs. -/
def BinaryWithExceptions : Prop := ∀ (ι : Type) [Finite ι] (s : Set ℝ) (bad : ℝ → Set ℝ)
  (g : ι → ℝ → ℝ → Prop), ¬s.Countable → (∀ x ∈ s, (bad x).Countable) →
  (∀ x ∈ s, ∀ y ∈ s, x < y → y ∉ bad x → ∃ c, g c x y) →
  ∃ c : ι, ∃ a b : ℕ ↪o ℝ, (∀ i j, a i < b j) ∧
    range a ∪ range b ⊆ s ∧ ∀ x ∈ range a ∪ range b, ∀ y ∈ range a ∪ range b,
      x < y → g c x y

/-- An iterated ultrafilter limit of a ternary predicate can be realized on a single subsequence. -/
private theorem diagonalTriple {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ atTop)
    (p : ℕ → ℕ → ℕ → Prop) (h : ∀ᶠ i in U, ∀ᶠ j in U, ∀ᶠ k in U, p i j k) :
    ∃ f : ℕ ↪o ℕ, ∀ i j k, i < j → j < k → p (f i) (f j) (f k) := by
  let B i j := ∀ᶠ k in U, p i j k
  let A i := ∀ᶠ j in U, B i j
  let rel (x y : ℕ) := x < y ∧ B x y ∧ ∀ i : Fin (x + 1), B i x → p i x y
  have extend (s : Finset ℕ) (hs : ∀ x ∈ s, A x) :
      ∃ y, A y ∧ ∀ x ∈ s, rel x y := by
    have next (x : ℕ) (hx : x ∈ s) : ∀ᶠ y in U, rel x y := by
      have hlast : ∀ᶠ y in U, ∀ i : Fin (x + 1), B i x → p i x y := by
        apply eventually_all.mpr
        intro i
        by_cases hb : B i x
        · exact hb.mono fun _ hy _ => hy
        · exact Eventually.of_forall fun _ hy => (hb hy).elim
      have hlt : ∀ᶠ y in U, x < y := hU (eventually_gt_atTop x)
      have hB : ∀ᶠ y in U, B x y := hs x hx
      exact hlt.and (hB.and hlast)
    exact (h.and (s.finite_toSet.eventually_all.mpr next)).exists
  obtain ⟨f, _, hf⟩ := exists_seq_of_forall_finset_exists A rel extend
  have hmono : StrictMono f := fun i j hij => (hf i j hij).1
  exact ⟨OrderEmbedding.ofStrictMono f hmono, fun i j k hij hjk =>
    (hf j k hjk).2.2 ⟨f i, Nat.lt_succ_of_lt (hmono hij)⟩ (hf i j hij).2.1⟩

/-- Infinite Ramsey for increasing triples of natural numbers and two colors. -/
theorem ramseyTriples (p : ℕ → ℕ → ℕ → Prop) :
    (∃ f : ℕ ↪o ℕ, ∀ i j k, i < j → j < k → p (f i) (f j) (f k)) ∨
    (∃ f : ℕ ↪o ℕ, ∀ i j k, i < j → j < k → ¬ p (f i) (f j) (f k)) := by
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le (atTop : Filter ℕ)
  by_cases h : ∀ᶠ i in U, ∀ᶠ j in U, ∀ᶠ k in U, p i j k
  · exact Or.inl (diagonalTriple hU p h)
  · apply Or.inr
    apply diagonalTriple hU (fun i j k => ¬ p i j k)
    simpa only [Ultrafilter.eventually_not] using h

/-- Sorting the arguments of a symmetric triple coloring preserves its truth value. -/
private theorem sortedTriplewise {α : Type*} [LinearOrder α] (p : α → α → α → Prop)
    (hs : ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (p x y z ↔ p y x z) ∧ (p x y z ↔ p x z y))
    (h : ∀ x y z, x < y → y < z → p x y z) : Triplewise p := by
  intro x y z hxy hyz hxz
  rcases lt_or_gt_of_ne hxy with h₁ | h₁ <;> rcases lt_or_gt_of_ne hyz with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hxz with h₃ | h₃ <;>
    grind

/-- In the absence of a blue four-set, any increasing sequence has a red infinite subsequence. -/
theorem redSubsequence (r : ℝ → ℝ → ℝ → Prop)
    (hs : ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y))
    (hb : ¬ ∃ s : Set ℝ, #s = 4 ∧ s.Triplewise (fun x y z => ¬ r x y z))
    (a : ℕ ↪o ℝ) : ∃ g : ℕ ↪o ℕ, (Set.range (g.trans a)).Triplewise r := by
  rcases ramseyTriples (fun i j k => r (a i) (a j) (a k)) with ⟨f, hf⟩ | ⟨f, hf⟩
  · let v := f.trans a
    have hall : Triplewise (fun i j k => r (v i) (v j) (v k)) :=
      sortedTriplewise _ (fun x y z h₁ h₂ h₃ => hs _ _ _ (v.injective.ne h₁)
        (v.injective.ne h₂) (v.injective.ne h₃)) hf
    refine ⟨f, ?_⟩
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ hij hjk hik
    exact hall (ne_of_apply_ne _ hij) (ne_of_apply_ne _ hjk) (ne_of_apply_ne _ hik)
  · exfalso
    let v : Fin 4 → ℝ := fun i => a (f i.val)
    have hinj : Function.Injective v := a.injective.comp (f.injective.comp Fin.val_injective)
    have hcard : #(Set.range v) = 4 :=
      (Cardinal.mk_congr (Equiv.ofInjective v hinj)).symm.trans (Cardinal.mk_fin 4)
    have hall : Triplewise (fun i j k => ¬ r (v i) (v j) (v k)) := by
      apply sortedTriplewise
      · intro i j k hij hjk hik
        have h := hs _ _ _ (hinj.ne hij) (hinj.ne hjk) (hinj.ne hik)
        exact ⟨not_congr h.1, not_congr h.2⟩
      · exact fun i j k hij hjk => hf i.val j.val k.val hij hjk
    apply hb ⟨Set.range v, hcard, ?_⟩
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ hij hjk hik
    exact hall (ne_of_apply_ne _ hij) (ne_of_apply_ne _ hjk) (ne_of_apply_ne _ hik)

local instance : IsWellOrder (ℕ ⊕ₗ ℕ) (· < ·) :=
  inferInstanceAs (IsWellOrder (ℕ ⊕ ℕ) (Sum.Lex (· < · : ℕ → ℕ → Prop) (· < · : ℕ → ℕ → Prop)))

private theorem blockType : typeLT (ℕ ⊕ₗ ℕ) = ω * 2 := by
  change Ordinal.type (Sum.Lex (· < · : ℕ → ℕ → Prop) (· < · : ℕ → ℕ → Prop)) = ω * 2
  rw [Ordinal.type_sum_lex, Ordinal.type_nat_lt, Ordinal.mul_two]

/-- Under the no-blue-four hypothesis the mixed conditions alone suffice for a red copy of ω·2. -/
theorem redOfMixed (r : ℝ → ℝ → ℝ → Prop)
    (hs : ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y))
    (hb : ¬ ∃ s : Set ℝ, #s = 4 ∧ s.Triplewise (fun x y z => ¬ r x y z))
    (hm : ∃ a b : ℕ ↪o ℝ, (∀ i j, a i < b j) ∧
      (∀ i j k, i < j → r (a i) (a j) (b k)) ∧
      (∀ i j k, j < k → r (a i) (b j) (b k))) :
    ∃ e : (Ordinal.omega0.{0} * 2).ToType ↪o ℝ, (Set.range e).Triplewise r := by
  obtain ⟨a, b, hsep, h₁, h₂⟩ := hm
  obtain ⟨f, hf⟩ := redSubsequence r hs hb a
  obtain ⟨g, hg⟩ := redSubsequence r hs hb b
  let u : ℕ ↪o ℝ := f.trans a
  let w : ℕ ↪o ℝ := g.trans b
  let v : ℕ ⊕ₗ ℕ → ℝ := Sum.elim u w
  have hv : StrictMono v := by
    rintro (i | i) (j | j) h
    · exact u.strictMono (Sum.Lex.inl_lt_inl_iff.mp h)
    · exact hsep _ _
    · exact (Sum.Lex.not_inr_lt_inl h).elim
    · exact w.strictMono (Sum.Lex.inr_lt_inr_iff.mp h)
  have hall : Triplewise (fun i j k => r (v i) (v j) (v k)) := by
    apply sortedTriplewise
    · intro i j k hij hjk hik
      exact hs _ _ _ (hv.injective.ne hij) (hv.injective.ne hjk) (hv.injective.ne hik)
    · rintro (i | i) (j | j) (k | k) hij hjk
      · have h := u.strictMono (Sum.Lex.inl_lt_inl_iff.mp hij)
        have h' := u.strictMono (Sum.Lex.inl_lt_inl_iff.mp hjk)
        exact hf ⟨i, rfl⟩ ⟨j, rfl⟩ ⟨k, rfl⟩ h.ne h'.ne (h.trans h').ne
      · exact h₁ _ _ _ (f.strictMono (Sum.Lex.inl_lt_inl_iff.mp hij))
      · exact (Sum.Lex.not_inr_lt_inl hjk).elim
      · exact h₂ _ _ _ (g.strictMono (Sum.Lex.inr_lt_inr_iff.mp hjk))
      · exact (Sum.Lex.not_inr_lt_inl hij).elim
      · exact (Sum.Lex.not_inr_lt_inl hij).elim
      · exact (Sum.Lex.not_inr_lt_inl hjk).elim
      · have h := w.strictMono (Sum.Lex.inr_lt_inr_iff.mp hij)
        have h' := w.strictMono (Sum.Lex.inr_lt_inr_iff.mp hjk)
        exact hg ⟨i, rfl⟩ ⟨j, rfl⟩ ⟨k, rfl⟩ h.ne h'.ne (h.trans h').ne
  obtain ⟨idx⟩ := Ordinal.type_le_iff'.mp
    ((Ordinal.type_toType (ω * 2)).trans blockType.symm).le
  let e : (Ordinal.omega0.{0} * 2).ToType ↪o ℝ := idx.orderEmbeddingOfLTEmbedding.trans (OrderEmbedding.ofStrictMono v hv)
  refine ⟨e, ?_⟩
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ hij hjk hik
  exact hall (ne_of_apply_ne v hij) (ne_of_apply_ne v hjk) (ne_of_apply_ne v hik)


/-- If each member of an uncountable set accepts a filter-large set of indices, a single
admissible index is accepted by uncountably many members. Only countably many indices occur. -/
private theorem uncountableColumn {s : Set ℝ} (hs : ¬s.Countable) (U : Ultrafilter ℕ)
    {allow : ℕ → Prop} (hallow : ∀ᶠ n in U, allow n)
    (p : ℝ → ℕ → Prop) (hp : ∀ x ∈ s, ∀ᶠ n in U, p x n) :
    ∃ n, allow n ∧ ¬ {x ∈ s | p x n}.Countable := by
  classical
  by_contra! h
  have small (n : ℕ) : {x ∈ s | allow n ∧ p x n}.Countable := by
    by_cases hn : allow n
    · simpa only [hn, true_and] using h n hn
    · simp [hn]
  apply hs
  apply (countable_iUnion small).mono
  intro x hx
  obtain ⟨n, hn, hxn⟩ := (hallow.and (hp x hx)).exists
  apply mem_iUnion.mpr
  exact ⟨n, show x ∈ {z ∈ s | allow n ∧ p z n} from ⟨hx,hn,hxn⟩⟩

/-- Interleave the two rows. At a finite stage the uncountable reservoir records eligible
lower points. A single new upper index preserves uncountably many of them. -/
theorem fuseRows (p : ℝ → ℝ → ℕ → Prop) (q : ℝ → ℕ → ℕ → Prop)
    (U : Ultrafilter ℕ) (hu : (U : Filter ℕ) ≤ atTop) (s : Set ℝ) (hunc : ¬s.Countable)
    (initial : ∀ x ∈ s, ∀ᶠ m in U, ∀ᶠ n in U, q x m n)
    (rich : ∀ (F : Finset ℕ) (t : Set ℝ), t ⊆ s → ¬t.Countable →
      ∃ x ∈ t, ¬ {y ∈ t | x < y ∧ (∀ n ∈ F, p x y n) ∧ ∀ᶠ n in U, p x y n}.Countable) :
    ∃ a : ℕ ↪o ℝ, ∃ e : ℕ ↪o ℕ, (∀ i, a i ∈ s) ∧
      (∀ i j k, i < j → p (a i) (a j) (e k)) ∧
      (∀ i j k, j < k → q (a i) (e j) (e k)) := by
  classical
  let pair (F : Finset ℕ) (x y : ℝ) := (∀ n ∈ F, p x y n) ∧ ∀ᶠ n in U, p x y n
  let point (F : Finset ℕ) (x : ℝ) :=
    (∀ m ∈ F, ∀ n ∈ F, m < n → q x m n) ∧ (∀ m ∈ F, ∀ᶠ n in U, q x m n) ∧
      ∀ᶠ m in U, ∀ᶠ n in U, q x m n
  let valid (D : Finset ℝ) (F : Finset ℕ) := (∀ x ∈ D, x ∈ s ∧ point F x) ∧
    (∀ x ∈ D, ∀ y ∈ D, x < y → pair F x y) ∧
    ∃ t ⊆ s, ¬t.Countable ∧ ∀ y ∈ t, point F y ∧ ∀ x ∈ D, x < y ∧ pair F x y
  have base : valid ∅ ∅ := by
    refine ⟨by simp, by simp, s, Subset.rfl, hunc, ?_⟩
    intro y hy
    simp [point,initial y hy]
  have addLeft (D F) (h : valid D F) :
      ∃ x, (∀ z ∈ D, z < x) ∧ valid (insert x D) F := by
    obtain ⟨hd, hp, t, hts, ht, eligible⟩ := h
    obtain ⟨x, hx, hnext⟩ := rich F t hts ht
    obtain ⟨px, prev⟩ := eligible x hx
    refine ⟨x, fun z hz => (prev z hz).1, ?_, ?_, _, fun _ hy => hts hy.1, hnext, ?_⟩
    · simpa using And.intro (And.intro (hts hx) px) hd
    · intro v hv w hw hvw
      rcases Finset.mem_insert.mp hv with rfl | hvD
      · rcases Finset.mem_insert.mp hw with rfl | hw
        · exact (lt_irrefl _ hvw).elim
        · exact (hvw.asymm (prev w hw).1).elim
      · rcases Finset.mem_insert.mp hw with rfl | hw
        · exact (prev v hvD).2
        · exact hp v hvD w hw hvw
    · intro y hy
      obtain ⟨py, old⟩ := eligible y hy.1
      exact ⟨py, by simpa using And.intro (And.intro hy.2.1 hy.2.2) old⟩
  let fresh (F : Finset ℕ) (x : ℝ) (n : ℕ) :=
    (∀ m ∈ F, q x m n) ∧ ∀ᶠ k in U, q x n k
  have can (F : Finset ℕ) (x : ℝ) (h : point F x) : ∀ᶠ n in U, fresh F x n :=
    (F.finite_toSet.eventually_all.mpr h.2.1).and h.2.2
  have liftPoint (F : Finset ℕ) (x : ℝ) (n : ℕ) (gt : ∀ m ∈ F, m < n)
      (old : point F x) (hn : fresh F x n) : point (insert n F) x := by
    refine ⟨?_, by simpa using And.intro hn.2 old.2.1, old.2.2⟩
    intro i hi j hj hij
    rcases Finset.mem_insert.mp hi with rfl | hiF
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (lt_irrefl _ hij).elim
      · exact (hij.asymm (gt j hj)).elim
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hn.1 i hiF
      · exact old.1 i hiF j hj hij
  have addRight (D F) (h : valid D F) :
      ∃ n, (∀ m ∈ F, m < n) ∧ valid D (insert n F) := by
    obtain ⟨hd, hp, t, hts, ht, eligible⟩ := h
    have hgt : ∀ᶠ n in U, ∀ m ∈ F, m < n := F.finite_toSet.eventually_all.mpr
      (fun m _ => hu (eventually_gt_atTop m))
    have hold : ∀ᶠ n in U, ∀ x ∈ D, fresh F x n :=
      D.finite_toSet.eventually_all.mpr fun x hx => can F x (hd x hx).2
    have hpair : ∀ᶠ n in U, ∀ x ∈ D, ∀ y ∈ D, x < y → p x y n := by
      refine D.finite_toSet.eventually_all.mpr fun x hx => D.finite_toSet.eventually_all.mpr fun y hy => ?_
      by_cases hxy : x < y
      · exact (hp x hx y hy hxy).2.mono fun _ hn _ => hn
      · exact Eventually.of_forall fun _ hf => (hxy hf).elim
    let accept y n := fresh F y n ∧ ∀ x ∈ D, p x y n
    have hacc (y : ℝ) (hy : y ∈ t) : ∀ᶠ n in U, accept y n := by
      obtain ⟨py, prev⟩ := eligible y hy
      exact (can F y py).and (D.finite_toSet.eventually_all.mpr fun x hx => (prev x hx).2.2)
    obtain ⟨n, ⟨gt, old, pairs⟩, hn⟩ := uncountableColumn ht U (hgt.and (hold.and hpair)) accept hacc
    refine ⟨n, gt, fun x hx => ⟨(hd x hx).1, liftPoint F x n gt (hd x hx).2 (old x hx)⟩, ?_,
      {y ∈ t | accept y n}, fun _ hy => hts hy.1, hn, ?_⟩
    · intro x hx y hy hxy
      have prev := hp x hx y hy hxy
      exact ⟨by simpa using And.intro (pairs x hx y hy hxy) prev.1, prev.2⟩
    · intro y hy
      obtain ⟨py, prev⟩ := eligible y hy.1
      refine ⟨liftPoint F y n gt py hy.2.1, fun x hx => ⟨(prev x hx).1, ?_, (prev x hx).2.2⟩⟩
      simpa using And.intro (hy.2.2 x hx) (prev x hx).2.1
  let State := {v : Finset ℝ × Finset ℕ // valid v.1 v.2}
  have step (v : State) : ∃ x n, (∀ z ∈ v.val.1, z < x) ∧ (∀ m ∈ v.val.2, m < n) ∧
      valid (insert x v.val.1) (insert n v.val.2) := by
    obtain ⟨x, hx, next⟩ := addLeft _ _ v.property
    obtain ⟨n, hn, done⟩ := addRight _ _ next
    exact ⟨x,n,hx,hn,done⟩
  choose x n laterX laterN good using step
  let next (v : State) : State := ⟨(insert (x v) v.val.1, insert (n v) v.val.2), good v⟩
  let v (i : ℕ) := next^[i] (⟨(∅,∅), base⟩ : State)
  have succ (i : ℕ) : v (i+1) = next (v i) := Function.iterate_succ_apply' next i _
  have dx (i : ℕ) : (v (i+1)).val.1 = insert (x (v i)) (v i).val.1 := by rw [succ]
  have dn (i : ℕ) : (v (i+1)).val.2 = insert (n (v i)) (v i).val.2 := by rw [succ]
  have mx : Monotone (fun i => (v i).val.1) := monotone_nat_of_le_succ fun i => by
    rw [dx]; exact Finset.subset_insert _ _
  have mn : Monotone (fun i => (v i).val.2) := monotone_nat_of_le_succ fun i => by
    rw [dn]; exact Finset.subset_insert _ _
  have xmem (i j : ℕ) (hij : i < j) : x (v i) ∈ (v j).val.1 := mx (show i+1 ≤ j from hij)
    (by change x (v i) ∈ (v (i+1)).val.1; rw [dx]; exact Finset.mem_insert_self ..)
  have nmem (i j : ℕ) (hij : i < j) : n (v i) ∈ (v j).val.2 := mn (show i+1 ≤ j from hij)
    (by change n (v i) ∈ (v (i+1)).val.2; rw [dn]; exact Finset.mem_insert_self ..)
  have xmono : StrictMono fun i => x (v i) := fun i j hij => laterX _ _ (xmem i j hij)
  have nmono : StrictMono fun i => n (v i) := fun i j hij => laterN _ _ (nmem i j hij)
  refine ⟨OrderEmbedding.ofStrictMono _ xmono, OrderEmbedding.ofStrictMono _ nmono,
    fun i => ((v (i+1)).property.1 _ (xmem i _ (by omega))).1, ?_, ?_⟩
  · intro i j k hij
    let l := i+j+k+1
    exact ((v l).property.2.1 _ (xmem i l (by dsimp [l]; omega)) _ (xmem j l (by dsimp [l]; omega))
      (xmono hij)).1 _ (nmem k l (by dsimp [l]; omega))
  · intro i j k hjk
    let l := i+j+k+1
    exact ((v l).property.1 _ (xmem i l (by dsimp [l]; omega))).2.1
      _ (nmem j l (by dsimp [l]; omega)) _ (nmem k l (by dsimp [l]; omega)) (nmono hjk)

/-- An uncountable set of reals contains an increasing sequence converging to one of its own points. -/
theorem increasingLimit {s : Set ℝ} (hs : ¬ s.Countable) :
    ∃ x ∈ s, ∃ f : ℕ → ℝ, StrictMono f ∧ Tendsto f atTop (𝓝 x) ∧
      ∀ n, f n ∈ s ∩ Iio x := by
  obtain ⟨x, hx, h⟩ : ∃ x ∈ s, 𝓝[s ∩ Iio x] x ≠ ⊥ := by
    by_contra! hall
    apply hs
    apply (countable_setOfPred_isolated_left_within (s := s)).mono
    intro y hy
    exact ⟨hy, hall y hy⟩
  have hcl : x ∈ closure (s ∩ Iio x) := mem_closure_iff_nhdsWithin_neBot.mpr ⟨h⟩
  have hne : (s ∩ Iio x).Nonempty := closure_nonempty_iff.mp ⟨x, hcl⟩
  have hlub : IsLUB (s ∩ Iio x) x :=
    isLUB_of_mem_closure (fun _ hy => hy.2.le) hcl
  obtain ⟨f, hf, _, hlim, hmem⟩ := hlub.exists_seq_strictMono_tendsto_of_notMem (by simp) hne
  exact ⟨x, hx, f, hf, hlim, hmem⟩

/-- A rational cut splits every uncountable real set into two uncountable pieces. -/
private theorem splitUncountable (s : Set ℝ) (hs : ¬s.Countable) :
    ∃ q : ℚ, ¬(s ∩ Iio (q : ℝ)).Countable ∧ ¬(s ∩ Ioi (q : ℝ)).Countable := by
  classical
  let bad (q : ℚ) : Set ℝ := (if (s ∩ Iio (q : ℝ)).Countable then s ∩ Iio (q : ℝ) else ∅) ∪
    (if (s ∩ Ioi (q : ℝ)).Countable then s ∩ Ioi (q : ℝ) else ∅)
  have hbad : (⋃ q, bad q).Countable := by
    apply countable_iUnion
    intro q
    unfold bad
    split <;> split <;> simp_all
  have hrem : ¬(s \ ⋃ q, bad q).Countable := fun h => hs (h.of_sdiff hbad)
  obtain ⟨_, _, f, hf, _, hm⟩ := increasingLimit hrem
  obtain ⟨q, h₀, h₁⟩ := exists_rat_btwn (hf (Nat.zero_lt_one))
  have hmem (i : ℕ) := (hm i).1
  refine ⟨q, fun h => (hmem 0).2 (mem_iUnion.mpr ⟨q, Or.inl ?_⟩),
    fun h => (hmem 1).2 (mem_iUnion.mpr ⟨q, Or.inr ?_⟩)⟩
  · rw [if_pos h]; exact ⟨(hmem 0).1, h₀⟩
  · rw [if_pos h]; exact ⟨(hmem 1).1, h₁⟩

/-- Four distinct points whose four unordered triples are blue give the blue alternative. -/
private theorem blueFour (r : ℝ → ℝ → ℝ → Prop)
    (hs : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y))
    {v : Fin 4 → ℝ} (hv : Function.Injective v)
    (h : ∀ i j k, i < j → j < k → ¬ r (v i) (v j) (v k)) :
    ∃ s : Set ℝ, #s = 4 ∧ s.Triplewise (fun x y z => ¬ r x y z) := by
  refine ⟨Set.range v, (Cardinal.mk_congr (Equiv.ofInjective v hv)).symm.trans (Cardinal.mk_fin 4), ?_⟩
  have hall : Triplewise (fun i j k => ¬r (v i) (v j) (v k)) := by
    apply sortedTriplewise _ _ h
    intro i j k hij hjk hik
    have h' := hs _ _ _ (hv.ne hij) (hv.ne hjk) (hv.ne hik)
    exact ⟨not_congr h'.1, not_congr h'.2⟩
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ hij hjk hik
  exact hall (ne_of_apply_ne _ hij) (ne_of_apply_ne _ hjk) (ne_of_apply_ne _ hik)

/-- Three blue faces of a tetrahedron force its fourth face to be red. -/
private theorem fourthRed (r : ℝ → ℝ → ℝ → Prop)
    (hs : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y))
    (hb : ¬ ∃ s : Set ℝ, #s = 4 ∧ s.Triplewise (fun x y z => ¬ r x y z))
    {w x y z : ℝ} (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hwxy : ¬r w x y) (hwxz : ¬r w x z) (hwyz : ¬r w y z) : r x y z := by
  by_contra hxyz
  let v : Fin 4 → ℝ := ![w, x, y, z]
  apply hb (blueFour r hs (v := v) ?_ ?_)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [v] at hij ⊢ <;> grind
  · intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> try (exfalso; exact (of_decide_eq_false rfl) hij)
    all_goals fin_cases k <;> first | assumption | exact (of_decide_eq_false rfl hjk).elim

/-- A finite family of ordinary links and one ultrafilter link have uncountably many
common forward neighbors somewhere, unless the mixed rows already exist. -/
theorem fromSeed (binary : BinaryWithExceptions) (r : ℝ → ℝ → ℝ → Prop)
    (sym : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y))
    (hb : ¬ ∃ s : Set ℝ, #s = 4 ∧ s.Triplewise (fun x y z => ¬ r x y z))
    (W : Set ℝ) (b : ℕ ↪o ℝ) (hWb : ∀ i, b i ∈ W) (U : Ultrafilter ℕ) (hu : (U : Filter ℕ) ≤ atTop)
    (s : Set ℝ) (hWs : s ⊆ W) (hunc : ¬s.Countable) (apart : (∀ i, ∀ x ∈ s, b i < x) ∨ (∀ i, ∀ x ∈ s, x < b i))
    (red : ∀ x ∈ s, ∀ᶠ m in U, ∀ᶠ n in U, r (b m) (b n) x) :
    ∃ a b : ℕ ↪o ℝ, range a ∪ range b ⊆ W ∧ (∀ i j, a i < b j) ∧ (∀ i j k, i < j → r (a i) (a j) (b k)) ∧
      (∀ i j k, j < k → r (a i) (b j) (b k)) := by
  classical
  by_contra noRows
  have away (i : ℕ) (x : ℝ) (hx : x ∈ s) : b i ≠ x := apart.elim
    (fun h => (h i x hx).ne) (fun h => (h i x hx).ne.symm)
  have rich (F : Finset ℕ) (t : Set ℝ) (hts : t ⊆ s) (ht : ¬t.Countable) :
      ∃ x ∈ t, ¬ {y ∈ t | x < y ∧ (∀ n ∈ F, r (b n) x y) ∧ ∀ᶠ n in U, r (b n) x y}.Countable := by
    by_contra! allSmall
    let bad x := {y ∈ t | x < y ∧ (∀ n ∈ F, r (b n) x y) ∧ ∀ᶠ n in U, r (b n) x y}
    let V : Option (↥F) → Ultrafilter ℕ := fun c => c.elim U (fun n => pure n.val)
    let g (c : Option (↥F)) (x y : ℝ) := ∀ᶠ n in V c, ¬r (b n) x y
    have cover (x : ℝ) (hx : x ∈ t) (y : ℝ) (hy : y ∈ t) (hxy : x < y) (hn : y ∉ bad x) :
        ∃ c, g c x y := by
      by_cases lim : ∀ᶠ n in U, r (b n) x y
      · have missing : ¬∀ n ∈ F, r (b n) x y := fun h => hn ⟨hy,hxy,h,lim⟩
        push Not at missing
        obtain ⟨n, hF, hblue⟩ := missing
        exact ⟨some ⟨n,hF⟩, by simpa [g,V] using hblue⟩
      · exact ⟨none, U.eventually_not.mpr lim⟩
    obtain ⟨c,l,u,sep,sub,edges⟩ := binary _ t bad g ht allSmall cover
    let w := range l ∪ range u
    have hall {x y z : ℝ} (hx : x ∈ w) (hy : y ∈ w) (hz : z ∈ w) (hxy : x < y) (hyz : y < z) :
        r x y z := by
      have e1 : ∀ᶠ n in V c, ¬r (b n) x y := edges _ hx _ hy hxy
      have e2 := edges _ hx _ hz (hxy.trans hyz)
      have e3 := edges _ hy _ hz hyz
      obtain ⟨n,h1,h2,h3⟩ := (e1.and (e2.and e3)).exists
      exact fourthRed r sym hb (away _ _ (hts (sub hx))) (away _ _ (hts (sub hy)))
        (away _ _ (hts (sub hz))) hxy.ne (hxy.trans hyz).ne hyz.ne h1 h2 h3
    exact noRows ⟨l,u,sub.trans (hts.trans hWs),sep, fun i j k hij => hall (Or.inl ⟨i,rfl⟩) (Or.inl ⟨j,rfl⟩)
      (Or.inr ⟨k,rfl⟩) (l.strictMono hij) (sep j k),
      fun i j k hjk => hall (Or.inl ⟨i,rfl⟩) (Or.inr ⟨j,rfl⟩) (Or.inr ⟨k,rfl⟩)
        (sep i j) (u.strictMono hjk)⟩
  obtain ⟨a,e,ha,hp,hq⟩ := fuseRows (fun x y n => r (b n) x y) (fun x m n => r (b m) (b n) x)
    U hu s hunc red rich
  rcases apart with below | above
  · exact noRows ⟨e.trans b, a, Set.union_subset (range_subset_iff.mpr (fun i => hWb (e i)))
      (range_subset_iff.mpr (fun i => hWs (ha i))), (fun i j => below (e i) _ (ha j)),
      fun i j k hij => hq k i j hij, fun i j k hjk => hp j k i hjk⟩
  · apply noRows
    refine ⟨a, e.trans b, Set.union_subset (range_subset_iff.mpr (fun i => hWs (ha i)))
      (range_subset_iff.mpr (fun i => hWb (e i))), fun i j => above _ _ (ha i), ?_, ?_⟩
    · intro i j k hij
      have h := hp i j k hij
      have xy := (a.strictMono hij).ne
      have xz := (above (e k) _ (ha i)).ne
      have yz := (above (e k) _ (ha j)).ne
      exact (sym _ _ _ xz yz.symm xy).2.mp ((sym _ _ _ xz.symm xy yz.symm).1.mp h)
    · intro i j k hjk
      have h := hq i j k hjk
      have xy := (above (e j) _ (ha i)).ne
      have xz := (above (e k) _ (ha i)).ne
      have yz := (b.strictMono (e.strictMono hjk)).ne
      exact (sym _ _ _ xy yz xz).1.mpr ((sym _ _ _ yz xz.symm xy.symm).2.mp h)

private abbrev I := (aleph.{0} 1).ord.ToType

private theorem avoidCountable (s : Set ℝ) (hs : ¬s.Countable) (bad : ℝ → Set ℝ)
    (hbad : ∀ x ∈ s, (bad x).Countable) :
    ∃ f : I ↪ ℝ, (∀ i, f i ∈ s) ∧ ∀ i j, i < j → f j ∉ bad (f i) := by
  classical
  have initial (i : I) : Countable (Iio i) :=
    by
      apply Cardinal.mk_le_aleph0_iff.mp
      apply Cardinal.lt_aleph_one_iff.mp
      simpa [I] using (Cardinal.mk_Iio_lt i (by simp [I]))
  have chooseNew (i : I) (f : ∀ j : I, j < i → s) :
      ∃ z : s, ∀ j (hj : j < i), z.val ≠ (f j hj).val ∧ z.val ∉ bad (f j hj).val := by
    let _ := initial i
    let excluded (j : Iio i) := insert (f j.val j.property).val (bad (f j.val j.property).val)
    have hc : (⋃ j, excluded j).Countable := countable_iUnion fun j =>
      (hbad _ (f j.val j.property).property).insert _
    obtain ⟨x,hx,hout⟩ : (s \ ⋃ j, excluded j).Nonempty := by
      by_contra! empty
      exact hs (hc.mono (Set.sdiff_eq_empty.mp empty))
    refine ⟨⟨x,hx⟩, fun j hj => ?_⟩
    have hn : x ∉ excluded ⟨j,hj⟩ := fun hm => hout (mem_iUnion.mpr ⟨⟨j,hj⟩,hm⟩)
    simpa [excluded, not_or] using hn
  let pick (i : I) (f : ∀ j : I, j < i → s) := (chooseNew i f).choose
  let F : I → s := wellFounded_lt.fix pick
  have newPoint (i j : I) (hij : i < j) : (F j).val ≠ (F i).val ∧ (F j).val ∉ bad (F i).val := by
    have eqn : F j = pick j (fun a _ => F a) := WellFounded.fix_eq _ _ _
    rw [eqn]
    exact (chooseNew j (fun a _ => F a)).choose_spec i hij
  let f (i : I) : ℝ := F i
  have inj : Function.Injective f := by
    intro i j eq
    rcases lt_trichotomy i j with h|h|h
    · exact ((newPoint i j h).1 eq.symm).elim
    · exact h
    · exact ((newPoint j i h).1 eq).elim
  exact ⟨⟨f,inj⟩,fun i => (F i).property,fun i j h => (newPoint i j h).2⟩

private def Two (s : Set ℝ) (g : ℝ → ℝ → K) (c : K) : Prop :=
  ∃ l u : ℕ ↪o ℝ, (∀ i j, l i < u j) ∧ range l ∪ range u ⊆ s ∧
    ∀ x ∈ range l ∪ range u, ∀ y ∈ range l ∪ range u, x < y → g x y = c

private def RealArrow : Prop := ∀ (K : Type) [Finite K] [Nonempty K] (s : Set ℝ),
  ¬s.Countable → ∀ g : ℝ → ℝ → K, (∀ x y, g x y = g y x) → ∃ c, Two s g c

private theorem realBinary (arrow : RealArrow) : BinaryWithExceptions := by
  classical
  intro K _ s bad g hs hbad cover
  obtain ⟨f,inside,avoid⟩ := avoidCountable s hs bad hbad
  let unc : Uncountable I := Cardinal.aleph0_lt_mk_iff.mp (by simp [I])
  have big : ¬(range f).Countable := by
    intro hc
    have := hc.to_subtype
    exact not_countable (α := I) (Equiv.ofInjective f f.injective).injective.countable
  let rank := Function.invFun f
  have back {x : ℝ} (hx : x ∈ range f) : f (rank x) = x := Function.invFun_eq hx
  let col (x y : ℝ) : Option K := if h : rank x < rank y ∧ ∃ k, g k x y then some h.2.choose else none
  let edge x y := col (min x y) (max x y)
  obtain ⟨k,l,u,sep,mem,edges⟩ := arrow _ _ big edge (fun x y => by simp [edge,min_comm x y,max_comm x y])
  have raw {x y : ℝ} (hx : x ∈ range l ∪ range u) (hy : y ∈ range l ∪ range u) (h : x < y) :
      col x y = k := by simpa [edge,min_eq_left h.le,max_eq_right h.le] using edges x hx y hy h
  have ok {x y : ℝ} (hx : x ∈ range f) (hy : y ∈ range f) (hlt : x < y) (hr : rank x < rank y) :
      ∃ k, g k x y := by
    have hx' := inside (rank x)
    have hy' := inside (rank y)
    have hn := avoid _ _ hr
    rw [back hx] at hx' hn
    rw [back hy] at hy' hn
    exact cover x hx' y hy' hlt hn
  cases k with
  | none =>
    obtain ⟨e,he⟩ := (wellQuasiOrdered_le (α := I)).exists_monotone_subseq (fun n => rank (l n))
    have left (n : ℕ) : l n ∈ range l ∪ range u := Or.inl ⟨n,rfl⟩
    have lt := l.strictMono (e.strictMono (by decide : 0 < 1))
    have ranklt : rank (l (e 0)) < rank (l (e 1)) := lt_of_le_of_ne (he 0 1 (by decide))
      (fun eq => lt.ne ((back (mem (left _))).symm.trans ((congrArg f eq).trans (back (mem (left _))))))
    have hcol := raw (left (e 0)) (left (e 1)) lt
    simp [col,ranklt,ok (mem (left _)) (mem (left _)) lt ranklt] at hcol
  | some k =>
    refine ⟨k,l,u,sep,mem.trans (range_subset_iff.mpr inside),?_⟩
    intro x hx y hy h
    have eq := raw hx hy h
    dsimp only [col] at eq
    split at eq
    next hh => exact Option.some.inj eq ▸ hh.2.choose_spec
    next => contradiction

private theorem twoRows (s : Set ℝ) (g : ℝ → ℝ → K) (c : K) (l u : ℕ ↪o ℝ)
    (sep : ∀ i j, l i < u j) (lm : ∀ i, l i ∈ s) (um : ∀ i, u i ∈ s)
    (ll : ∀ i j, i < j → g (l i) (l j) = c) (uu : ∀ i j, i < j → g (u i) (u j) = c)
    (lu : ∀ i j, g (l i) (u j) = c) : Two s g c := by
  refine ⟨l,u,sep,Set.union_subset (range_subset_iff.mpr lm) (range_subset_iff.mpr um),?_⟩
  rintro _ (⟨i,rfl⟩|⟨i,rfl⟩) _ (⟨j,rfl⟩|⟨j,rfl⟩) h
  · exact ll i j (l.lt_iff_lt.mp h)
  · exact lu i j
  · exact ((sep j i).asymm h).elim
  · exact uu i j (u.lt_iff_lt.mp h)

/-- The colors of increasing infinite homogeneous rows. Minimize this finite set
over uncountable subsets so every remaining row color has a rich forward link. -/
private noncomputable def rowColors [Fintype K] (g : ℝ → ℝ → K) (s : Set ℝ) : Finset K := by
  classical
  exact Finset.univ.filter (fun c => ∃ a : ℕ ↪o ℝ, (∀ i, a i ∈ s) ∧ ∀ i j, i < j → g (a i) (a j) = c)

private theorem stableSet [Fintype K] (g : ℝ → ℝ → K) (s : Set ℝ) (hs : ¬s.Countable) :
    ∃ S ⊆ s, ¬S.Countable ∧ ∀ c ∈ rowColors g S, ∀ t ⊆ S, ¬t.Countable →
      ∃ x ∈ t, ¬ {y ∈ t | x < y ∧ g x y = c}.Countable := by
  classical
  let P (n : ℕ) := ∃ t ⊆ s, ¬t.Countable ∧ (rowColors g t).card = n
  have ex : ∃ n, P n := ⟨_,s,Subset.rfl,hs,rfl⟩
  obtain ⟨S,sub,big,eq⟩ := Nat.find_spec ex
  have same (t : Set ℝ) (ts : t ⊆ S) (ht : ¬t.Countable) : rowColors g t = rowColors g S := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      obtain ⟨a,ha,hc⟩ := (Finset.mem_filter.mp hc).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a, fun i => ts (ha i), hc⟩
    · rw [eq]
      exact Nat.find_min' ex ⟨t,ts.trans sub,ht,rfl⟩
  refine ⟨S,sub,big,?_⟩
  intro c hc t ht hbig
  by_contra! small
  obtain ⟨f,inside,avoid⟩ := avoidCountable t hbig (fun x => {y ∈ t | x < y ∧ g x y = c}) small
  let unc : Uncountable I := Cardinal.aleph0_lt_mk_iff.mp (by simp [I])
  have rg : ¬(range f).Countable := by
    intro hc
    have := hc.to_subtype
    exact not_countable (α := I) (Equiv.ofInjective f f.injective).injective.countable
  have hcol : c ∈ rowColors g (range f) := by rwa [same _ ((range_subset_iff.mpr inside).trans ht) rg]
  obtain ⟨a,inside',edge⟩ := (Finset.mem_filter.mp hcol).2
  choose pre hpre using inside'
  obtain ⟨e,he⟩ := (wellQuasiOrdered_le (α := I)).exists_monotone_subseq pre
  have iLt : e 0 < e 1 := e.strictMono (by decide)
  have realLt : f (pre (e 0)) < f (pre (e 1)) := by simpa only [hpre] using a.strictMono iLt
  have h := avoid _ _ (lt_of_le_of_ne (he 0 1 (by decide)) (ne_of_apply_ne f realLt.ne))
  exact h ⟨inside _,realLt,by simpa only [hpre] using edge _ _ iLt⟩

private noncomputable def pickColor [Finite K] (F : Ultrafilter α) (v : α → K) : K :=
  (Ultrafilter.eventually_exists_iff.mp (Eventually.of_forall (f := (F : Filter α))
    (fun x => show ∃ k, v x = k from ⟨_,rfl⟩))).choose

private theorem pickSpec [Finite K] (F : Ultrafilter α) (v : α → K) :
    ∀ᶠ x in F, v x = pickColor F v :=
  (Ultrafilter.eventually_exists_iff.mp (Eventually.of_forall (f := (F : Filter α))
    (fun x => show ∃ k, v x = k from ⟨_,rfl⟩))).choose_spec

private theorem pick_eq [Finite K] {F : Ultrafilter α} {v : α → K} {k : K}
    (h : ∀ᶠ x in F, v x = k) : pickColor F v = k := by
  obtain ⟨_,he,hk⟩ := ((pickSpec F v).and h).exists
  exact he.symm.trans hk

private theorem filterSmall [Fintype K] (s : Set ℝ) (g : ℝ → ℝ → K) (sym : ∀ x y, g x y = g y x)
    (no : ∀ c, ¬Two s g c)
    (rich : ∀ c ∈ rowColors g s, ∀ t ⊆ s, ¬t.Countable →
      ∃ x ∈ t, ¬{y ∈ t | x < y ∧ g x y = c}.Countable)
    (F : Ultrafilter ℝ) (C : Set ℝ) (hc : C.Countable) (hC : C ∈ F) (Cs : C ⊆ s)
    (z : ℝ) (approach : ∀ a < z, Ioo a z ∈ F) :
    let c := pickColor F (fun x => pickColor F (g x))
    {y ∈ s | pickColor F (fun x => g x y) = c}.Countable := by
  classical
  let c := pickColor F (fun x => pickColor F (g x))
  let Y := {y ∈ s | pickColor F (fun x => g x y) = c}
  change Y.Countable
  by_contra big
  obtain ⟨b,hb⟩ := hc.exists_eq_range (Filter.nonempty_of_mem (f := (F : Filter ℝ)) hC)
  let enc := Function.invFun b
  let U := F.map enc
  have transfer (p : ℝ → Prop) (hp : ∀ᶠ x in F, p x) : ∀ᶠ i in U, p (b i) := by
    change ∀ᶠ x in F, p (b (enc x))
    filter_upwards [hp,hC] with x hx hc
    rwa [Function.invFun_eq (hb ▸ hc : x ∈ range b)]
  have inc : ∀ᶠ i in U, ∀ᶠ j in U, b i < b j := by
    apply transfer (fun x => ∀ᶠ j in U, x < b j)
    have below : ∀ᶠ x in F, x < z := mem_of_superset (approach (z-1) (by linarith)) (fun _ hx => hx.2)
    exact below.mono fun x hx => transfer _ (mem_of_superset (approach x hx) (fun _ h => h.1))
  have hu : (U : Filter ℕ) ≤ atTop := by
    rcases U.le_cofinite_or_eq_pure with h|⟨n,hn⟩
    · exact h.trans_eq Nat.cofinite_eq_atTop
    · rw [hn] at inc
      simp at inc
  have edges : ∀ᶠ i in U, ∀ᶠ j in U, g (b i) (b j) = c := by
    apply transfer (fun x => ∀ᶠ j in U, g x (b j) = c)
    filter_upwards [pickSpec F (fun x => pickColor F (g x))] with x hx
    exact transfer _ (hx ▸ pickSpec F (g x))
  have memS : ∀ᶠ i in U, b i ∈ s := transfer _ (mem_of_superset hC Cs)
  have single : c ∈ rowColors g s := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    let p i j (_ : ℕ) := b i ∈ s ∧ b i < b j ∧ g (b i) (b j) = c
    have hp : ∀ᶠ i in U, ∀ᶠ j in U, ∀ᶠ k in U, p i j k := by
      filter_upwards [memS,inc,edges] with i hi hii hie
      filter_upwards [hii,hie] with j hj hjc
      exact Eventually.of_forall fun _ => ⟨hi,hj,hjc⟩
    obtain ⟨e,he⟩ := diagonalTriple hu p hp
    have h {i j : ℕ} (hij : i < j) := he i j (j+1) hij (Nat.lt_succ_self _)
    exact ⟨OrderEmbedding.ofStrictMono (fun i => b (e i)) (fun _ _ hij => (h hij).2.1),
      fun i => (h (Nat.lt_succ_self i)).1,fun _ _ hij => (h hij).2.2⟩
  obtain ⟨q,hl,hr⟩ := splitUncountable Y big
  have sides : ∃ T ⊆ Y, ¬T.Countable ∧ ∃ A : Set ℝ, (∀ᶠ i in U, b i ∈ A) ∧
      ((∀ x ∈ A, ∀ y ∈ T, x < y) ∨ (∀ x ∈ A, ∀ y ∈ T, y < x)) := by
    by_cases h : ∀ᶠ i in U, b i ≤ (q:ℝ)
    · exact ⟨_,inter_subset_left,hr,Iic _,h,Or.inl (fun _ hx _ hy => lt_of_le_of_lt hx hy.2)⟩
    · exact ⟨_,inter_subset_left,hl,Ioi _,by simpa using U.eventually_not.mpr h,
          Or.inr (fun _ hx _ hy => hy.2.trans hx)⟩
  obtain ⟨T,ty,ht,A,ha,apart⟩ := sides
  let Q (y : ℝ) (i j : ℕ) := b i ∈ s ∧ b i ∈ A ∧ g (b i) y = c ∧ b i < b j ∧ g (b i) (b j) = c
  have ini (y : ℝ) (hy : y ∈ T) : ∀ᶠ i in U, ∀ᶠ j in U, Q y i j := by
    have col : ∀ᶠ i in U, g (b i) y = c := transfer _ ((ty hy).2 ▸ pickSpec F (fun x => g x y))
    filter_upwards [memS,ha,col,inc,edges] with i hi hai hci hlt hcol
    exact (hlt.and hcol).mono fun _ h => ⟨hi,hai,hci,h⟩
  have rich' (Z : Finset ℕ) (t : Set ℝ) (ht' : t ⊆ T) (hbig : ¬t.Countable) := rich c single t
    (fun _ hy => (ty (ht' hy)).1) hbig
  obtain ⟨a,e,am,aa,both⟩ := fuseRows (fun x y _ => g x y = c) Q U hu T ht ini (by
    intro Z t ht' hbig
    obtain ⟨x,hx,h⟩ := rich' Z t ht' hbig
    refine ⟨x,hx,fun small => h (small.mono ?_)⟩
    intro y hy
    exact ⟨hy.1,hy.2.1,fun _ _ => hy.2.2,Eventually.of_forall fun _ => hy.2.2⟩)
  have data (i j : ℕ) := both i j (j+1) (Nat.lt_succ_self _)
  let d := OrderEmbedding.ofStrictMono (fun i => b (e i)) (fun i j hij => (both 0 i j hij).2.2.2.1)
  have dd (i j : ℕ) (h : i < j) : g (d i) (d j) = c := (both 0 i j h).2.2.2.2
  have dm (i : ℕ) : d i ∈ s := (data 0 i).1
  have asub (i : ℕ) := (ty (am i)).1
  rcases apart with below|above
  · exact no c (twoRows s g c d a (fun i j => below _ (data 0 i).2.1 _ (am j)) dm asub dd
      (fun i j h => aa i j 0 h) (fun i j => (data j i).2.2.1))
  · exact no c (twoRows s g c a d (fun i j => above _ (data 0 j).2.1 _ (am i)) asub dm
      (fun i j h => aa i j 0 h) dd (fun i j => (sym _ _).trans (data i j).2.2.1))

/-- The indices preserving an uncountable column form a large set themselves. -/
private theorem manyColumns {s : Set ℝ} (hs : ¬s.Countable) (U : Ultrafilter ℕ)
    (p : ℝ → ℕ → Prop) (hp : ∀ x ∈ s, ∀ᶠ n in U, p x n) :
    ∀ᶠ n in U, ¬{x ∈ s | p x n}.Countable := by
  by_contra h
  have loss := U.eventually_not.mpr h
  obtain ⟨n,wrong,right⟩ := uncountableColumn hs U loss p hp
  exact wrong right

/-- In the sparse case choose an arbitrarily large finite block, retaining two
uncountable reservoirs simultaneously. -/
private theorem finiteBlue (r : ℝ → ℝ → ℝ → Prop) (c : ℕ ↪o ℝ) (U : Ultrafilter ℕ)
    (hu : (U : Filter ℕ) ≤ atTop) (T : Bool → Set ℝ) (unc : ∀ h, ¬(T h).Countable)
    (blue : ∀ h, ∀ y ∈ T h, ∀ᶠ i in U, ∀ᶠ j in U, ¬r (c i) (c j) y) (k : ℕ) :
    ∃ v : Fin k → ℕ, StrictMono v ∧ ∃ t : Bool → Set ℝ, (∀ h, t h ⊆ T h ∧ ¬(t h).Countable) ∧
      ∀ h, ∀ y ∈ t h, ∀ i j : Fin k, i < j → ¬r (c (v i)) (c (v j)) y := by
  classical
  have build (m : ℕ) : ∃ v : Fin m → ℕ, StrictMono v ∧ ∃ t : Bool → Set ℝ,
      (∀ h, t h ⊆ T h ∧ ¬(t h).Countable) ∧ ∀ h, ∀ y ∈ t h,
        (∀ i j : Fin m, i < j → ¬r (c (v i)) (c (v j)) y) ∧
        (∀ i : Fin m, ∀ᶠ j in U, ¬r (c (v i)) (c j) y) := by
    induction m with
    | zero =>
      exact ⟨Fin.elim0,fun i => i.elim0,T,fun h => ⟨Subset.rfl,unc h⟩,
        fun _ _ _ => ⟨fun i => i.elim0,fun i => i.elim0⟩⟩
    | succ m ih =>
      obtain ⟨v,inc,t,ht,old⟩ := ih
      let accept (y : ℝ) (n : ℕ) :=
        (∀ᶠ j in U, ¬r (c n) (c j) y) ∧ ∀ i : Fin m, ¬r (c (v i)) (c n) y
      have ok (h : Bool) (y : ℝ) (hy : y ∈ t h) : ∀ᶠ n in U, accept y n :=
        (blue h y ((ht h).1 hy)).and (eventually_all.mpr (old h y hy).2)
      have later : ∀ᶠ n in U, ∀ i : Fin m, v i < n := eventually_all.mpr
        (fun i => hu (eventually_gt_atTop (v i)))
      obtain ⟨n,hn,keep⟩ := (later.and (eventually_all.mpr (fun h => manyColumns (ht h).2 U accept (ok h)))).exists
      let w : Fin (m+1) → ℕ := Fin.snoc (α := fun _ => ℕ) v n
      refine ⟨w, ?_,fun h => {y ∈ t h | accept y n}, fun h => ⟨fun _ hy => (ht h).1 hy.1,keep h⟩,?_⟩
      · intro i j hij
        induction i using Fin.lastCases with
        | last => exact ((Fin.le_last _).not_gt hij).elim
        | cast i =>
          induction j using Fin.lastCases with
          | last => simpa [w] using hn i
          | cast j => simpa [w] using inc (Fin.castSucc_lt_castSucc_iff.mp hij)
      · intro h y hy
        constructor
        · intro i j hij
          induction i using Fin.lastCases with
          | last => exact ((Fin.le_last _).not_gt hij).elim
          | cast i =>
            induction j using Fin.lastCases with
            | last => simpa [w] using hy.2.2 i
            | cast j => simpa [w] using (old h y hy.1).1 i j (Fin.castSucc_lt_castSucc_iff.mp hij)
        · intro i
          induction i using Fin.lastCases with
          | last => simpa [w] using hy.2.1
          | cast i => simpa [w] using (old h y hy.1).2 i
  obtain ⟨v,inc,t,ht,good⟩ := build k
  exact ⟨v,inc,t,ht,fun h y hy => (good h y hy).1⟩

/-- Either a seed already yields all mixed rows, or any separated source supplies finite
blocks blue to uncountable parts of both specified reservoirs. -/
private theorem chooseBlock (binary : BinaryWithExceptions) (r : ℝ → ℝ → ℝ → Prop)
    (sym : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y))
    (hb : ¬ ∃ s : Set ℝ, #s = 4 ∧ s.Triplewise (fun x y z => ¬ r x y z))
    (noRows : ¬∃ a b : ℕ ↪o ℝ, (∀ i j, a i < b j) ∧
      (∀ i j k, i < j → r (a i) (a j) (b k)) ∧ (∀ i j k, j < k → r (a i) (b j) (b k)))
    (S : Set ℝ) (hs : ¬S.Countable) (T : Bool → Set ℝ) (ht : ∀ h, ¬(T h).Countable)
    (apart : ∀ h, (∀ x ∈ S, ∀ y ∈ T h, x < y) ∨ (∀ x ∈ S, ∀ y ∈ T h, y < x)) (k : ℕ) :
    ∃ v : Fin k → ℝ, StrictMono v ∧ (∀ i, v i ∈ S) ∧ ∃ t : Bool → Set ℝ,
      (∀ h, t h ⊆ T h ∧ ¬(t h).Countable) ∧
      ∀ h, ∀ y ∈ t h, ∀ i j : Fin k, i < j → ¬r (v i) (v j) y := by
  classical
  obtain ⟨_,_,a,inc,_,hm⟩ := increasingLimit hs
  let c := OrderEmbedding.ofStrictMono a inc
  have cm (i : ℕ) : c i ∈ S := (hm i).1
  obtain ⟨U,hu⟩ := Ultrafilter.exists_le (atTop : Filter ℕ)
  let A (h : Bool) := {x ∈ T h | ∀ᶠ i in U, ∀ᶠ j in U, r (c i) (c j) x}
  have small (h : Bool) : (A h).Countable := by
    by_contra big
    have side : (∀ i, ∀ x ∈ A h, c i < x) ∨ (∀ i, ∀ x ∈ A h, x < c i) :=
      (apart h).imp (fun p i _ hx => p _ (cm i) _ hx.1) (fun p i _ hx => p _ (cm i) _ hx.1)
    obtain ⟨l,u,_,sep,p,q⟩ := fromSeed binary r sym hb univ c (by simp) U hu (A h)
      (subset_univ _) big side (fun _ hx => hx.2)
    exact noRows ⟨l,u,sep,p,q⟩
  let t0 (h : Bool) := T h \ A h
  have large (h : Bool) : ¬(t0 h).Countable := fun hno => ht h (hno.of_sdiff (small h))
  have hblue (h : Bool) (y : ℝ) (hy : y ∈ t0 h) : ∀ᶠ i in U, ∀ᶠ j in U, ¬r (c i) (c j) y := by
    have notred : ¬ (∀ᶠ i in U, ∀ᶠ j in U, r (c i) (c j) y) := fun hr => hy.2 ⟨hy.1,hr⟩
    simpa only [Ultrafilter.eventually_not] using notred
  obtain ⟨v,vinc,t,sub,blue⟩ := finiteBlue r c U hu t0 large hblue k
  exact ⟨fun i => c (v i),c.strictMono.comp vinc,fun i => cm _,t,
    fun h => ⟨fun _ hx => ((sub h).1 hx).1,(sub h).2⟩,blue⟩

/-- Produce two columns of growing finite blocks. Every pair in a block is blue
towards every vertex at a later stage, in either column. -/
private theorem growingBlocks (r : ℝ → ℝ → ℝ → Prop)
    (choice : ∀ (S : Set ℝ), ¬S.Countable → ∀ T : Bool → Set ℝ, (∀ h, ¬(T h).Countable) →
      (∀ h, (∀ x ∈ S, ∀ y ∈ T h, x < y) ∨ (∀ x ∈ S, ∀ y ∈ T h, y < x)) →
      ∀ k : ℕ, ∃ v : Fin k → ℝ, StrictMono v ∧ (∀ i, v i ∈ S) ∧ ∃ t : Bool → Set ℝ,
        (∀ h, t h ⊆ T h ∧ ¬(t h).Countable) ∧
        ∀ h, ∀ y ∈ t h, ∀ i j : Fin k, i < j → ¬r (v i) (v j) y) :
    ∃ B : (n : ℕ) → Bool → Fin (n+2) → ℝ, (∀ n h, StrictMono (B n h)) ∧
      (∀ i j u v, B i false u < B j true v) ∧
      (∀ h i j u v, i < j → B i h u < B j h v) ∧
      ∀ i j t h u v w, i < j → u < v → ¬r (B i t u) (B i t v) (B j h w) := by
  classical
  obtain ⟨cut,hl,hr⟩ := splitUncountable univ Set.not_countable_univ
  let W (h : Bool) : Set ℝ := if h then univ ∩ Ioi (cut : ℝ) else univ ∩ Iio (cut : ℝ)
  have sep (x : ℝ) (hx : x ∈ W false) (y : ℝ) (hy : y ∈ W true) : x < y :=
    (show x < (cut : ℝ) from hx.2).trans hy.2
  let Res := {T : Bool → Set ℝ // ∀ h, T h ⊆ W h ∧ ¬(T h).Countable}
  have stage (k : ℕ) (T : Res) : ∃ B : Bool → Fin k → ℝ, ∃ N : Res,
      (∀ h, StrictMono (B h)) ∧ (∀ h i, B h i ∈ T.val h) ∧ (∀ h, N.val h ⊆ T.val h) ∧
      (∀ h i y, y ∈ N.val h → B h i < y) ∧
      (∀ t h y, y ∈ N.val h → ∀ i j, i < j → ¬r (B t i) (B t j) y) := by
    obtain ⟨d,leftSource,leftTail⟩ := splitUncountable _ (T.property false).2
    let L := T.val false ∩ Iio (d : ℝ)
    let targets (h : Bool) := if h then T.val true else T.val false ∩ Ioi (d : ℝ)
    have big (h : Bool) : ¬(targets h).Countable := by
      cases h
      · exact leftTail
      · exact (T.property true).2
    have side (h : Bool) : (∀ x ∈ L, ∀ y ∈ targets h, x < y) ∨ (∀ x ∈ L, ∀ y ∈ targets h, y < x) := by
      cases h
      · exact Or.inl fun x hx y hy => (show x < (d : ℝ) from hx.2).trans hy.2
      · exact Or.inl fun x hx y hy => sep _ ((T.property false).1 hx.1) _ ((T.property true).1 hy)
    obtain ⟨l,incL,memL,U,hU,blueL⟩ := choice L leftSource targets big side k
    obtain ⟨e,rightSource,rightTail⟩ := splitUncountable _ (hU true).2
    let R := U true ∩ Iio (e : ℝ)
    let rest (h : Bool) := if h then U true ∩ Ioi (e : ℝ) else U false
    have big' (h : Bool) : ¬(rest h).Countable := by
      cases h
      · exact (hU false).2
      · exact rightTail
    have side' (h : Bool) : (∀ x ∈ R, ∀ y ∈ rest h, x < y) ∨ (∀ x ∈ R, ∀ y ∈ rest h, y < x) := by
      cases h
      · exact Or.inr fun x hx y hy => sep _ ((T.property false).1 ((hU false).1 hy).1)
          _ ((T.property true).1 ((hU true).1 hx.1))
      · exact Or.inl fun x hx y hy => (show x < (e : ℝ) from hx.2).trans hy.2
    obtain ⟨u,incU,memU,N,hN,blueU⟩ := choice R rightSource rest big' side' k
    have subU (h : Bool) : N h ⊆ U h := by
      cases h
      · exact (hN false).1
      · exact fun _ hy => ((hN true).1 hy).1
    have subT (h : Bool) : N h ⊆ T.val h := by
      cases h
      · exact fun _ hy => ((hU false).1 (subU false hy)).1
      · exact (subU true).trans (hU true).1
    let N' : Res := ⟨N,fun h => ⟨(subT h).trans (T.property h).1,(hN h).2⟩⟩
    refine ⟨(fun h => if h then u else l),N',?_,?_,subT,?_,?_⟩
    · intro h; cases h
      · exact incL
      · exact incU
    · intro h i; cases h
      · exact (memL i).1
      · exact (hU true).1 (memU i).1
    · intro h i y hy; cases h
      · exact (show l i < (d : ℝ) from (memL i).2).trans ((hU false).1 (subU false hy)).2
      · exact (show u i < (e : ℝ) from (memU i).2).trans ((hN true).1 hy).2
    · intro t h y hy; cases t
      · exact blueL h y (subU h hy)
      · exact blueU h y hy
  choose B next inc mem sub earlier blue using stage
  let init : Res := ⟨W,by intro h; cases h <;> exact ⟨Subset.rfl,by assumption⟩⟩
  let T : ℕ → Res := Nat.rec init (fun n s => next (n+2) s)
  have succ (n : ℕ) : T (n+1) = next (n+2) (T n) := rfl
  have nested (h : Bool) : Antitone fun i => (T i).val h :=
    antitone_nat_of_succ_le fun i => sub (i+2) (T i) h
  have hm {i j : ℕ} (hij : i < j) (h : Bool) (v : Fin (j+2)) :
      B (j+2) (T j) h v ∈ (next (i+2) (T i)).val h :=
    nested h (show i+1 ≤ j from hij) (mem _ _ _ _)
  exact ⟨(fun n => B (n+2) (T n)),fun n => inc _ _,
    fun i j u v => sep _ (((T i).property false).1 (mem _ _ _ _)) _ (((T j).property true).1 (mem _ _ _ _)),
    fun h i j u v hij => earlier _ _ h u _ (hm hij h v),
    fun i j t h u v w hij huv => blue _ _ t h _ (hm hij h w) u v huv⟩

/-- On a disjoint union of growing finite sets choose an ultrafilter avoiding any set
with at most one point in every fiber, and containing every tail of the stage coordinate. -/
private theorem stripFilter :
    ∃ U : Ultrafilter ((n : ℕ) × Fin (n+2)),
      (∀ m : ℕ, ∀ᶠ (d : (n : ℕ) × Fin (n+2)) in U, m < d.1) ∧
      ∀ p : ((n : ℕ) × Fin (n+2)) → Prop, (∀ n, {i : Fin (n+2) | ¬p ⟨n,i⟩}.Subsingleton) →
        ∀ᶠ d in U, p d := by
  classical
  let D := (n : ℕ) × Fin (n+2)
  let exc (s : Set D) (n : ℕ) := Finset.univ.filter (fun i : Fin (n+2) => (⟨n,i⟩ : D) ∉ s)
  let F : Filter D := {
    sets := {s | ∃ M : ℕ, ∀ n, (exc s n).card ≤ M}
    univ_sets := ⟨0,by simp [exc]⟩
    sets_of_superset := by
      rintro s t ⟨M,hM⟩ st
      refine ⟨M,fun n => (Finset.card_le_card ?_).trans (hM n)⟩
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun h => (Finset.mem_filter.mp hi).2 (st h)⟩
    inter_sets := by
      rintro s t ⟨M,hM⟩ ⟨N,hN⟩
      refine ⟨M+N,fun n => ?_⟩
      have sub : exc (s ∩ t) n ⊆ exc s n ∪ exc t n := by
        intro i hi
        simp only [exc,Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_inter_iff,Finset.mem_union] at hi ⊢
        tauto
      exact (Finset.card_le_card sub).trans ((Finset.card_union_le ..).trans (Nat.add_le_add (hM n) (hN n))) }
  have nontriv : F.NeBot := by
    apply Filter.neBot_iff.mpr
    intro eqBot
    have he : (∅ : Set D) ∈ F := by rw [eqBot]; simp
    obtain ⟨M,hM⟩ := he
    have tooBig := hM M
    simp [exc] at tooBig
  obtain ⟨U,hU⟩ := Ultrafilter.exists_le F
  refine ⟨U,?_,?_⟩
  · intro m
    apply hU
    refine ⟨m+2,fun n => ?_⟩
    by_cases hl : n ≤ m
    · exact (Finset.card_le_univ _).trans (by simp; omega)
    · simp [exc, Nat.lt_of_not_ge hl]
  · intro p hp
    apply hU
    refine ⟨1,fun n => Finset.card_le_one.mpr ?_⟩
    intro i hi j hj
    exact hp n (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

/-- Realize an iterated ultrafilter condition by a single sequence of increasing stages. -/
private theorem stripDiagonal (U : Ultrafilter ((n : ℕ) × Fin (n+2)))
    (tail : ∀ m : ℕ, ∀ᶠ (d : (n : ℕ) × Fin (n+2)) in U, m < d.1)
    (P : ((n : ℕ) × Fin (n+2)) → ((n : ℕ) × Fin (n+2)) → ((n : ℕ) × Fin (n+2)) → Prop)
    (h : ∀ᶠ d in U, ∀ᶠ e in U, ∀ᶠ f in U, P d e f) :
    ∃ seq : ℕ → ((n : ℕ) × Fin (n+2)), StrictMono (fun i => (seq i).1) ∧
      ∀ i j k, i < j → j < k → P (seq i) (seq j) (seq k) := by
  classical
  let D := (n : ℕ) × Fin (n+2)
  let B d e := ∀ᶠ f in U, P d e f
  let A d := ∀ᶠ e in U, B d e
  let pre (i : ℕ) : Finset D := (Finset.range i).sigma (fun _ => Finset.univ)
  let rel (x y : D) := x.1 < y.1 ∧ B x y ∧ ∀ i ∈ pre x.1, B i x → P i x y
  have ext (F : Finset D) (hf : ∀ x ∈ F, A x) : ∃ y, A y ∧ ∀ x ∈ F, rel x y := by
    have one (x : D) (hx : x ∈ F) : ∀ᶠ y in U, rel x y := by
      have finish : ∀ᶠ y in U, ∀ i ∈ pre x.1, B i x → P i x y := by
        apply (pre x.1).finite_toSet.eventually_all.mpr
        intro i _
        by_cases hi : B i x
        · exact hi.mono fun _ hy _ => hy
        · exact Eventually.of_forall fun _ hz => (hi hz).elim
      exact (tail x.1).and ((hf x hx).and finish)
    exact (h.and (F.finite_toSet.eventually_all.mpr one)).exists
  obtain ⟨f,_,hf⟩ := exists_seq_of_forall_finset_exists A rel ext
  have inc : StrictMono fun i => (f i).1 := fun i j hij => (hf i j hij).1
  refine ⟨f,inc,fun i j k hij hjk => (hf j k hjk).2.2 _ ?_ (hf i j hij).2.1⟩
  exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (inc hij), Finset.mem_univ _⟩

/-- Under the growing-block hypotheses the threefold limit is red for all eight
assignments to the two columns. Two bad entries in one fiber would give a blue four-set. -/
private theorem rowsOfGrowing (r : ℝ → ℝ → ℝ → Prop)
    (sym : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y))
    (hb : ¬ ∃ s : Set ℝ, #s = 4 ∧ s.Triplewise (fun x y z => ¬ r x y z))
    (B : (n : ℕ) → Bool → Fin (n+2) → ℝ) (inc : ∀ n h, StrictMono (B n h))
    (sep : ∀ i j u v, B i false u < B j true v)
    (ord : ∀ h i j u v, i < j → B i h u < B j h v)
    (blue : ∀ i j t h u v w, i < j → u < v → ¬r (B i t u) (B i t v) (B j h w)) :
    ∃ a b : ℕ ↪o ℝ, (∀ i j, a i < b j) ∧ (∀ i j k, i < j → r (a i) (a j) (b k)) ∧
      (∀ i j k, j < k → r (a i) (b j) (b k)) := by
  classical
  let D := (n : ℕ) × Fin (n+2)
  let p (h : Bool) (d : D) := B d.1 h d.2
  have ne {d e : D} (hd : d.1 < e.1) (u v : Bool) : p u d ≠ p v e := by
    cases u <;> cases v
    · exact (ord _ _ _ _ _ hd).ne
    · exact (sep ..).ne
    · exact (sep ..).ne.symm
    · exact (ord _ _ _ _ _ hd).ne
  obtain ⟨U,tail,large⟩ := stripFilter
  have product (t u v : Bool) : ∀ᶠ d in U, ∀ᶠ e in U, ∀ᶠ f in U, r (p t d) (p u e) (p v f) := by
    apply large
    intro n a ha b hb'
    have clash (a b : Fin (n+2)) (hab : a < b)
        (xa : ¬ (∀ᶠ e in U, ∀ᶠ f in U, r (B n t a) (p u e) (p v f)))
        (xb : ¬ (∀ᶠ e in U, ∀ᶠ f in U, r (B n t b) (p u e) (p v f))) : False := by
      have ea : ∀ᶠ e in U, ∀ᶠ f in U, ¬r (B n t a) (p u e) (p v f) := by simpa only [Ultrafilter.eventually_not] using xa
      have eb : ∀ᶠ e in U, ∀ᶠ f in U, ¬r (B n t b) (p u e) (p v f) := by simpa only [Ultrafilter.eventually_not] using xb
      obtain ⟨e,he,hA,hB⟩ := ((tail n).and (ea.and eb)).exists
      obtain ⟨f,hf,badA,badB⟩ := ((tail e.1).and (hA.and hB)).exists
      have different (j : Fin (n+2)) (d : D) (w : Bool) (hlt : n < d.1) : B n t j ≠ p w d := ne (d := ⟨n,j⟩) hlt t w
      exact badB (fourthRed r sym hb ((inc n t) hab).ne (different a e u he) (different a f v (he.trans hf))
        (different b e u he) (different b f v (he.trans hf)) (ne hf u v)
        (blue _ _ _ _ _ _ _ he hab) (blue _ _ _ _ _ _ _ (he.trans hf) hab) badA)
    rcases lt_trichotomy a b with hab | hab | hba
    · exact (clash a b hab ha hb').elim
    · exact hab
    · exact (clash b a hba hb' ha).elim
  have total : ∀ᶠ d in U, ∀ᶠ e in U, ∀ᶠ f in U, ∀ t u v : Bool, r (p t d) (p u e) (p v f) := by
    have first := eventually_all.mpr (fun t => eventually_all.mpr (fun u => eventually_all.mpr (product t u)))
    filter_upwards [first] with d hd
    have second := eventually_all.mpr (fun t => eventually_all.mpr (fun u => eventually_all.mpr (hd t u)))
    filter_upwards [second] with e he
    exact eventually_all.mpr (fun t => eventually_all.mpr (fun u => eventually_all.mpr (he t u)))
  obtain ⟨f,stage,good⟩ := stripDiagonal U tail (fun d e f => ∀ t u v, r (p t d) (p u e) (p v f)) total
  let value (i : ℕ) := p (decide (i%2 = 1)) (f i)
  have inj : Function.Injective value := by
    intro i j h
    rcases lt_trichotomy i j with lt|eq|gt
    · exact (ne (stage lt) _ _ h).elim
    · exact eq
    · exact (ne (stage gt) _ _ h.symm).elim
  have allRed : Triplewise (fun i j k => r (value i) (value j) (value k)) :=
    sortedTriplewise _ (fun i j k h1 h2 h3 => sym _ _ _ (inj.ne h1) (inj.ne h2) (inj.ne h3))
      (fun i j k h1 h2 => good i j k h1 h2 _ _ _)
  let l (i : ℕ) := p false (f (2*i))
  let u (i : ℕ) := p true (f (2*i+1))
  have left (i : ℕ) : value (2*i) = l i := by simp [value,l]
  have right (i : ℕ) : value (2*i+1) = u i := by simp [value,u]
  have li : StrictMono l := fun i j hij => ord _ _ _ _ _ (stage (by omega : 2*i < 2*j))
  have ui : StrictMono u := fun i j hij => ord _ _ _ _ _ (stage (by omega : 2*i+1 < 2*j+1))
  refine ⟨OrderEmbedding.ofStrictMono l li,OrderEmbedding.ofStrictMono u ui,fun i j => sep ..,?_,?_⟩
  · intro i j k hij
    change r (l i) (l j) (u k)
    simpa only [left,right] using
      (allRed (i := 2*i) (j := 2*j) (k := 2*k+1) (by omega) (by omega) (by omega))
  · intro i j k hjk
    change r (l i) (u j) (u k)
    simpa only [left,right] using
      (allRed (i := 2*i) (j := 2*j+1) (k := 2*k+1) (by omega) (by omega) (by omega))

/-- A countably supported ultrafilter and an exceptional set, both recorded in the
original ambient set of reals. -/
private structure Germ where
  z : ℝ
  F : Ultrafilter ℝ
  C : Set ℝ
  E : Set ℝ

private structure Good [Finite K] (s : Set ℝ) (g : ℝ → ℝ → K) (J : Finset K)
    (D : Set ℝ) (w : Germ) : Prop where
  point : w.z ∈ s
  countC : w.C.Countable
  memC : w.C ∈ w.F
  subC : w.C ⊆ s
  conv : ∀ a b, a < w.z → w.z < b → Ioo a b ∈ w.F
  agree : ∀ u ∈ D, pickColor w.F (g u) = g u w.z
  countE : w.E.Countable
  clean : ∀ y ∈ s, y ∉ w.E → pickColor w.F (fun x => g x y) ∉ J

private def Possible [Finite K] (s : Set ℝ) (g : ℝ → ℝ → K) (J : Finset K) : Prop :=
  ∀ D E : Set ℝ, D.Countable → E.Countable → ∃ w : Germ, Good s g J D w ∧ w.z ∉ E

private def Profiles (K : Type*) (D : Set ℝ) := {h : Set (ℝ × K) // h.Finite ∧ h ⊆ D ×ˢ Set.univ}

private theorem countProfiles [Finite K] {D : Set ℝ} (hD : D.Countable) : Countable (Profiles K D) :=
  (countable_ofPred_finite_subset (hD.prod (countable_univ (α := K)))).to_subtype

private def Matches (g : ℝ → ℝ → K) (h : Set (ℝ × K)) (x : ℝ) := ∀ p ∈ h, g p.1 x = p.2

/-- Sample each realized rational interval and each finite color profile on a countable
test set. The countability refers to the full witnesses, including their ultrafilters. -/
private theorem sampleProfiles [Finite K] {D : Set ℝ} (hD : D.Countable) (g : ℝ → ℝ → K)
    (G : Germ → Prop) :
    ∃ W : Set Germ, W.Countable ∧ (∀ w ∈ W, G w) ∧ ∀ h : Profiles K D, ∀ a b : ℚ,
      (∃ w, G w ∧ (a:ℝ) < w.z ∧ w.z < (b:ℝ) ∧ Matches g h.val w.z) →
      ∃ w ∈ W, (a:ℝ) < w.z ∧ w.z < (b:ℝ) ∧ Matches g h.val w.z := by
  classical
  have := countProfiles (K := K) hD
  let hits (p : Profiles K D × ℚ × ℚ) (w : Germ) := G w ∧
    (p.2.1 : ℝ) < w.z ∧ w.z < (p.2.2 : ℝ) ∧ Matches g p.1.val w.z
  let P := {p : Profiles K D × ℚ × ℚ // ∃ w, hits p w}
  let pick (p : P) := p.property.choose
  refine ⟨range pick,countable_range _,?_,?_⟩
  · rintro _ ⟨p,rfl⟩
    exact p.property.choose_spec.1
  · intro h a b ex
    let p : P := ⟨(h,a,b),ex⟩
    exact ⟨pick p,mem_range_self _,p.property.choose_spec.2⟩

private theorem mergeGerms [Fintype K] [DecidableEq K] (s : Set ℝ) (g : ℝ → ℝ → K) (J : Finset K)
    (poss : Possible s g J)
    (small : ∀ (F : Ultrafilter ℝ) (C : Set ℝ), C.Countable → C ∈ F → C ⊆ s →
      ∀ z : ℝ, (∀ a < z, Ioo a z ∈ F) →
      {y ∈ s | pickColor F (fun x => g x y) = pickColor F (fun x => pickColor F (g x))}.Countable)
    (D E : Set ℝ) (hD : D.Countable) (hE : E.Countable) :
    ∃ j ∉ J, ∃ w : Germ, Good s g (insert j J) D w ∧ w.z ∉ E := by
  classical
  let Test := {d : Set ℝ // d.Countable}
  have samples (d : Test) := sampleProfiles d.property g (Good s g J d.val)
  choose W countW regular cover using samples
  let C (d : Test) := ⋃ w : W d, w.val.C
  have cC (d : Test) : (C d).Countable := by
    have := (countW d).to_subtype
    exact countable_iUnion fun w => (regular d w.val w.property).countC
  let next (d : Test) : Test := ⟨d.val ∪ C d,d.property.union (cC d)⟩
  let d (n : ℕ) := next^[n] (⟨D,hD⟩ : Test)
  have succ (n : ℕ) : d (n+1) = next (d n) := Function.iterate_succ_apply' next n _
  have mono : Monotone fun n => (d n).val := monotone_nat_of_le_succ fun n => by
    rw [succ]; exact subset_union_left
  let bigD := ⋃ n, (d n).val
  have countD : bigD.Countable := countable_iUnion fun n => (d n).property
  have subD (n : ℕ) : (d n).val ⊆ bigD := subset_iUnion (fun m => (d m).val) n
  have d0 : D ⊆ bigD := subD 0
  let support := ⋃ n, C (d n)
  have countSupp : support.Countable := countable_iUnion (fun n => cC (d n))
  have suppD : support ⊆ bigD := by
    intro x hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    apply subD (n+1)
    rw [succ]; exact Or.inr hn
  have suppS : support ⊆ s := by
    rintro x hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    obtain ⟨w,hw⟩ := mem_iUnion.mp hn
    exact (regular (d n) w.val w.property).subC hw
  let allE := ⋃ n, ⋃ w : W (d n), w.val.E
  have counts : allE.Countable := by
    apply countable_iUnion
    intro n
    have := (countW (d n)).to_subtype
    exact countable_iUnion fun w => (regular (d n) w.val w.property).countE
  let X := {z : ℝ | ∃ w : Germ, Good s g J bigD w ∧ w.z = z}
  let cell (h : Profiles K bigD) := {x ∈ X | Matches g h.val x}
  let exc (h : Profiles K bigD) := {x ∈ cell h | 𝓝[cell h ∩ Iio x] x = ⊥}
  have := countProfiles (K := K) countD
  have cexc : (⋃ h, exc h).Countable := countable_iUnion fun _ => countable_setOfPred_isolated_left_within
  obtain ⟨center,good,out⟩ := poss bigD (E ∪ allE ∪ ⋃ h, exc h) countD ((hE.union counts).union cexc)
  let z := center.z
  have outE : z ∉ E := fun h => out (Or.inl (Or.inl h))
  have outAll : z ∉ allE := fun h => out (Or.inl (Or.inr h))
  have approach (h : Profiles K bigD) (hz : Matches g h.val z) (a : ℝ) (ha : a < z) :
      ∃ y ∈ X, Matches g h.val y ∧ a < y ∧ y < z := by
    have hc : z ∈ cell h := ⟨⟨center,good,rfl⟩,hz⟩
    have nontriv : 𝓝[cell h ∩ Iio z] z ≠ ⊥ := fun he => out (Or.inr (mem_iUnion.mpr ⟨h,hc,he⟩))
    have cl := mem_closure_iff_nhdsWithin_neBot.mpr (Filter.neBot_iff.mpr nontriv)
    obtain ⟨y,hy,hm⟩ := mem_closure_iff_nhds.mp cl (Ioi a) (Ioi_mem_nhds ha)
    exact ⟨y,hm.1.1,hm.1.2,hy,hm.2⟩
  have finiteStage (H : Finset bigD) : ∃ n, ∀ u ∈ H, u.val ∈ (d n).val := by
    induction H using Finset.induction_on with
    | empty => exact ⟨0,by simp⟩
    | insert u H _ ih =>
      obtain ⟨n,hn⟩ := ih
      obtain ⟨m,hm⟩ := mem_iUnion.mp u.property
      refine ⟨max n m,?_⟩
      simpa using And.intro (mono (le_max_right n m) hm)
        (fun v hv => mono (le_max_left n m) (hn v hv))
  let IX := Finset bigD × ↥(Iio z)
  have existsNear (i : IX) : ∃ w : Germ, w.C ⊆ support ∧ w.E ⊆ allE ∧ w.z ∈ Ioo i.2.val z ∧
      (∀ u ∈ i.1, pickColor w.F (g u.val) = g u.val z) ∧ Good s g J ∅ w := by
    obtain ⟨n,hn⟩ := finiteStage i.1
    let h := (fun u : bigD => (u.val,g u.val z)) '' (i.1 : Set bigD)
    have hf : h.Finite := i.1.finite_toSet.image _
    have hsub : h ⊆ (d n).val ×ˢ Set.univ := by rintro _ ⟨u,hu,rfl⟩; exact ⟨hn u hu,trivial⟩
    let hg : Profiles K bigD := ⟨h,hf,fun _ hp => ⟨subD n (hsub hp).1,trivial⟩⟩
    obtain ⟨y,⟨w,hw,rfl⟩,matchY,lt1,lt2⟩ := approach hg (by rintro _ ⟨_,_,rfl⟩; rfl) i.2.val i.2.property
    obtain ⟨a,hwa,haw⟩ := exists_rat_btwn lt1
    obtain ⟨b,hwb,hbz⟩ := exists_rat_btwn lt2
    have gm : Good s g J (d n).val w := { hw with agree := fun u hu => hw.agree u (subD n hu) }
    obtain ⟨v,hv,av,vb,mv⟩ := cover _ ⟨h,hf,hsub⟩ a b ⟨w,gm,haw,hwb,matchY⟩
    have gv := regular (d n) v hv
    refine ⟨v,fun x hx => mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨⟨v,hv⟩,hx⟩⟩,
      fun x hx => mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨⟨v,hv⟩,hx⟩⟩,
      ⟨hwa.trans av,vb.trans hbz⟩,fun u hu => (gv.agree u.val (hn u hu)).trans (mv _ ⟨u,hu,rfl⟩),
      { gv with agree := fun _ h => h.elim }⟩
  choose w ws we wz wag wg using existsNear
  let iz : ↥(Iio z) := ⟨z-1,by change z-1 < z; linarith⟩
  have : Nonempty ↥(Iio z) := ⟨iz⟩
  obtain ⟨V,hV⟩ := Ultrafilter.exists_le (atTop : Filter IX)
  let F := V.bind fun i => (w i).F
  have supported : support ∈ F := Eventually.of_forall (f := (V : Filter IX)) fun i => mem_of_superset (wg i).memC (ws i)
  have strict (a : ℝ) (ha : a < z) : Ioo a z ∈ F := by
    have later : ∀ᶠ i : IX in V, ((∅,⟨a,ha⟩) : IX) ≤ i := hV (eventually_ge_atTop _)
    exact later.mono fun i hi => (wg i).conv a z (lt_of_le_of_lt hi.2 (wz i).1) (wz i).2
  have agree (u : ℝ) (hu : u ∈ bigD) : pickColor F (g u) = g u z := by
    apply pick_eq
    let v : bigD := ⟨u,hu⟩
    have later : ∀ᶠ i : IX in V, (({v},iz) : IX) ≤ i := hV (eventually_ge_atTop _)
    exact later.mono fun i hi => wag i v (hi.1 (Finset.mem_singleton_self _)) ▸ pickSpec (w i).F (g u)
  let val (y : ℝ) := pickColor F (fun x => g x y)
  have goodVal (y : ℝ) (hy : y ∈ s) (outside : y ∉ allE) : val y ∉ J := by
    have ev : ∀ᶠ x in F, g x y ∉ J := Eventually.of_forall (f := (V : Filter IX)) fun i =>
      (pickSpec (w i).F (fun x => g x y)).mono (fun x hx => hx ▸ (wg i).clean y hy (fun h => outside (we i h)))
    obtain ⟨_,hx,eq⟩ := (ev.and (pickSpec F (fun x => g x y))).exists
    exact fun h => hx (eq.symm ▸ h : g _ y ∈ J)
  let j := pickColor F (fun x => pickColor F (g x))
  have eq : j = val z := by
    apply pick_eq
    filter_upwards [supported,pickSpec F (fun x => g x z)] with u hu hc
    exact (agree u (suppD hu)).trans hc
  let loss := {y ∈ s | val y = j}
  have countLoss : loss.Countable := small F support countSupp supported suppS z strict
  refine ⟨j,eq ▸ goodVal z good.point outAll,⟨z,F,support,loss ∪ allE⟩,?_,outE⟩
  refine ⟨good.point,countSupp,supported,suppS,fun a b ha hb => mem_of_superset (strict a ha)
    (fun _ h => ⟨h.1,h.2.trans hb⟩),fun u hu => agree u (d0 hu),countLoss.union counts,?_⟩
  intro y hy hout
  simpa only [Finset.mem_insert,not_or] using And.intro (fun he => hout (Or.inl ⟨hy,he⟩))
    (goodVal y hy (fun he => hout (Or.inr he)))

/-- The finite-color pair theorem on uncountable real sets at order type ω·2.
Among the sets of excludable colors take one with the fewest remaining colors.
A countable list of failed tests for every possible next color can be tested together. -/
private theorem realArrowProof : RealArrow := by
  classical
  intro K _ _ s hs g sym
  let _ := Fintype.ofFinite K
  obtain ⟨S,sub,hS,rich⟩ := stableSet g s hs
  by_contra! no
  have none (c : K) : ¬Two S g c := by
    rintro ⟨l,u,sep,mem,edges⟩
    exact no c ⟨l,u,sep,mem.trans sub,edges⟩
  have base : Possible S g ∅ := by
    intro D E _ hE
    obtain ⟨z,hz,he⟩ : (S \ E).Nonempty := by
      by_contra! h
      exact hS (hE.mono (Set.sdiff_eq_empty.mp h))
    refine ⟨⟨z,pure z,{z},∅⟩,?_,he⟩
    exact ⟨hz,countable_singleton _,by simp,singleton_subset_iff.mpr hz,
      fun _ _ ha hb => by simpa using And.intro ha hb,
      fun _ _ => pick_eq (by simp),countable_empty,by simp⟩
  let P (n : ℕ) := ∃ J : Finset K, Possible S g J ∧ (Finset.univ \ J).card = n
  have ex : ∃ n, P n := ⟨_,∅,base,rfl⟩
  obtain ⟨J,poss,eq⟩ := Nat.find_spec ex
  have fail (j : K) (hj : j ∉ J) : ¬Possible S g (insert j J) := by
    intro more
    have min := Nat.find_min' ex ⟨_,more,rfl⟩
    rw [← eq] at min
    apply min.not_gt
    apply Finset.card_lt_card
    exact Finset.ssubset_iff_of_subset (Finset.sdiff_subset_sdiff_right _ (Finset.subset_insert _ _)) |>.mpr
      ⟨j,by simp [hj],by simp⟩
  let New := {j : K // j ∉ J}
  have fails (j : New) := fail j.val j.property
  unfold Possible at fails
  push Not at fails
  choose D E hd he obstruction using fails
  let d := ⋃ j, D j
  let e := ⋃ j, E j
  obtain ⟨j,hj,w,good,out⟩ := mergeGerms S g J poss (filterSmall S g sym none rich)
    d e (countable_iUnion hd) (countable_iUnion he)
  let k : New := ⟨j,hj⟩
  have test : Good S g (insert j J) (D k) w :=
    {good with agree := fun u hu => good.agree u (mem_iUnion.mpr ⟨k,hu⟩)}
  exact out (mem_iUnion.mpr ⟨k,obstruction k w test⟩)

theorem binaryTheorem : BinaryWithExceptions := realBinary realArrowProof

/-- The sparse case of G1's argument forces all eight assignment patterns on one sequence
of stages. In the other case the interleaved construction already produced the rows. -/
theorem mixedOfBinary (binary : BinaryWithExceptions) (r : ℝ → ℝ → ℝ → Prop)
    (sym : ∀ x y z, x ≠ y → y ≠ z → x ≠ z → (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y))
    (hb : ¬ ∃ s : Set ℝ, #s = 4 ∧ s.Triplewise (fun x y z => ¬ r x y z)) :
    ∃ a b : ℕ ↪o ℝ, (∀ i j, a i < b j) ∧ (∀ i j k, i < j → r (a i) (a j) (b k)) ∧
      (∀ i j k, j < k → r (a i) (b j) (b k)) := by
  by_contra noRows
  obtain ⟨B,inc,sep,ord,blue⟩ := growingBlocks r (chooseBlock binary r sym hb noRows)
  exact noRows (rowsOfGrowing r sym hb B inc sep ord blue)

theorem fromBinary (binary : BinaryWithExceptions) : type_of% @Erdos70.erdos_70.variants.omega_times_two_four := by
  intro r sym
  by_cases blue : ∃ s : Set ℝ, #s = 4 ∧ s.Triplewise (fun x y z => ¬ r x y z)
  · exact Or.inr blue
  · exact Or.inl (redOfMixed r sym blue (mixedOfBinary binary r sym blue))

/-- The exact R2 selection obligation, with its three supplied antecedents. -/
theorem roundTwoSelection :
  ∀ (r : ℝ → ℝ → ℝ → Prop),
    (∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y)) →
    (¬ ∃ s : Set ℝ, #s = 4 ∧ s.Triplewise (fun x y z => ¬ r x y z)) →
    (∀ (U : Ultrafilter ℝ) (s : Set ℝ),
      {x ∈ s | {y ∈ s | x < y ∧ ∀ᶠ w in U, r w x y}.Countable}.Countable) →
    (∀ (a : ℕ ↪o ℝ) (s : Set ℝ), ¬s.Countable → ∃ e : ℕ ↪o ℕ, ∃ b : ℕ ↪o ℝ,
      (∀ i, b i ∈ s) ∧ ∀ i j k, j < k → k ≤ i → r (a (e i)) (b j) (b k)) →
    (∀ (b : ℕ ↪o ℝ) (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ atTop → ∀ s : Set ℝ,
      ¬s.Countable → (∀ x ∈ s, x < b 0) →
      (∃ a : ℕ ↪o ℝ, ∃ e : ℕ ↪o ℕ, (∀ i, a i ∈ s) ∧ ∀ i j k, i < j → j < k →
        r (a i) (a j) (b (e k)) ∧ r (a i) (b (e j)) (b (e k))) ∨
      (∃ t ⊆ s, ¬t.Countable ∧ (s \ t).Countable ∧
        t.Pairwise (fun x y => ∀ᶠ n in U, r x y (b n)))) →
    ∃ a b : ℕ ↪o ℝ, (∀ i j, a i < b j) ∧
      (∀ i j k, j < k → k ≤ i → r (a i) (b j) (b k)) ∧
      ∀ c : Fin 5, ∀ f : ℕ ↪o ℕ, ∃ i j k, i < j ∧ j < k ∧
        ![r (a (f i)) (a (f j)) (b (f k)), r (a (f i)) (a (f k)) (b (f j)),
          r (a (f j)) (a (f k)) (b (f i)), r (a (f i)) (b (f j)) (b (f k)),
          r (a (f j)) (b (f i)) (b (f k))] c := by
  intro r sym hb _ _ _
  obtain ⟨a,b,sep,hp,hq⟩ := mixedOfBinary binaryTheorem r sym hb
  refine ⟨a,b,sep,fun i j k hjk _ => hq i j k hjk,?_⟩
  intro c f
  refine ⟨0,1,2,by decide,by decide,?_⟩
  have h01 := f.strictMono (by decide : 0 < 1)
  have h02 := f.strictMono (by decide : 0 < 2)
  have h12 := f.strictMono (by decide : 1 < 2)
  fin_cases c
  · exact hp _ _ _ h01
  · exact hp _ _ _ h02
  · exact hp _ _ _ h12
  · exact hq _ _ _ h12
  · exact hq _ _ _ h02

end OMA.Erdos70Rows

theorem OMA.solution : type_of% @Erdos70.erdos_70.variants.omega_times_two_four :=
  OMA.Erdos70Rows.fromBinary OMA.Erdos70Rows.binaryTheorem
