import OMAStatements.S_oeis_a223228

namespace OMA.S_oeis_a223228

open PowerSeries Finset





/-- The adjacency matrix packed into one number: bit 12 x + y is set when x ~ y. -/
def adjB (x y : Fin 12) : Prop := Nat.testBit 10805476240743161716340406575141537830555710
  (12 * x.val + y.val) = true

instance : DecidableRel adjB := fun x y => by unfold adjB; infer_instance

lemma adj_iff_B (x y : Fin 12) : adj x y ↔ adjB x y := by
  revert x y
  decide

/-- A row. -/
abbrev S := Fin 12 × Fin 12 × Fin 12

/-- A row is allowed when its horizontal moves are edges. -/
def rowOK (s : S) : Prop := adjB s.1 s.2.1 ∧ adjB s.2.1 s.2.2

/-- Row t may follow row s: the diagonal and antidiagonal moves are edges. -/
def step (s t : S) : Prop := adjB s.1 t.2.1 ∧ adjB s.2.1 t.2.2 ∧ adjB s.2.1 t.1 ∧ adjB s.2.2 t.2.1

instance : DecidablePred rowOK := fun s => by unfold rowOK; infer_instance

instance : DecidableRel step := fun s t => by unfold step; infer_instance

/-- A valid sequence of rows. -/
def Valid {n : ℕ} (g : Fin n → S) : Prop :=
  (∀ i, rowOK (g i)) ∧ ∀ i i' : Fin n, i'.val = i.val + 1 → step (g i) (g i')

instance {n : ℕ} : DecidablePred (@Valid n) := fun g => by unfold Valid; infer_instance

lemma a_eq (n : ℕ) : a n = ((univ : Finset (Fin n → S)).filter
    (fun g => (∀ i : Fin n, i.val = 0 → (g i).1 = 0) ∧ Valid g)).card := by
  unfold a
  apply Finset.card_bij (fun f _ => fun i => ((f i 0, f i 1, f i 2) : S))
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    obtain ⟨h0, h1, h2⟩ := hf
    simp only [adj_iff_B] at h1 h2
    refine ⟨fun i hi => h0 i hi, fun i => ⟨h1 i 0 1 rfl, h1 i 1 2 rfl⟩, fun i i' hii =>
      ⟨(h2 i i' hii 0 1 rfl).1, (h2 i i' hii 1 2 rfl).1, (h2 i i' hii 0 1 rfl).2,
        (h2 i i' hii 1 2 rfl).2⟩⟩
  · intro f _ f' _ hff
    funext i j
    have := congrFun hff i
    simp only [Prod.mk.injEq] at this
    fin_cases j
    · exact this.1
    · exact this.2.1
    · exact this.2.2
  · intro g hg
    refine ⟨fun i j => ![(g i).1, (g i).2.1, (g i).2.2] j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      obtain ⟨h0, hr, hs⟩ := hg
      simp only [adj_iff_B]
      refine ⟨fun i hi => by simpa using h0 i hi, fun i j j' hjj => ?_, fun i i' hii j j' hjj => ?_⟩
      · obtain ⟨r1, r2⟩ := hr i
        fin_cases j <;> fin_cases j'
        all_goals first
          | exact absurd hjj (by decide)
          | simpa using r1
          | simpa using r2
      · obtain ⟨s1, s2, s3, s4⟩ := hs i i' hii
        fin_cases j <;> fin_cases j'
        all_goals first
          | exact absurd hjj (by decide)
          | exact ⟨by simpa using s1, by simpa using s3⟩
          | exact ⟨by simpa using s2, by simpa using s4⟩
    · funext i
      simp

/-- W(n, s): valid sequences of n + 1 rows whose first row is s. -/
def W (n : ℕ) (s : S) : ℕ :=
  ((univ : Finset (Fin (n + 1) → S)).filter (fun g => Valid g ∧ g 0 = s)).card

lemma valid_cons {n : ℕ} (s : S) (g : Fin (n + 1) → S) :
    Valid (Fin.cons s g : Fin (n + 2) → S) ↔ rowOK s ∧ step s (g 0) ∧ Valid g := by
  constructor
  · rintro ⟨hr, h⟩
    refine ⟨by simpa using hr 0, ?_, fun i => by simpa using hr i.succ, ?_⟩
    · have := h 0 1 (by simp)
      simpa using this
    · intro i j hij
      have := h i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨hs, h0, hr, hg⟩
    refine ⟨?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hs
      | succ i => simpa using hr i
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        have hj : j = 0 := by ext; simp at hij; omega
        subst hj
        simpa using h0
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        simp only [Fin.cons_succ]
        exact hg i j (by simp at hij; omega)

lemma a_sum (n : ℕ) : a (n + 1) = ∑ s ∈ (univ : Finset S).filter (fun s => s.1 = 0), W n s := by
  rw [a_eq]
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0)
    (t := (univ : Finset S).filter (fun s => s.1 = 0))]
  · refine Finset.sum_congr rfl (fun s hs => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hv⟩, h0⟩
      exact ⟨hv, h0⟩
    · rintro ⟨hv, h0⟩
      refine ⟨⟨fun j hj => ?_, hv⟩, h0⟩
      have : j = 0 := Fin.ext hj
      rw [this, h0, hs]
  · intro g hg
    rw [Finset.mem_coe, Finset.mem_filter] at hg
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hg.2.1 0 rfl⟩

lemma W_zero (s : S) : W 0 s = if rowOK s then 1 else 0 := by
  unfold W
  split_ifs with hs
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => s, ?_⟩
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hg⟩
      funext i
      rw [Fin.fin_one_eq_zero i, hg]
    · rintro rfl
      refine ⟨⟨fun _ => hs, ?_⟩, rfl⟩
      intro i j hij
      have := j.isLt
      omega
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hr, _⟩, h0⟩
    exact hs (h0 ▸ hr 0)

/-- Prepending the row s. -/
def consEmb (n : ℕ) (s : S) : (Fin (n + 1) → S) ↪ (Fin (n + 2) → S) where
  toFun g := Fin.cons s g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (s : S) (g : Fin (n + 1) → S) :
    consEmb n s g = Fin.cons s g := rfl

lemma W_succ (n : ℕ) (s : S) :
    W (n + 1) s = if rowOK s then ∑ t : S, (if step s t then W n t else 0) else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → S)).filter (fun g => Valid g ∧ g 0 = s)) =
      (((univ : Finset (Fin (n + 1) → S)).filter
        (fun g => rowOK s ∧ step s (g 0) ∧ Valid g)).map (consEmb n s)) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, h0⟩
      refine ⟨Fin.tail g, ?_, ?_⟩
      · have hg : g = Fin.cons s (Fin.tail g) := by
          rw [← h0]; exact (Fin.cons_self_tail g).symm
        rw [hg, valid_cons] at hv
        exact hv
      · rw [← h0]; exact Fin.cons_self_tail g
    · rintro ⟨g', hg', rfl⟩
      exact ⟨(valid_cons s g').2 hg', by simp⟩
  unfold W
  rw [e, Finset.card_map]
  split_ifs with hs
  · rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    split_ifs with hst
    · congr 1
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, _, hg⟩, h0⟩
        exact ⟨hg, h0⟩
      · rintro ⟨hg, h0⟩
        exact ⟨⟨hs, h0 ▸ hst, hg⟩, h0⟩
    · rw [Finset.card_eq_zero]
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨⟨_, hst', _⟩, h0⟩
      exact hst (h0 ▸ hst')
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨hs', _⟩
    exact hs hs'

lemma W_not_ok (n : ℕ) (s : S) (hs : ¬ rowOK s) : W n s = 0 := by
  cases n with
  | zero => rw [W_zero, if_neg hs]
  | succ n => rw [W_succ, if_neg hs]

/-- The five neighbours of each vertex, packed as base-12 digits: digit 5 v + k is the k-th
neighbour of v. -/
def nbr (v : Fin 12) (k : Fin 5) : Fin 12 :=
  ⟨50759452627860224136420571413071009518555949165100666725763158473 / 12 ^ (5 * v.val + k.val) %
    12, Nat.mod_lt _ (by norm_num)⟩

lemma adj_iff (u v : Fin 12) : adjB u v ↔ ∃ k, nbr u k = v := by
  revert u v
  decide

lemma nbr_inj (u : Fin 12) (k k' : Fin 5) (h : nbr u k = nbr u k') : k = k' := by
  revert u k k'
  decide

/-- The candidate successors of a row s: x' a neighbour of y, y' of x', z' of y'. -/
def nb3 (s : S) (b : Fin 5 × Fin 5 × Fin 5) : S :=
  (nbr s.2.1 b.1, nbr (nbr s.2.1 b.1) b.2.1, nbr (nbr (nbr s.2.1 b.1) b.2.1) b.2.2)

/-- The remaining conditions on a candidate. -/
def rest (s t : S) : Prop := adjB s.1 t.2.1 ∧ adjB s.2.1 t.2.2 ∧ adjB s.2.2 t.2.1

instance : DecidableRel rest := fun s t => by unfold rest; infer_instance

lemma nb3_inj (s : S) {b b' : Fin 5 × Fin 5 × Fin 5} (h : nb3 s b = nb3 s b') : b = b' := by
  simp only [nb3, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e1 := nbr_inj _ _ _ h1
  rw [e1] at h2 h3
  have e2 := nbr_inj _ _ _ h2
  rw [e2] at h3
  have e3 := nbr_inj _ _ _ h3
  exact Prod.ext e1 (Prod.ext e2 e3)

lemma step_ok_iff (s t : S) : (step s t ∧ rowOK t) ↔ (∃ b, nb3 s b = t) ∧ rest s t := by
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
    obtain ⟨k1, hk1⟩ := (adj_iff _ _).1 h3
    obtain ⟨k2, hk2⟩ := (adj_iff _ _).1 h5
    obtain ⟨k3, hk3⟩ := (adj_iff _ _).1 h6
    refine ⟨⟨(k1, k2, k3), ?_⟩, h1, h2, h4⟩
    simp only [nb3]
    rw [hk1, hk2, hk3]
  · rintro ⟨⟨b, rfl⟩, h1, h2, h4⟩
    exact ⟨⟨h1, h2, (adj_iff _ _).2 ⟨b.1, rfl⟩, h4⟩, (adj_iff _ _).2 ⟨b.2.1, rfl⟩,
      (adj_iff _ _).2 ⟨b.2.2, rfl⟩⟩

lemma W_succ' (n : ℕ) (s : S) :
    W (n + 1) s = if rowOK s then ∑ b : Fin 5 × Fin 5 × Fin 5,
      (if rest s (nb3 s b) then W n (nb3 s b) else 0) else 0 := by
  rw [W_succ]
  split_ifs with hs
  · have e0 : ∑ t : S, (if step s t then W n t else 0) =
        ∑ t : S, (if step s t ∧ rowOK t then W n t else 0) := by
      refine Finset.sum_congr rfl (fun t _ => ?_)
      by_cases ht : rowOK t
      · simp [ht]
      · simp [ht, W_not_ok n t ht]
    rw [e0, ← Finset.sum_filter, ← Finset.sum_filter]
    have e : (univ : Finset S).filter (fun t => step s t ∧ rowOK t) =
        ((univ : Finset (Fin 5 × Fin 5 × Fin 5)).filter (fun b => rest s (nb3 s b))).image (nb3 s) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, step_ok_iff]
      constructor
      · rintro ⟨⟨b, rfl⟩, h⟩
        exact ⟨b, h, rfl⟩
      · rintro ⟨b, h, rfl⟩
        exact ⟨⟨b, rfl⟩, h⟩
    rw [e, Finset.sum_image (fun b _ b' _ h => nb3_inj s h)]
  · rfl

/-- Table lookup: entry (x, y, z) of a nested list. -/
def tb (L : List (List (List ℕ))) (s : S) : ℕ := ((L.getD s.1.val []).getD s.2.1.val []).getD s.2.2.val 0

def t1L : List (List (List ℕ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [41, 0, 29, 0, 0, 29, 29, 29, 0, 0, 0, 0], [41, 29, 0, 29, 0, 0, 0, 29, 29, 0, 0, 0], [41, 0, 29, 0, 29, 0, 0, 0, 29, 29, 0, 0], [41, 0, 0, 29, 0, 29, 0, 0, 0, 29, 29, 0], [41, 29, 0, 0, 29, 0, 29, 0, 0, 0, 29, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 41, 29, 29, 29, 29, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [29, 41, 0, 29, 0, 0, 0, 29, 29, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [29, 41, 0, 0, 29, 0, 29, 0, 0, 0, 29, 0], [0, 41, 0, 0, 0, 29, 0, 29, 0, 0, 29, 29], [0, 41, 29, 0, 0, 0, 29, 0, 29, 0, 0, 29], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 29, 41, 29, 29, 29, 0, 0, 0, 0, 0, 0], [29, 0, 41, 0, 0, 29, 29, 29, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [29, 0, 41, 0, 29, 0, 0, 0, 29, 29, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 29, 41, 0, 0, 0, 29, 0, 29, 0, 0, 29], [0, 0, 41, 29, 0, 0, 0, 29, 0, 29, 0, 29], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 29, 29, 41, 29, 29, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [29, 29, 0, 41, 0, 0, 0, 29, 29, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [29, 0, 0, 41, 0, 29, 0, 0, 0, 29, 29, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 29, 41, 0, 0, 0, 29, 0, 29, 0, 29], [0, 0, 0, 41, 29, 0, 0, 0, 29, 0, 29, 29], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 29, 29, 29, 41, 29, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [29, 0, 29, 0, 41, 0, 0, 0, 29, 29, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [29, 29, 0, 0, 41, 0, 29, 0, 0, 0, 29, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 29, 41, 0, 0, 0, 29, 0, 29, 29], [0, 0, 0, 0, 41, 29, 29, 0, 0, 29, 0, 29], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 29, 29, 29, 29, 41, 0, 0, 0, 0, 0, 0], [29, 0, 29, 0, 0, 41, 29, 29, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [29, 0, 0, 29, 0, 41, 0, 0, 0, 29, 29, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 29, 0, 0, 0, 41, 0, 29, 0, 0, 29, 29], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 29, 41, 29, 0, 0, 29, 0, 29], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [29, 0, 29, 0, 0, 29, 41, 29, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [29, 29, 0, 0, 29, 0, 41, 0, 0, 0, 29, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 29, 29, 0, 0, 0, 41, 0, 29, 0, 0, 29], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 29, 29, 41, 0, 0, 29, 0, 29], [0, 0, 0, 0, 0, 0, 41, 29, 29, 29, 29, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [29, 0, 29, 0, 0, 29, 29, 41, 0, 0, 0, 0], [29, 29, 0, 29, 0, 0, 0, 41, 29, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 29, 0, 0, 0, 29, 0, 41, 0, 0, 29, 29], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 29, 29, 0, 0, 0, 41, 0, 29, 0, 29], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 29, 41, 29, 29, 29, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [29, 29, 0, 29, 0, 0, 0, 29, 41, 0, 0, 0], [29, 0, 29, 0, 29, 0, 0, 0, 41, 29, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 29, 29, 0, 0, 0, 29, 0, 41, 0, 0, 29], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 29, 29, 0, 0, 0, 41, 0, 29, 29], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 29, 29, 41, 29, 29, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [29, 0, 29, 0, 29, 0, 0, 0, 29, 41, 0, 0], [29, 0, 0, 29, 0, 29, 0, 0, 0, 41, 29, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 29, 29, 0, 0, 0, 29, 0, 41, 0, 29], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 29, 29, 29, 0, 0, 41, 0, 29], [0, 0, 0, 0, 0, 0, 29, 29, 29, 41, 29, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [29, 0, 0, 29, 0, 29, 0, 0, 0, 29, 41, 0], [29, 29, 0, 0, 29, 0, 29, 0, 0, 0, 41, 0], [0, 29, 0, 0, 0, 29, 0, 29, 0, 0, 41, 29], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 29, 29, 0, 0, 0, 29, 0, 41, 29], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 29, 29, 29, 29, 41, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 29, 0, 0, 0, 29, 0, 29, 0, 0, 29, 41], [0, 29, 29, 0, 0, 0, 29, 0, 29, 0, 0, 41], [0, 0, 29, 29, 0, 0, 0, 29, 0, 29, 0, 41], [0, 0, 0, 29, 29, 0, 0, 0, 29, 0, 29, 41], [0, 0, 0, 0, 29, 29, 29, 0, 0, 29, 0, 41], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]

def t2L : List (List (List ℕ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1345, 0, 925, 0, 0, 925, 925, 925, 0, 0, 0, 0], [1345, 925, 0, 925, 0, 0, 0, 925, 925, 0, 0, 0], [1345, 0, 925, 0, 925, 0, 0, 0, 925, 925, 0, 0], [1345, 0, 0, 925, 0, 925, 0, 0, 0, 925, 925, 0], [1345, 925, 0, 0, 925, 0, 925, 0, 0, 0, 925, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 1345, 925, 925, 925, 925, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [925, 1345, 0, 925, 0, 0, 0, 925, 925, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [925, 1345, 0, 0, 925, 0, 925, 0, 0, 0, 925, 0], [0, 1345, 0, 0, 0, 925, 0, 925, 0, 0, 925, 925], [0, 1345, 925, 0, 0, 0, 925, 0, 925, 0, 0, 925], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 925, 1345, 925, 925, 925, 0, 0, 0, 0, 0, 0], [925, 0, 1345, 0, 0, 925, 925, 925, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [925, 0, 1345, 0, 925, 0, 0, 0, 925, 925, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 925, 1345, 0, 0, 0, 925, 0, 925, 0, 0, 925], [0, 0, 1345, 925, 0, 0, 0, 925, 0, 925, 0, 925], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 925, 925, 1345, 925, 925, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [925, 925, 0, 1345, 0, 0, 0, 925, 925, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [925, 0, 0, 1345, 0, 925, 0, 0, 0, 925, 925, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 925, 1345, 0, 0, 0, 925, 0, 925, 0, 925], [0, 0, 0, 1345, 925, 0, 0, 0, 925, 0, 925, 925], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 925, 925, 925, 1345, 925, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [925, 0, 925, 0, 1345, 0, 0, 0, 925, 925, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [925, 925, 0, 0, 1345, 0, 925, 0, 0, 0, 925, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 925, 1345, 0, 0, 0, 925, 0, 925, 925], [0, 0, 0, 0, 1345, 925, 925, 0, 0, 925, 0, 925], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 925, 925, 925, 925, 1345, 0, 0, 0, 0, 0, 0], [925, 0, 925, 0, 0, 1345, 925, 925, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [925, 0, 0, 925, 0, 1345, 0, 0, 0, 925, 925, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 925, 0, 0, 0, 1345, 0, 925, 0, 0, 925, 925], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 925, 1345, 925, 0, 0, 925, 0, 925], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [925, 0, 925, 0, 0, 925, 1345, 925, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [925, 925, 0, 0, 925, 0, 1345, 0, 0, 0, 925, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 925, 925, 0, 0, 0, 1345, 0, 925, 0, 0, 925], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 925, 925, 1345, 0, 0, 925, 0, 925], [0, 0, 0, 0, 0, 0, 1345, 925, 925, 925, 925, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [925, 0, 925, 0, 0, 925, 925, 1345, 0, 0, 0, 0], [925, 925, 0, 925, 0, 0, 0, 1345, 925, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 925, 0, 0, 0, 925, 0, 1345, 0, 0, 925, 925], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 925, 925, 0, 0, 0, 1345, 0, 925, 0, 925], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 925, 1345, 925, 925, 925, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [925, 925, 0, 925, 0, 0, 0, 925, 1345, 0, 0, 0], [925, 0, 925, 0, 925, 0, 0, 0, 1345, 925, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 925, 925, 0, 0, 0, 925, 0, 1345, 0, 0, 925], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 925, 925, 0, 0, 0, 1345, 0, 925, 925], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 925, 925, 1345, 925, 925, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [925, 0, 925, 0, 925, 0, 0, 0, 925, 1345, 0, 0], [925, 0, 0, 925, 0, 925, 0, 0, 0, 1345, 925, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 925, 925, 0, 0, 0, 925, 0, 1345, 0, 925], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 925, 925, 925, 0, 0, 1345, 0, 925], [0, 0, 0, 0, 0, 0, 925, 925, 925, 1345, 925, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [925, 0, 0, 925, 0, 925, 0, 0, 0, 925, 1345, 0], [925, 925, 0, 0, 925, 0, 925, 0, 0, 0, 1345, 0], [0, 925, 0, 0, 0, 925, 0, 925, 0, 0, 1345, 925], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 925, 925, 0, 0, 0, 925, 0, 1345, 925], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 925, 925, 925, 925, 1345, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 925, 0, 0, 0, 925, 0, 925, 0, 0, 925, 1345], [0, 925, 925, 0, 0, 0, 925, 0, 925, 0, 0, 1345], [0, 0, 925, 925, 0, 0, 0, 925, 0, 925, 0, 1345], [0, 0, 0, 925, 925, 0, 0, 0, 925, 0, 925, 1345], [0, 0, 0, 0, 925, 925, 925, 0, 0, 925, 0, 1345], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]

lemma W1_0 (y z : Fin 12) : W 1 (0, y, z) = tb t1L (0, y, z) := by
  rw [W_succ']; simp only [W_zero]; revert y z; decide +kernel

lemma W1_1 (y z : Fin 12) : W 1 (1, y, z) = tb t1L (1, y, z) := by
  rw [W_succ']; simp only [W_zero]; revert y z; decide +kernel

lemma W1_2 (y z : Fin 12) : W 1 (2, y, z) = tb t1L (2, y, z) := by
  rw [W_succ']; simp only [W_zero]; revert y z; decide +kernel

lemma W1_3 (y z : Fin 12) : W 1 (3, y, z) = tb t1L (3, y, z) := by
  rw [W_succ']; simp only [W_zero]; revert y z; decide +kernel

lemma W1_4 (y z : Fin 12) : W 1 (4, y, z) = tb t1L (4, y, z) := by
  rw [W_succ']; simp only [W_zero]; revert y z; decide +kernel

lemma W1_5 (y z : Fin 12) : W 1 (5, y, z) = tb t1L (5, y, z) := by
  rw [W_succ']; simp only [W_zero]; revert y z; decide +kernel

lemma W1_6 (y z : Fin 12) : W 1 (6, y, z) = tb t1L (6, y, z) := by
  rw [W_succ']; simp only [W_zero]; revert y z; decide +kernel

lemma W1_7 (y z : Fin 12) : W 1 (7, y, z) = tb t1L (7, y, z) := by
  rw [W_succ']; simp only [W_zero]; revert y z; decide +kernel

lemma W1_8 (y z : Fin 12) : W 1 (8, y, z) = tb t1L (8, y, z) := by
  rw [W_succ']; simp only [W_zero]; revert y z; decide +kernel

lemma W1_9 (y z : Fin 12) : W 1 (9, y, z) = tb t1L (9, y, z) := by
  rw [W_succ']; simp only [W_zero]; revert y z; decide +kernel

lemma W1_10 (y z : Fin 12) : W 1 (10, y, z) = tb t1L (10, y, z) := by
  rw [W_succ']; simp only [W_zero]; revert y z; decide +kernel

lemma W1_11 (y z : Fin 12) : W 1 (11, y, z) = tb t1L (11, y, z) := by
  rw [W_succ']; simp only [W_zero]; revert y z; decide +kernel

lemma W1 (s : S) : W 1 s = tb t1L s := by
  obtain ⟨x, y, z⟩ := s
  fin_cases x
  · exact W1_0 y z
  · exact W1_1 y z
  · exact W1_2 y z
  · exact W1_3 y z
  · exact W1_4 y z
  · exact W1_5 y z
  · exact W1_6 y z
  · exact W1_7 y z
  · exact W1_8 y z
  · exact W1_9 y z
  · exact W1_10 y z
  · exact W1_11 y z

lemma W2_0 (y z : Fin 12) : W 2 (0, y, z) = tb t2L (0, y, z) := by
  rw [W_succ']; simp only [W1]; revert y z; decide +kernel

lemma W2_1 (y z : Fin 12) : W 2 (1, y, z) = tb t2L (1, y, z) := by
  rw [W_succ']; simp only [W1]; revert y z; decide +kernel

lemma W2_2 (y z : Fin 12) : W 2 (2, y, z) = tb t2L (2, y, z) := by
  rw [W_succ']; simp only [W1]; revert y z; decide +kernel

lemma W2_3 (y z : Fin 12) : W 2 (3, y, z) = tb t2L (3, y, z) := by
  rw [W_succ']; simp only [W1]; revert y z; decide +kernel

lemma W2_4 (y z : Fin 12) : W 2 (4, y, z) = tb t2L (4, y, z) := by
  rw [W_succ']; simp only [W1]; revert y z; decide +kernel

lemma W2_5 (y z : Fin 12) : W 2 (5, y, z) = tb t2L (5, y, z) := by
  rw [W_succ']; simp only [W1]; revert y z; decide +kernel

lemma W2_6 (y z : Fin 12) : W 2 (6, y, z) = tb t2L (6, y, z) := by
  rw [W_succ']; simp only [W1]; revert y z; decide +kernel

lemma W2_7 (y z : Fin 12) : W 2 (7, y, z) = tb t2L (7, y, z) := by
  rw [W_succ']; simp only [W1]; revert y z; decide +kernel

lemma W2_8 (y z : Fin 12) : W 2 (8, y, z) = tb t2L (8, y, z) := by
  rw [W_succ']; simp only [W1]; revert y z; decide +kernel

lemma W2_9 (y z : Fin 12) : W 2 (9, y, z) = tb t2L (9, y, z) := by
  rw [W_succ']; simp only [W1]; revert y z; decide +kernel

lemma W2_10 (y z : Fin 12) : W 2 (10, y, z) = tb t2L (10, y, z) := by
  rw [W_succ']; simp only [W1]; revert y z; decide +kernel

lemma W2_11 (y z : Fin 12) : W 2 (11, y, z) = tb t2L (11, y, z) := by
  rw [W_succ']; simp only [W1]; revert y z; decide +kernel

lemma W2 (s : S) : W 2 s = tb t2L s := by
  obtain ⟨x, y, z⟩ := s
  fin_cases x
  · exact W2_0 y z
  · exact W2_1 y z
  · exact W2_2 y z
  · exact W2_3 y z
  · exact W2_4 y z
  · exact W2_5 y z
  · exact W2_6 y z
  · exact W2_7 y z
  · exact W2_8 y z
  · exact W2_9 y z
  · exact W2_10 y z
  · exact W2_11 y z

lemma Wrec0 (s : S) : W 2 s + 90 * W 0 s = 35 * W 1 s := by
  rw [W2, W1, W_zero]; revert s; decide +kernel

/-- The per-row relation W(k + 2) + 90 W(k) = 35 W(k + 1). -/
lemma W_rec (k : ℕ) (s : S) : W (k + 2) s + 90 * W k s = 35 * W (k + 1) s := by
  induction k generalizing s with
  | zero => exact Wrec0 s
  | succ k ih =>
    rw [W_succ' (k + 2), W_succ' k, W_succ' (k + 1)]
    split_ifs
    · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      split_ifs
      · exact ih _
      · simp
    · simp

lemma a_rec (m : ℕ) : a (m + 2 + 1) + 90 * a (m + 1) = 35 * a (m + 1 + 1) := by
  rw [a_sum, a_sum, a_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun s _ => W_rec m s)

lemma a1 : a 1 = 25 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_sum]; simp only [W_zero]; decide +kernel

lemma a2 : a 2 = 785 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_sum]; simp only [W1]; decide +kernel

lemma a_rec' (m : ℕ) : (a (m + 3) : ℚ) + 90 * a (m + 1) = 35 * a (m + 2) := by
  have h := a_rec m
  rw [show m + 2 + 1 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl] at h
  exact_mod_cast h

/-- Controls: the entry's data a(1..12). -/
theorem controls : a 1 = 25 ∧ a 2 = 785 ∧ a 3 = 25225 ∧ a 4 = 812225 ∧ a 5 = 26157625 ∧
    a 6 = 842416625 ∧ a 7 = 27130395625 ∧ a 8 = 873746350625 ∧ a 9 = 28139386665625 ∧
    a 10 = 906241361740625 ∧ a 11 = 29185902861015625 ∧ a 12 = 939944877578890625 := by
  have q : ∀ m : ℕ, a (m + 3) + 90 * a (m + 1) = 35 * a (m + 2) := fun m => by
    have h := a_rec m
    rw [show m + 2 + 1 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl] at h
    exact h
  have h3 : a 3 = 25225 := by
    have h := q 0; norm_num [a1, a2] at h; generalize a 3 = x at h ⊢; omega
  have h4 : a 4 = 812225 := by
    have h := q 1; norm_num [a2, h3] at h; generalize a 4 = x at h ⊢; omega
  have h5 : a 5 = 26157625 := by
    have h := q 2; norm_num [h3, h4] at h; generalize a 5 = x at h ⊢; omega
  have h6 : a 6 = 842416625 := by
    have h := q 3; norm_num [h4, h5] at h; generalize a 6 = x at h ⊢; omega
  have h7 : a 7 = 27130395625 := by
    have h := q 4; norm_num [h5, h6] at h; generalize a 7 = x at h ⊢; omega
  have h8 : a 8 = 873746350625 := by
    have h := q 5; norm_num [h6, h7] at h; generalize a 8 = x at h ⊢; omega
  have h9 : a 9 = 28139386665625 := by
    have h := q 6; norm_num [h7, h8] at h; generalize a 9 = x at h ⊢; omega
  have h10 : a 10 = 906241361740625 := by
    have h := q 7; norm_num [h8, h9] at h; generalize a 10 = x at h ⊢; omega
  have h11 : a 11 = 29185902861015625 := by
    have h := q 8; norm_num [h9, h10] at h; generalize a 11 = x at h ⊢; omega
  have h12 : a 12 = 939944877578890625 := by
    have h := q 9; norm_num [h10, h11] at h; generalize a 12 = x at h ⊢; omega
  exact ⟨a1, a2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 5x(5 - 18x)/(1 - 35x + 90x^2). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 35 * X + 90 * X ^ 2) = 5 * X * (5 - 18 * X) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - 35 * X + 90 * X ^ 2) = A - C (35 : ℚ) * (A * X ^ 1) + C (90 : ℚ) * (A * X ^ 2) := by
    rw [show (C (35 : ℚ) : ℚ⟦X⟧) = 35 from map_ofNat C 35,
      show (C (90 : ℚ) : ℚ⟦X⟧) = 90 from map_ofNat C 90]
    ring
  have e2 : (5 : ℚ⟦X⟧) * X * (5 - 18 * X) = C (25 : ℚ) * X ^ 1 - C (90 : ℚ) * X ^ 2 := by
    rw [show (C (25 : ℚ) : ℚ⟦X⟧) = 25 from map_ofNat C 25,
      show (C (90 : ℚ) : ℚ⟦X⟧) = 90 from map_ofNat C 90]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp [a1, a2] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h' := a_rec' m
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
      show ¬ m + 3 = 0 by omega, show ¬ m + 2 = 0 by omega, show ¬ m + 1 = 0 by omega,
      show 1 ≤ m + 3 by omega, show 2 ≤ m + 3 by omega, if_true, if_false]
    linear_combination h'

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
    (2 : ℝ) ^ ((-1 : ℝ) - n) * ((35 - Real.sqrt 865) ^ n * (-15 + Real.sqrt 865) +
      (15 + Real.sqrt 865) * (35 + Real.sqrt 865) ^ n) / Real.sqrt 865 := by
  have s865 : Real.sqrt 865 ^ 2 = 865 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 865 := Real.sqrt_pos.2 (by norm_num)
  have hrp : ∀ n : ℕ, (2 : ℝ) ^ ((-1 : ℝ) - n) * ((35 - Real.sqrt 865) ^ n * (-15 + Real.sqrt 865) +
      (15 + Real.sqrt 865) * (35 + Real.sqrt 865) ^ n) =
      (1 / 2) * (((35 - Real.sqrt 865) / 2) ^ n * (-15 + Real.sqrt 865) +
        (15 + Real.sqrt 865) * ((35 + Real.sqrt 865) / 2) ^ n) := by
    intro n
    rw [Real.rpow_sub (by norm_num), Real.rpow_neg_one, Real.rpow_natCast, div_pow, div_pow]
    have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
  set s := Real.sqrt 865 with hs
  set H : ℕ → ℝ := fun n =>
    (1 / 2) * (((35 - s) / 2) ^ n * (-15 + s) + (15 + s) * ((35 + s) / 2) ^ n) with hH
  have H1 : H 1 = 25 * s := by
    simp only [hH]
    ring
  have H2 : H 2 = 785 * s := by
    simp only [hH]
    linear_combination (s / 4) * s865
  have r1 : ∀ m : ℕ, ((35 - s) / 2) ^ (m + 3) =
      35 * ((35 - s) / 2) ^ (m + 2) - 90 * ((35 - s) / 2) ^ (m + 1) := by
    intro m
    have : ((35 - s) / 2) ^ 2 = 35 * ((35 - s) / 2) - 90 := by
      linear_combination (1 / 4) * s865
    calc ((35 - s) / 2) ^ (m + 3) = ((35 - s) / 2) ^ (m + 1) * ((35 - s) / 2) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  have r2 : ∀ m : ℕ, ((35 + s) / 2) ^ (m + 3) =
      35 * ((35 + s) / 2) ^ (m + 2) - 90 * ((35 + s) / 2) ^ (m + 1) := by
    intro m
    have : ((35 + s) / 2) ^ 2 = 35 * ((35 + s) / 2) - 90 := by
      linear_combination (1 / 4) * s865
    calc ((35 + s) / 2) ^ (m + 3) = ((35 + s) / 2) ^ (m + 1) * ((35 + s) / 2) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  have Hrec : ∀ m, H (m + 3) = 35 * H (m + 2) - 90 * H (m + 1) := by
    intro m
    simp only [hH]
    rw [r1, r2]
    ring
  have key : ∀ m, (a (m + 1) : ℝ) * s = H (m + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases m with _ | _ | m
      · rw [a1, H1]; norm_num
      · rw [a2, H2]; norm_num
      · have h' : (a (m + 3) : ℝ) + 90 * a (m + 1) = 35 * a (m + 2) := by
          have := a_rec' m
          exact_mod_cast this
        have e1 : (a (m + 1) : ℝ) * s = H (m + 1) := ih m (by omega)
        have e2 : (a (m + 2) : ℝ) * s = H (m + 2) := ih (m + 1) (by omega)
        show (a (m + 3) : ℝ) * s = H (m + 3)
        rw [Hrec m, ← e1, ← e2]
        linear_combination s * h'
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [hrp, eq_div_iff hpos.ne', key k]

/-- Both of Barker's conjectures. -/
theorem conjecture : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 35 * X + 90 * X ^ 2) = 5 * X * (5 - 18 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 : ℝ) ^ ((-1 : ℝ) - n) * ((35 - Real.sqrt 865) ^ n * (-15 + Real.sqrt 865) +
        (15 + Real.sqrt 865) * (35 + Real.sqrt 865) ^ n) / Real.sqrt 865 :=
  ⟨gf, closed_form⟩

end OMA.S_oeis_a223228

theorem OMA.solution : type_of% @OMA.S_oeis_a223228.main :=
  OMA.S_oeis_a223228.conjecture
