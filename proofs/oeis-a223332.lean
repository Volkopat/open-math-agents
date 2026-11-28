import OMAStatements.S_oeis_a223332

namespace OMA.S_oeis_a223332

open PowerSeries Finset




/-- A column. -/
abbrev S := Fin 8 × Fin 8 × Fin 8

/-- Column y may follow column x. -/
def step (x y : S) : Prop :=
  adj x.1 y.1 ∧ adj x.2.1 y.2.1 ∧ adj x.2.2 y.2.2 ∧ adj y.1 x.2.1 ∧ adj y.2.1 x.2.2

instance : DecidableRel step := fun x y => by unfold step; infer_instance

/-- A valid sequence of columns. -/
def Valid {n : ℕ} (g : Fin n → S) : Prop :=
  ∀ j j' : Fin n, j'.val = j.val + 1 → step (g j) (g j')

instance {n : ℕ} : DecidablePred (@Valid n) := fun g => by unfold Valid; infer_instance

lemma a_eq (n : ℕ) : a n = ((univ : Finset (Fin n → S)).filter
    (fun g => (∀ j : Fin n, j.val = 0 → (g j).1 = 0) ∧ Valid g)).card := by
  unfold a
  apply Finset.card_bij (fun f _ => fun j => ((f 0 j, f 1 j, f 2 j) : S))
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    obtain ⟨h0, h1, h2⟩ := hf
    refine ⟨fun j hj => h0 j hj, fun j j' hjj => ⟨h1 0 j j' hjj, h1 1 j j' hjj, h1 2 j j' hjj,
      h2 0 1 rfl j j' hjj, h2 1 2 rfl j j' hjj⟩⟩
  · intro f _ f' _ hff
    funext i j
    have := congrFun hff j
    simp only [Prod.mk.injEq] at this
    fin_cases i
    · exact this.1
    · exact this.2.1
    · exact this.2.2
  · intro g hg
    refine ⟨fun i j => ![(g j).1, (g j).2.1, (g j).2.2] i, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      obtain ⟨h0, hv⟩ := hg
      refine ⟨fun j hj => by simpa using h0 j hj, fun i j j' hjj => ?_, fun i i' hii j j' hjj => ?_⟩
      · obtain ⟨s1, s2, s3, _, _⟩ := hv j j' hjj
        fin_cases i
        · simpa using s1
        · simpa using s2
        · simpa using s3
      · obtain ⟨_, _, _, s4, s5⟩ := hv j j' hjj
        fin_cases i <;> fin_cases i'
        all_goals first
          | exact absurd hii (by decide)
          | simpa using s4
          | simpa using s5
    · funext j
      simp

/-- W(n, x): valid sequences of n + 1 columns whose first column is x. -/
def W (n : ℕ) (x : S) : ℕ :=
  ((univ : Finset (Fin (n + 1) → S)).filter (fun g => Valid g ∧ g 0 = x)).card

lemma valid_cons {n : ℕ} (x : S) (g : Fin (n + 1) → S) :
    Valid (Fin.cons x g : Fin (n + 2) → S) ↔ step x (g 0) ∧ Valid g := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 0 1 (by simp)
      simpa using this
    · intro i j hij
      have := h i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨h0, hg⟩ i j hij
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

lemma a_sum (n : ℕ) : a (n + 1) = ∑ x ∈ (univ : Finset S).filter (fun x => x.1 = 0), W n x := by
  rw [a_eq]
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0)
    (t := (univ : Finset S).filter (fun x => x.1 = 0))]
  · refine Finset.sum_congr rfl (fun x hx => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hv⟩, h0⟩
      exact ⟨hv, h0⟩
    · rintro ⟨hv, h0⟩
      refine ⟨⟨fun j hj => ?_, hv⟩, h0⟩
      have : j = 0 := Fin.ext hj
      rw [this, h0, hx]
  · intro g hg
    rw [Finset.mem_coe, Finset.mem_filter] at hg
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hg.2.1 0 rfl⟩

lemma W_zero (x : S) : W 0 x = 1 := by
  unfold W
  rw [Finset.card_eq_one]
  refine ⟨fun _ => x, ?_⟩
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hg⟩
    funext i
    rw [Fin.fin_one_eq_zero i, hg]
  · rintro rfl
    refine ⟨?_, rfl⟩
    intro i j hij
    have := j.isLt
    omega

/-- Prepending the column x. -/
def consEmb (n : ℕ) (x : S) : (Fin (n + 1) → S) ↪ (Fin (n + 2) → S) where
  toFun g := Fin.cons x g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (x : S) (g : Fin (n + 1) → S) :
    consEmb n x g = Fin.cons x g := rfl

lemma W_succ (n : ℕ) (x : S) :
    W (n + 1) x = ∑ y : S, if step x y then W n y else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → S)).filter (fun g => Valid g ∧ g 0 = x)) =
      (((univ : Finset (Fin (n + 1) → S)).filter (fun g => step x (g 0) ∧ Valid g)).map
        (consEmb n x)) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, h0⟩
      refine ⟨Fin.tail g, ?_, ?_⟩
      · have hg : g = Fin.cons x (Fin.tail g) := by
          rw [← h0]; exact (Fin.cons_self_tail g).symm
        rw [hg, valid_cons] at hv
        exact hv
      · rw [← h0]; exact Fin.cons_self_tail g
    · rintro ⟨g', hg', rfl⟩
      exact ⟨(valid_cons x g').2 hg', by simp⟩
  unfold W
  rw [e, Finset.card_map]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  split_ifs with hxy
  · congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hg⟩, h0⟩
      exact ⟨hg, h0⟩
    · rintro ⟨hg, h0⟩
      exact ⟨⟨h0 ▸ hxy, hg⟩, h0⟩
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hst, _⟩, h0⟩
    exact hxy (h0 ▸ hst)

/-- The three cube neighbours of a vertex v: v xor 1, v xor 2, v xor 4. -/
def flip (v : Fin 8) (k : Fin 3) : Fin 8 :=
  ![![1, 2, 4], ![0, 3, 5], ![3, 0, 6], ![2, 1, 7], ![5, 6, 0], ![4, 7, 1], ![7, 4, 2],
    ![6, 5, 3]] v k

lemma adj_iff (u v : Fin 8) : adj u v ↔ ∃ k, flip u k = v := by
  revert u v
  decide

lemma flip_inj (u : Fin 8) (k k' : Fin 3) (h : flip u k = flip u k') : k = k' := by
  revert u k k'
  decide

/-- The candidate successors of a column. -/
def nb (x : S) (b : Fin 3 × Fin 3 × Fin 3) : S := (flip x.1 b.1, flip x.2.1 b.2.1, flip x.2.2 b.2.2)

/-- The antidiagonal part of a step. -/
def anti (x y : S) : Prop := adj y.1 x.2.1 ∧ adj y.2.1 x.2.2

instance : DecidableRel anti := fun x y => by unfold anti; infer_instance

lemma nb_inj (x : S) {b b' : Fin 3 × Fin 3 × Fin 3} (h : nb x b = nb x b') : b = b' := by
  simp only [nb, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact Prod.ext (flip_inj _ _ _ h1) (Prod.ext (flip_inj _ _ _ h2) (flip_inj _ _ _ h3))

lemma step_iff (x y : S) : step x y ↔ (∃ b, nb x b = y) ∧ anti x y := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨k1, hk1⟩ := (adj_iff _ _).1 h1
    obtain ⟨k2, hk2⟩ := (adj_iff _ _).1 h2
    obtain ⟨k3, hk3⟩ := (adj_iff _ _).1 h3
    exact ⟨⟨(k1, k2, k3), by simp [nb, hk1, hk2, hk3]⟩, h4, h5⟩
  · rintro ⟨⟨b, rfl⟩, h4, h5⟩
    exact ⟨(adj_iff _ _).2 ⟨b.1, rfl⟩, (adj_iff _ _).2 ⟨b.2.1, rfl⟩,
      (adj_iff _ _).2 ⟨b.2.2, rfl⟩, h4, h5⟩

lemma W_succ' (n : ℕ) (x : S) :
    W (n + 1) x = ∑ b : Fin 3 × Fin 3 × Fin 3, if anti x (nb x b) then W n (nb x b) else 0 := by
  rw [W_succ, ← Finset.sum_filter, ← Finset.sum_filter]
  have e : (univ : Finset S).filter (fun y => step x y) =
      ((univ : Finset (Fin 3 × Fin 3 × Fin 3)).filter (fun b => anti x (nb x b))).image (nb x) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, step_iff]
    constructor
    · rintro ⟨⟨b, rfl⟩, h⟩
      exact ⟨b, h, rfl⟩
    · rintro ⟨b, h, rfl⟩
      exact ⟨⟨b, rfl⟩, h⟩
  rw [e, Finset.sum_image (fun b _ b' _ h => nb_inj x h)]

/-- Table lookup: entry (x0, x1, x2) of a nested list. -/
def tb (L : List (List (List ℕ))) (x : S) : ℕ := ((L.getD x.1.val []).getD x.2.1.val []).getD x.2.2.val 0

def t1L : List (List (List ℕ)) :=
  [[[27, 0, 0, 18, 0, 18, 18, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [12, 0, 0, 18, 0, 12, 12, 0], [0, 0, 0, 0, 0, 0, 0, 0], [12, 0, 0, 12, 0, 18, 12, 0], [12, 0, 0, 12, 0, 12, 18, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 27, 18, 0, 18, 0, 0, 18], [0, 12, 18, 0, 12, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0], [0, 12, 12, 0, 18, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 12, 12, 0, 12, 0, 0, 18]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 18, 12, 0, 12, 0, 0, 12], [0, 18, 27, 0, 18, 0, 0, 18], [0, 0, 0, 0, 0, 0, 0, 0], [0, 12, 12, 0, 18, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 12, 12, 0, 12, 0, 0, 18]],
    [[18, 0, 0, 12, 0, 12, 12, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [18, 0, 0, 27, 0, 18, 18, 0], [0, 0, 0, 0, 0, 0, 0, 0], [12, 0, 0, 12, 0, 18, 12, 0], [12, 0, 0, 12, 0, 12, 18, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 18, 12, 0, 12, 0, 0, 12], [0, 12, 18, 0, 12, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0], [0, 18, 18, 0, 27, 0, 0, 18], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 12, 12, 0, 12, 0, 0, 18]],
    [[18, 0, 0, 12, 0, 12, 12, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [12, 0, 0, 18, 0, 12, 12, 0], [0, 0, 0, 0, 0, 0, 0, 0], [18, 0, 0, 18, 0, 27, 18, 0], [12, 0, 0, 12, 0, 12, 18, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[18, 0, 0, 12, 0, 12, 12, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [12, 0, 0, 18, 0, 12, 12, 0], [0, 0, 0, 0, 0, 0, 0, 0], [12, 0, 0, 12, 0, 18, 12, 0], [18, 0, 0, 18, 0, 18, 27, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 18, 12, 0, 12, 0, 0, 12], [0, 12, 18, 0, 12, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0], [0, 12, 12, 0, 18, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 18, 18, 0, 18, 0, 0, 27]]]

def t2L : List (List (List ℕ)) :=
  [[[441, 0, 0, 294, 0, 294, 294, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [210, 0, 0, 294, 0, 189, 189, 0], [0, 0, 0, 0, 0, 0, 0, 0], [210, 0, 0, 189, 0, 294, 189, 0], [210, 0, 0, 189, 0, 189, 294, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 441, 294, 0, 294, 0, 0, 294], [0, 210, 294, 0, 189, 0, 0, 189], [0, 0, 0, 0, 0, 0, 0, 0], [0, 210, 189, 0, 294, 0, 0, 189], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 210, 189, 0, 189, 0, 0, 294]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 294, 210, 0, 189, 0, 0, 189], [0, 294, 441, 0, 294, 0, 0, 294], [0, 0, 0, 0, 0, 0, 0, 0], [0, 189, 210, 0, 294, 0, 0, 189], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 189, 210, 0, 189, 0, 0, 294]],
    [[294, 0, 0, 210, 0, 189, 189, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [294, 0, 0, 441, 0, 294, 294, 0], [0, 0, 0, 0, 0, 0, 0, 0], [189, 0, 0, 210, 0, 294, 189, 0], [189, 0, 0, 210, 0, 189, 294, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 294, 189, 0, 210, 0, 0, 189], [0, 189, 294, 0, 210, 0, 0, 189], [0, 0, 0, 0, 0, 0, 0, 0], [0, 294, 294, 0, 441, 0, 0, 294], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 189, 189, 0, 210, 0, 0, 294]],
    [[294, 0, 0, 189, 0, 210, 189, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [189, 0, 0, 294, 0, 210, 189, 0], [0, 0, 0, 0, 0, 0, 0, 0], [294, 0, 0, 294, 0, 441, 294, 0], [189, 0, 0, 189, 0, 210, 294, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[294, 0, 0, 189, 0, 189, 210, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [189, 0, 0, 294, 0, 189, 210, 0], [0, 0, 0, 0, 0, 0, 0, 0], [189, 0, 0, 189, 0, 294, 210, 0], [294, 0, 0, 294, 0, 294, 441, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 294, 189, 0, 189, 0, 0, 210], [0, 189, 294, 0, 189, 0, 0, 210], [0, 0, 0, 0, 0, 0, 0, 0], [0, 189, 189, 0, 294, 0, 0, 210], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 294, 294, 0, 294, 0, 0, 441]]]

def t3L : List (List (List ℕ)) :=
  [[[7245, 0, 0, 4788, 0, 4788, 4788, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [3444, 0, 0, 4830, 0, 3066, 3066, 0], [0, 0, 0, 0, 0, 0, 0, 0], [3444, 0, 0, 3066, 0, 4830, 3066, 0], [3444, 0, 0, 3066, 0, 3066, 4830, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 7245, 4788, 0, 4788, 0, 0, 4788], [0, 3444, 4830, 0, 3066, 0, 0, 3066], [0, 0, 0, 0, 0, 0, 0, 0], [0, 3444, 3066, 0, 4830, 0, 0, 3066], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 3444, 3066, 0, 3066, 0, 0, 4830]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 4830, 3444, 0, 3066, 0, 0, 3066], [0, 4788, 7245, 0, 4788, 0, 0, 4788], [0, 0, 0, 0, 0, 0, 0, 0], [0, 3066, 3444, 0, 4830, 0, 0, 3066], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 3066, 3444, 0, 3066, 0, 0, 4830]],
    [[4830, 0, 0, 3444, 0, 3066, 3066, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [4788, 0, 0, 7245, 0, 4788, 4788, 0], [0, 0, 0, 0, 0, 0, 0, 0], [3066, 0, 0, 3444, 0, 4830, 3066, 0], [3066, 0, 0, 3444, 0, 3066, 4830, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 4830, 3066, 0, 3444, 0, 0, 3066], [0, 3066, 4830, 0, 3444, 0, 0, 3066], [0, 0, 0, 0, 0, 0, 0, 0], [0, 4788, 4788, 0, 7245, 0, 0, 4788], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 3066, 3066, 0, 3444, 0, 0, 4830]],
    [[4830, 0, 0, 3066, 0, 3444, 3066, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [3066, 0, 0, 4830, 0, 3444, 3066, 0], [0, 0, 0, 0, 0, 0, 0, 0], [4788, 0, 0, 4788, 0, 7245, 4788, 0], [3066, 0, 0, 3066, 0, 3444, 4830, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[4830, 0, 0, 3066, 0, 3066, 3444, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [3066, 0, 0, 4830, 0, 3066, 3444, 0], [0, 0, 0, 0, 0, 0, 0, 0], [3066, 0, 0, 3066, 0, 4830, 3444, 0], [4788, 0, 0, 4788, 0, 4788, 7245, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 4830, 3066, 0, 3066, 0, 0, 3444], [0, 3066, 4830, 0, 3066, 0, 0, 3444], [0, 0, 0, 0, 0, 0, 0, 0], [0, 3066, 3066, 0, 4830, 0, 0, 3444], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 4788, 4788, 0, 4788, 0, 0, 7245]]]

def t4L : List (List (List ℕ)) :=
  [[[118503, 0, 0, 78246, 0, 78246, 78246, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [56322, 0, 0, 79002, 0, 50085, 50085, 0], [0, 0, 0, 0, 0, 0, 0, 0], [56322, 0, 0, 50085, 0, 79002, 50085, 0], [56322, 0, 0, 50085, 0, 50085, 79002, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 118503, 78246, 0, 78246, 0, 0, 78246], [0, 56322, 79002, 0, 50085, 0, 0, 50085], [0, 0, 0, 0, 0, 0, 0, 0], [0, 56322, 50085, 0, 79002, 0, 0, 50085], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 56322, 50085, 0, 50085, 0, 0, 79002]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 79002, 56322, 0, 50085, 0, 0, 50085], [0, 78246, 118503, 0, 78246, 0, 0, 78246], [0, 0, 0, 0, 0, 0, 0, 0], [0, 50085, 56322, 0, 79002, 0, 0, 50085], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 50085, 56322, 0, 50085, 0, 0, 79002]],
    [[79002, 0, 0, 56322, 0, 50085, 50085, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [78246, 0, 0, 118503, 0, 78246, 78246, 0], [0, 0, 0, 0, 0, 0, 0, 0], [50085, 0, 0, 56322, 0, 79002, 50085, 0], [50085, 0, 0, 56322, 0, 50085, 79002, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 79002, 50085, 0, 56322, 0, 0, 50085], [0, 50085, 79002, 0, 56322, 0, 0, 50085], [0, 0, 0, 0, 0, 0, 0, 0], [0, 78246, 78246, 0, 118503, 0, 0, 78246], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 50085, 50085, 0, 56322, 0, 0, 79002]],
    [[79002, 0, 0, 50085, 0, 56322, 50085, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [50085, 0, 0, 79002, 0, 56322, 50085, 0], [0, 0, 0, 0, 0, 0, 0, 0], [78246, 0, 0, 78246, 0, 118503, 78246, 0], [50085, 0, 0, 50085, 0, 56322, 79002, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[79002, 0, 0, 50085, 0, 50085, 56322, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [50085, 0, 0, 79002, 0, 50085, 56322, 0], [0, 0, 0, 0, 0, 0, 0, 0], [50085, 0, 0, 50085, 0, 79002, 56322, 0], [78246, 0, 0, 78246, 0, 78246, 118503, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0], [0, 79002, 50085, 0, 50085, 0, 0, 56322], [0, 50085, 79002, 0, 50085, 0, 0, 56322], [0, 0, 0, 0, 0, 0, 0, 0], [0, 50085, 50085, 0, 79002, 0, 0, 56322], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 78246, 78246, 0, 78246, 0, 0, 118503]]]

lemma W1 (x : S) : W 1 x = tb t1L x := by
  rw [W_succ']; simp only [W_zero]; revert x; decide +kernel

lemma W2 (x : S) : W 2 x = tb t2L x := by
  rw [W_succ']; simp only [W1]; revert x; decide +kernel

lemma W3 (x : S) : W 3 x = tb t3L x := by
  rw [W_succ']; simp only [W2]; revert x; decide +kernel

lemma W4 (x : S) : W 4 x = tb t4L x := by
  rw [W_succ']; simp only [W3]; revert x; decide +kernel

/-- The per-column relation W(k + 4) + 27 W(k + 2) = 18 W(k + 3). -/
lemma W_rec (k : ℕ) (x : S) : W (k + 4) x + 27 * W (k + 2) x = 18 * W (k + 3) x := by
  induction k generalizing x with
  | zero =>
    rw [W4, W2, W3]
    revert x
    decide +kernel
  | succ k ih =>
    rw [W_succ' (k + 4), W_succ' (k + 2), W_succ' (k + 3)]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    split_ifs
    · exact ih _
    · simp

lemma a_rec (m : ℕ) : a (m + 4 + 1) + 27 * a (m + 2 + 1) = 18 * a (m + 3 + 1) := by
  rw [a_sum, a_sum, a_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => W_rec m x)

lemma a1 : a 1 = 64 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_sum]; simp only [W_zero]; decide +kernel

lemma a2 : a 2 = 243 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_sum]; simp only [W1]; decide +kernel

lemma a3 : a 3 = 3969 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_sum]; simp only [W2]; decide +kernel

lemma a4 : a 4 = 64827 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_sum]; simp only [W3]; decide +kernel

lemma a_rec' (m : ℕ) : (a (m + 5) : ℚ) + 27 * a (m + 3) = 18 * a (m + 4) := by
  have h := a_rec m
  rw [show m + 4 + 1 = m + 5 from rfl, show m + 2 + 1 = m + 3 from rfl,
    show m + 3 + 1 = m + 4 from rfl] at h
  exact_mod_cast h

/-- Controls: the entry's data a(1..13). -/
theorem controls : a 1 = 64 ∧ a 2 = 243 ∧ a 3 = 3969 ∧ a 4 = 64827 ∧ a 5 = 1059723 ∧
    a 6 = 17324685 ∧ a 7 = 283231809 ∧ a 8 = 4630406067 ∧ a 9 = 75700050363 ∧
    a 10 = 1237579942725 ∧ a 11 = 20232537609249 ∧ a 12 = 330771018512907 ∧
    a 13 = 5407599817782603 := by
  have q : ∀ m : ℕ, a (m + 5) + 27 * a (m + 3) = 18 * a (m + 4) := fun m => by
    have h := a_rec m
    rw [show m + 4 + 1 = m + 5 from rfl, show m + 2 + 1 = m + 3 from rfl,
      show m + 3 + 1 = m + 4 from rfl] at h
    exact h
  have h5 : a 5 = 1059723 := by
    have h := q 0; norm_num [a3, a4] at h; generalize a 5 = x at h ⊢; omega
  have h6 : a 6 = 17324685 := by
    have h := q 1; norm_num [a4, h5] at h; generalize a 6 = x at h ⊢; omega
  have h7 : a 7 = 283231809 := by
    have h := q 2; norm_num [h5, h6] at h; generalize a 7 = x at h ⊢; omega
  have h8 : a 8 = 4630406067 := by
    have h := q 3; norm_num [h6, h7] at h; generalize a 8 = x at h ⊢; omega
  have h9 : a 9 = 75700050363 := by
    have h := q 4; norm_num [h7, h8] at h; generalize a 9 = x at h ⊢; omega
  have h10 : a 10 = 1237579942725 := by
    have h := q 5; norm_num [h8, h9] at h; generalize a 10 = x at h ⊢; omega
  have h11 : a 11 = 20232537609249 := by
    have h := q 6; norm_num [h9, h10] at h; generalize a 11 = x at h ⊢; omega
  have h12 : a 12 = 330771018512907 := by
    have h := q 7; norm_num [h10, h11] at h; generalize a 12 = x at h ⊢; omega
  have h13 : a 13 = 5407599817782603 := by
    have h := q 8; norm_num [h11, h12] at h; generalize a 13 = x at h ⊢; omega
  exact ⟨a1, a2, a3, a4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x(64 - 909x + 1323x^2 - 54x^3)/(1 - 18x + 27x^2). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 18 * X + 27 * X ^ 2) = X * (64 - 909 * X + 1323 * X ^ 2 - 54 * X ^ 3) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - 18 * X + 27 * X ^ 2) = A - C (18 : ℚ) * (A * X ^ 1) + C (27 : ℚ) * (A * X ^ 2) := by
    rw [show (C (18 : ℚ) : ℚ⟦X⟧) = 18 from map_ofNat C 18,
      show (C (27 : ℚ) : ℚ⟦X⟧) = 27 from map_ofNat C 27]
    ring
  have e2 : (X : ℚ⟦X⟧) * (64 - 909 * X + 1323 * X ^ 2 - 54 * X ^ 3) =
      C (64 : ℚ) * X ^ 1 - C (909 : ℚ) * X ^ 2 + C (1323 : ℚ) * X ^ 3 - C (54 : ℚ) * X ^ 4 := by
    rw [show (C (64 : ℚ) : ℚ⟦X⟧) = 64 from map_ofNat C 64,
      show (C (909 : ℚ) : ℚ⟦X⟧) = 909 from map_ofNat C 909,
      show (C (1323 : ℚ) : ℚ⟦X⟧) = 1323 from map_ofNat C 1323,
      show (C (54 : ℚ) : ℚ⟦X⟧) = 54 from map_ofNat C 54]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> simp [a1, a2, a3, a4] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have h' := a_rec' m
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show ¬ m + 5 = 0 by omega,
      show ¬ m + 4 = 0 by omega, show ¬ m + 3 = 0 by omega, show ¬ m + 2 = 0 by omega,
      show ¬ m + 1 = 0 by omega, show 1 ≤ m + 5 by omega, show 2 ≤ m + 5 by omega,
      show 3 ≤ m + 5 by omega, show 4 ≤ m + 5 by omega, if_true, if_false]
    linear_combination h'

/-- Barker's closed form, for n > 2. -/
theorem closed_form : ∀ n : ℕ, 2 < n →
    (a n : ℝ) = (49 / 54) * ((9 - 3 * Real.sqrt 6) ^ n + (3 * (3 + Real.sqrt 6)) ^ n) := by
  have s6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 6 with hs
  set H : ℕ → ℝ := fun n => (49 / 54) * ((9 - 3 * s) ^ n + (3 * (3 + s)) ^ n) with hH
  have H3 : H 3 = 3969 := by
    simp only [hH]
    linear_combination 441 * s6
  have H4 : H 4 = 64827 := by
    simp only [hH]
    linear_combination (8820 + 147 * s ^ 2) * s6
  have r1 : ∀ m : ℕ, (9 - 3 * s) ^ (m + 5) = 18 * (9 - 3 * s) ^ (m + 4) - 27 * (9 - 3 * s) ^ (m + 3) := by
    intro m
    have : (9 - 3 * s) ^ 2 = 18 * (9 - 3 * s) - 27 := by linear_combination 9 * s6
    calc (9 - 3 * s) ^ (m + 5) = (9 - 3 * s) ^ (m + 3) * (9 - 3 * s) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  have r2 : ∀ m : ℕ, (3 * (3 + s)) ^ (m + 5) =
      18 * (3 * (3 + s)) ^ (m + 4) - 27 * (3 * (3 + s)) ^ (m + 3) := by
    intro m
    have : (3 * (3 + s)) ^ 2 = 18 * (3 * (3 + s)) - 27 := by linear_combination 9 * s6
    calc (3 * (3 + s)) ^ (m + 5) = (3 * (3 + s)) ^ (m + 3) * (3 * (3 + s)) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  have Hrec : ∀ m, H (m + 5) = 18 * H (m + 4) - 27 * H (m + 3) := by
    intro m
    simp only [hH]
    rw [r1, r2]
    ring
  have key : ∀ m, (a (m + 3) : ℝ) = H (m + 3) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases m with _ | _ | m
      · rw [a3, H3]; norm_num
      · rw [a4, H4]; norm_num
      · have h' : (a (m + 5) : ℝ) + 27 * a (m + 3) = 18 * a (m + 4) := by
          have := a_rec' m
          exact_mod_cast this
        have e1 : (a (m + 3) : ℝ) = H (m + 3) := ih m (by omega)
        have e2 : (a (m + 4) : ℝ) = H (m + 4) := ih (m + 1) (by omega)
        show (a (m + 5) : ℝ) = H (m + 5)
        rw [Hrec m, ← e1, ← e2]
        linear_combination h'
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  exact key k

/-- Both of Barker's conjectures. -/
theorem conjecture : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 18 * X + 27 * X ^ 2) = X * (64 - 909 * X + 1323 * X ^ 2 - 54 * X ^ 3) ∧
    ∀ n : ℕ, 2 < n →
      (a n : ℝ) = (49 / 54) * ((9 - 3 * Real.sqrt 6) ^ n + (3 * (3 + Real.sqrt 6)) ^ n) :=
  ⟨gf, closed_form⟩

end OMA.S_oeis_a223332

theorem OMA.solution : type_of% @OMA.S_oeis_a223332.main :=
  OMA.S_oeis_a223332.conjecture
