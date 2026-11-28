import OMAStatements.S_oeis_a233257

-- Problem: A233257: Number of 2 X n 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabelled 6-colorings with no clashing color pairs).
-- Upstream: formal-conjectures statements/oeis-a233257.lean:0 (declaration OMA.S_oeis_a233257.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the order conditions say that the first of 1..4 to occur is 1 and the first of 2, 3
-- is 2; equivalently C1 (the first of 1..4 lies in {1,4}), C2 (every 4 has a 1 before it) and C3
-- (every 3 has a 2 before it). Each of the value maps (1 2)(4 3), (2 3), (1 4) keeps the clash
-- condition, and an involution argument (exactly one of x and its image satisfies the condition
-- unless the values concerned are absent) gives 2N(C1) = T + Z, 2N(C1 C3) = N(C1) + U and
-- 2N(C1 C3 C2) = N(C1 C3) + Z, so 8a = T + 2U + 5Z, where T, U, Z count the arrays without order
-- conditions with values in 0..5, in {0,1,4,5}, in {0,5}. Each is a transfer over columns split
-- by whether the two entries of the last column clash: T = 64*12^k, U = 8*4^k, Z = 0 at k+2
-- columns. Hence a(k+2) = 8*12^k + 2*4^k and a(1) = 3; the g.f. follows by comparing coefficients.

open OMA.S_oeis_a233257

theorem bef57_lt (n : ℕ) (i i' : Fin 2) (j j' : Fin n)
    (h : i'.val < i.val ∨ (i'.val = i.val ∧ j'.val < j.val)) :
    i'.val * n + j'.val < i.val * n + j.val := by
  have hi : i.val < 2 := i.isLt
  have hj' : j'.val < n := j'.isLt
  rcases h with h | ⟨h1, h2⟩
  · have e1 : i'.val = 0 := by omega
    have e2 : i.val = 1 := by omega
    rw [e1, e2, Nat.zero_mul, Nat.one_mul, Nat.zero_add]
    exact Nat.lt_of_lt_of_le hj' (Nat.le_add_right n _)
  · rw [h1]
    exact Nat.add_lt_add_left h2 _

/-- The array with the map τ applied to every entry. -/
def mapA57 (n : ℕ) (τ : Fin 6 → Fin 6) (x : Fin n → Fin 2 → Fin 6) : Fin n → Fin 2 → Fin 6 :=
  fun j i => τ (x j i)

theorem mapA57_inv (n : ℕ) (τ : Fin 6 → Fin 6) (hτ : ∀ v, τ (τ v) = v)
    (x : Fin n → Fin 2 → Fin 6) : mapA57 n τ (mapA57 n τ x) = x := by
  funext j i
  exact hτ (x j i)

/-- Every entry with V2 has an entry with V1 before it in row major order. -/
def FO57 (n : ℕ) (V1 V2 : Fin 6 → Bool) (x : Fin n → Fin 2 → Fin 6) : Prop :=
  ∀ j : Fin n, ∀ i : Fin 2, V2 (x j i) = true →
    ∃ j' : Fin n, ∃ i' : Fin 2, (i'.val < i.val ∨ (i'.val = i.val ∧ j'.val < j.val)) ∧
      V1 (x j' i') = true

instance (n : ℕ) (V1 V2 : Fin 6 → Bool) (x : Fin n → Fin 2 → Fin 6) :
    Decidable (FO57 n V1 V2 x) := by
  unfold FO57
  infer_instance

/-- No entry has V1 or V2. -/
def NoV57 (n : ℕ) (V1 V2 : Fin 6 → Bool) (x : Fin n → Fin 2 → Fin 6) : Prop :=
  ∀ j : Fin n, ∀ i : Fin 2, V1 (x j i) = false ∧ V2 (x j i) = false

instance (n : ℕ) (V1 V2 : Fin 6 → Bool) (x : Fin n → Fin 2 → Fin 6) :
    Decidable (NoV57 n V1 V2 x) := by
  unfold NoV57
  infer_instance

theorem FO57_or (n : ℕ) (V1 V2 : Fin 6 → Bool) (τ : Fin 6 → Fin 6)
    (h12 : ∀ v, V1 (τ v) = V2 v) (h21 : ∀ v, V2 (τ v) = V1 v)
    (hdisj : ∀ v, V1 v = true → V2 v = true → False)
    (x : Fin n → Fin 2 → Fin 6) : FO57 n V1 V2 x ∨ FO57 n V1 V2 (mapA57 n τ x) := by
  by_contra hc
  have h1 : ¬ FO57 n V1 V2 x := fun h => hc (Or.inl h)
  have h2 : ¬ FO57 n V1 V2 (mapA57 n τ x) := fun h => hc (Or.inr h)
  have e1 : ∃ j : Fin n, ∃ i : Fin 2, V2 (x j i) = true ∧ ∀ j' : Fin n, ∀ i' : Fin 2,
      (i'.val < i.val ∨ (i'.val = i.val ∧ j'.val < j.val)) → V1 (x j' i') = true → False := by
    by_contra hh
    apply h1
    intro j i hx
    by_contra hne
    exact hh ⟨j, i, hx, fun j' i' hb hx' => hne ⟨j', i', hb, hx'⟩⟩
  have e2 : ∃ j : Fin n, ∃ i : Fin 2, V1 (x j i) = true ∧ ∀ j' : Fin n, ∀ i' : Fin 2,
      (i'.val < i.val ∨ (i'.val = i.val ∧ j'.val < j.val)) → V2 (x j' i') = true → False := by
    by_contra hh
    apply h2
    intro j i hx
    by_contra hne
    exact hh ⟨j, i, (h21 (x j i)).symm.trans hx,
      fun j' i' hb hx' => hne ⟨j', i', hb, (h12 (x j' i')).trans hx'⟩⟩
  obtain ⟨j, i, hx, hb⟩ := e1
  obtain ⟨j2, i2, hx2, hb2⟩ := e2
  rcases lt_trichotomy i.val i2.val with hlt | heq | hgt
  · exact hb2 j i (Or.inl hlt) hx
  · rcases lt_trichotomy j.val j2.val with hlt' | heq' | hgt'
    · exact hb2 j i (Or.inr ⟨heq, hlt'⟩) hx
    · have ei : i = i2 := Fin.ext heq
      have ej : j = j2 := Fin.ext heq'
      subst ei ej
      exact hdisj _ hx2 hx
    · exact hb j2 i2 (Or.inr ⟨heq.symm, hgt'⟩) hx2
  · exact hb j2 i2 (Or.inl hgt) hx2

theorem FO57_both (n : ℕ) (V1 V2 : Fin 6 → Bool) (τ : Fin 6 → Fin 6)
    (h12 : ∀ v, V1 (τ v) = V2 v) (h21 : ∀ v, V2 (τ v) = V1 v)
    (x : Fin n → Fin 2 → Fin 6) (h1 : FO57 n V1 V2 x) (h2 : FO57 n V1 V2 (mapA57 n τ x)) :
    NoV57 n V1 V2 x := by
  have key : ∀ m : ℕ, ∀ j : Fin n, ∀ i : Fin 2, i.val * n + j.val < m →
      V1 (x j i) = false ∧ V2 (x j i) = false := by
    intro m
    induction m with
    | zero =>
      intro j i h
      exact absurd h (Nat.not_lt_zero _)
    | succ m ih =>
      intro j i hm
      constructor
      · rw [Bool.eq_false_iff]
        intro hx
        obtain ⟨j', i', hb, hx'⟩ := h2 j i ((h21 (x j i)).trans hx)
        have hv : V2 (x j' i') = true := (h12 (x j' i')).symm.trans hx'
        exact Bool.false_ne_true ((ih j' i'
          (Nat.lt_of_lt_of_le (bef57_lt n i i' j j' hb) (Nat.le_of_lt_succ hm))).2.symm.trans hv)
      · rw [Bool.eq_false_iff]
        intro hx
        obtain ⟨j', i', hb, hx'⟩ := h1 j i hx
        exact Bool.false_ne_true ((ih j' i'
          (Nat.lt_of_lt_of_le (bef57_lt n i i' j j' hb) (Nat.le_of_lt_succ hm))).1.symm.trans hx')
  intro j i
  exact key _ j i (Nat.lt_succ_self _)

theorem FO57_map (n : ℕ) (V1 V2 : Fin 6 → Bool) (τ : Fin 6 → Fin 6)
    (hp1 : ∀ v, V1 (τ v) = V1 v) (hp2 : ∀ v, V2 (τ v) = V2 v) (x : Fin n → Fin 2 → Fin 6) :
    FO57 n V1 V2 (mapA57 n τ x) ↔ FO57 n V1 V2 x := by
  constructor
  · intro h j i hx
    obtain ⟨j', i', hb, hx'⟩ := h j i ((hp2 (x j i)).trans hx)
    exact ⟨j', i', hb, (hp1 (x j' i')).symm.trans hx'⟩
  · intro h j i hx
    obtain ⟨j', i', hb, hx'⟩ := h j i ((hp2 (x j i)).symm.trans hx)
    exact ⟨j', i', hb, (hp1 (x j' i')).trans hx'⟩

/-- The involution argument: 2 N(FO) = |S| + N(no V1, V2). -/
theorem twiceFO57 (n : ℕ) (V1 V2 : Fin 6 → Bool) (τ : Fin 6 → Fin 6) (hτ : ∀ v, τ (τ v) = v)
    (h12 : ∀ v, V1 (τ v) = V2 v) (h21 : ∀ v, V2 (τ v) = V1 v)
    (hdisj : ∀ v, V1 v = true → V2 v = true → False)
    (hfix : ∀ v, V1 v = false → V2 v = false → τ v = v)
    (S : Finset (Fin n → Fin 2 → Fin 6)) (hS : ∀ x, x ∈ S → mapA57 n τ x ∈ S) :
    2 * (S.filter (FO57 n V1 V2)).card = S.card + (S.filter (NoV57 n V1 V2)).card := by
  have hinj : Function.Injective (mapA57 n τ) := by
    intro x y hxy
    rw [← mapA57_inv n τ hτ x, hxy, mapA57_inv n τ hτ y]
  have hI : ((S.filter (FO57 n V1 V2)).image (mapA57 n τ)).card = (S.filter (FO57 n V1 V2)).card :=
    Finset.card_image_of_injective _ hinj
  have memI : ∀ y, y ∈ (S.filter (FO57 n V1 V2)).image (mapA57 n τ) ↔
      y ∈ S ∧ FO57 n V1 V2 (mapA57 n τ y) := by
    intro y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Finset.mem_filter] at hx
      rw [mapA57_inv n τ hτ]
      exact ⟨hS x hx.1, hx.2⟩
    · rintro ⟨hy, hf⟩
      exact ⟨mapA57 n τ y, Finset.mem_filter.2 ⟨hS y hy, hf⟩, mapA57_inv n τ hτ y⟩
  have hU : S.filter (FO57 n V1 V2) ∪ (S.filter (FO57 n V1 V2)).image (mapA57 n τ) = S := by
    ext y
    rw [Finset.mem_union, memI, Finset.mem_filter]
    constructor
    · rintro (⟨hy, -⟩ | ⟨hy, -⟩)
      · exact hy
      · exact hy
    · intro hy
      rcases FO57_or n V1 V2 τ h12 h21 hdisj y with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
  have hN : S.filter (FO57 n V1 V2) ∩ (S.filter (FO57 n V1 V2)).image (mapA57 n τ) =
      S.filter (NoV57 n V1 V2) := by
    ext y
    rw [Finset.mem_inter, memI, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hy, h1⟩, -, h2⟩
      exact ⟨hy, FO57_both n V1 V2 τ h12 h21 y h1 h2⟩
    · rintro ⟨hy, hz⟩
      have hf : FO57 n V1 V2 y := fun j i hx => (Bool.false_ne_true ((hz j i).2.symm.trans hx)).elim
      have hs : mapA57 n τ y = y := by
        funext j i
        exact hfix (y j i) (hz j i).1 (hz j i).2
      refine ⟨⟨hy, hf⟩, hy, ?_⟩
      rw [hs]
      exact hf
  have hc := Finset.card_union_add_card_inter (S.filter (FO57 n V1 V2))
    ((S.filter (FO57 n V1 V2)).image (mapA57 n τ))
  rw [hU, hN, hI] at hc
  omega

theorem noClash_map57 (n : ℕ) (τ : Fin 6 → Fin 6) (hcl : ∀ u v, clash (τ u) (τ v) ↔ clash u v)
    (x : Fin n → Fin 2 → Fin 6) : noClash n (mapA57 n τ x) ↔ noClash n x := by
  constructor
  · intro h j k hk
    obtain ⟨h1, h2⟩ := h j k hk
    exact ⟨fun i hc => h1 i ((hcl (x j i) (x k i)).2 hc), fun hc => h2 ((hcl (x j 1) (x k 0)).2 hc)⟩
  · intro h j k hk
    obtain ⟨h1, h2⟩ := h j k hk
    exact ⟨fun i hc => h1 i ((hcl (x j i) (x k i)).1 hc), fun hc => h2 ((hcl (x j 1) (x k 0)).1 hc)⟩

theorem tl_map57 (n : ℕ) (τ : Fin 6 → Fin 6) (h0 : ∀ v, τ v = 0 ↔ v = 0)
    (x : Fin n → Fin 2 → Fin 6) : topLeftZero n (mapA57 n τ x) ↔ topLeftZero n x := by
  constructor
  · intro h j hj
    exact (h0 (x j 0)).1 (h j hj)
  · intro h j hj
    exact (h0 (x j 0)).2 (h j hj)

/-- The value sets and maps of the three involution steps. -/
def p1_57 (v : Fin 6) : Bool := decide (v = 1)
def p4_57 (v : Fin 6) : Bool := decide (v = 4)
def p2_57 (v : Fin 6) : Bool := decide (v = 2)
def p3_57 (v : Fin 6) : Bool := decide (v = 3)
def p14_57 (v : Fin 6) : Bool := decide (v = 1 ∨ v = 4)
def p23_57 (v : Fin 6) : Bool := decide (v = 2 ∨ v = 3)
def tA57 (v : Fin 6) : Fin 6 := if v = 1 then 4 else if v = 4 then 1 else v
def tB57 (v : Fin 6) : Fin 6 := if v = 2 then 3 else if v = 3 then 2 else v
def tC57 (v : Fin 6) : Fin 6 :=
  if v = 1 then 2 else if v = 2 then 1 else if v = 3 then 4 else if v = 4 then 3 else v

theorem tA57_inv : ∀ v, tA57 (tA57 v) = v := by decide
theorem tB57_inv : ∀ v, tB57 (tB57 v) = v := by decide
theorem tC57_inv : ∀ v, tC57 (tC57 v) = v := by decide
theorem tA57_cl : ∀ u v, clash (tA57 u) (tA57 v) ↔ clash u v := by decide
theorem tB57_cl : ∀ u v, clash (tB57 u) (tB57 v) ↔ clash u v := by decide
theorem tC57_cl : ∀ u v, clash (tC57 u) (tC57 v) ↔ clash u v := by decide
theorem tA57_0 : ∀ v, tA57 v = 0 ↔ v = 0 := by decide
theorem tB57_0 : ∀ v, tB57 v = 0 ↔ v = 0 := by decide
theorem tC57_0 : ∀ v, tC57 v = 0 ↔ v = 0 := by decide
theorem tA57_12 : ∀ v, p1_57 (tA57 v) = p4_57 v := by decide
theorem tA57_21 : ∀ v, p4_57 (tA57 v) = p1_57 v := by decide
theorem tB57_12 : ∀ v, p2_57 (tB57 v) = p3_57 v := by decide
theorem tB57_21 : ∀ v, p3_57 (tB57 v) = p2_57 v := by decide
theorem tC57_12 : ∀ v, p14_57 (tC57 v) = p23_57 v := by decide
theorem tC57_21 : ∀ v, p23_57 (tC57 v) = p14_57 v := by decide
theorem dA57 : ∀ v, p1_57 v = true → p4_57 v = true → False := by decide
theorem dB57 : ∀ v, p2_57 v = true → p3_57 v = true → False := by decide
theorem dC57 : ∀ v, p14_57 v = true → p23_57 v = true → False := by decide
theorem fA57 : ∀ v, p1_57 v = false → p4_57 v = false → tA57 v = v := by decide
theorem fB57 : ∀ v, p2_57 v = false → p3_57 v = false → tB57 v = v := by decide
theorem fC57 : ∀ v, p14_57 v = false → p23_57 v = false → tC57 v = v := by decide
theorem tA57_p14 : ∀ v, p14_57 (tA57 v) = p14_57 v := by decide
theorem tA57_p23 : ∀ v, p23_57 (tA57 v) = p23_57 v := by decide
theorem tA57_p2 : ∀ v, p2_57 (tA57 v) = p2_57 v := by decide
theorem tA57_p3 : ∀ v, p3_57 (tA57 v) = p3_57 v := by decide
theorem tB57_p14 : ∀ v, p14_57 (tB57 v) = p14_57 v := by decide
theorem tB57_p23 : ∀ v, p23_57 (tB57 v) = p23_57 v := by decide
theorem oU57 : ∀ v, p2_57 v = false → p3_57 v = false → p23_57 v = false := by decide
theorem oZ1_57 : ∀ v, p1_57 v = false → p4_57 v = false → p14_57 v = false := by decide
theorem oZ2_57 : ∀ v, p23_57 v = false → p3_57 v = false := by decide
theorem oZ3_57 : ∀ v, p14_57 v = false → p1_57 v = false := by decide
theorem oZ4_57 : ∀ v, p14_57 v = false → p4_57 v = false := by decide

/-- The arrays without the order conditions. -/
def T57 (n : ℕ) : Finset (Fin n → Fin 2 → Fin 6) :=
  Finset.univ.filter (fun x => noClash n x ∧ topLeftZero n x)

def N1_57 (n : ℕ) : Finset (Fin n → Fin 2 → Fin 6) := (T57 n).filter (FO57 n p14_57 p23_57)

def N13_57 (n : ℕ) : Finset (Fin n → Fin 2 → Fin 6) := (N1_57 n).filter (FO57 n p2_57 p3_57)

/-- Those with values in {0, 1, 4, 5}. -/
def U57 (n : ℕ) : Finset (Fin n → Fin 2 → Fin 6) := (T57 n).filter (NoV57 n p2_57 p3_57)

/-- Those with values in {0, 5}. -/
def Z57 (n : ℕ) : Finset (Fin n → Fin 2 → Fin 6) := (T57 n).filter (NoV57 n p14_57 p23_57)

theorem memT57 (n : ℕ) (x : Fin n → Fin 2 → Fin 6) :
    x ∈ T57 n ↔ noClash n x ∧ topLeftZero n x := by
  unfold T57
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem memN1_57 (n : ℕ) (x : Fin n → Fin 2 → Fin 6) :
    x ∈ N1_57 n ↔ x ∈ T57 n ∧ FO57 n p14_57 p23_57 x := by
  unfold N1_57
  exact Finset.mem_filter

theorem memN13_57 (n : ℕ) (x : Fin n → Fin 2 → Fin 6) :
    x ∈ N13_57 n ↔ x ∈ N1_57 n ∧ FO57 n p2_57 p3_57 x := by
  unfold N13_57
  exact Finset.mem_filter

theorem mapT57 (n : ℕ) (τ : Fin 6 → Fin 6) (hcl : ∀ u v, clash (τ u) (τ v) ↔ clash u v)
    (h0 : ∀ v, τ v = 0 ↔ v = 0) (x : Fin n → Fin 2 → Fin 6) (hx : x ∈ T57 n) :
    mapA57 n τ x ∈ T57 n := by
  rw [memT57] at hx ⊢
  exact ⟨(noClash_map57 n τ hcl x).2 hx.1, (tl_map57 n τ h0 x).2 hx.2⟩

theorem twoB_iff57 (n : ℕ) (x : Fin n → Fin 2 → Fin 6) :
    twoBeforeThree n x ↔ FO57 n p2_57 p3_57 x := by
  constructor
  · intro h j i hx
    obtain ⟨j', i', hb, hx'⟩ := h j i (of_decide_eq_true hx)
    exact ⟨j', i', hb, decide_eq_true hx'⟩
  · intro h j i hx
    obtain ⟨j', i', hb, hx'⟩ := h j i (decide_eq_true hx)
    exact ⟨j', i', hb, of_decide_eq_true hx'⟩

theorem oneFirst_iff57 (n : ℕ) (x : Fin n → Fin 2 → Fin 6) :
    oneFirst n x ↔ FO57 n p14_57 p23_57 x ∧ FO57 n p1_57 p4_57 x := by
  constructor
  · intro h
    refine ⟨fun j i hx => ?_, fun j i hx => ?_⟩
    · have hv : x j i = 2 ∨ x j i = 3 := of_decide_eq_true hx
      obtain ⟨j', i', hb, hx'⟩ := h j i (hv.elim Or.inl (fun h3 => Or.inr (Or.inl h3)))
      exact ⟨j', i', hb, decide_eq_true (Or.inl hx')⟩
    · have hv : x j i = 4 := of_decide_eq_true hx
      obtain ⟨j', i', hb, hx'⟩ := h j i (Or.inr (Or.inr hv))
      exact ⟨j', i', hb, decide_eq_true hx'⟩
  · rintro ⟨h1, h2⟩ j i hx
    have step : x j i = 2 ∨ x j i = 3 → ∃ j' : Fin n, ∃ i' : Fin 2,
        (i'.val < i.val ∨ (i'.val = i.val ∧ j'.val < j.val)) ∧ x j' i' = 1 := by
      intro h23
      obtain ⟨j', i', hb, hx'⟩ := h1 j i (decide_eq_true h23)
      have hv : x j' i' = 1 ∨ x j' i' = 4 := of_decide_eq_true hx'
      rcases hv with hv | hv
      · exact ⟨j', i', hb, hv⟩
      · obtain ⟨j'', i'', hb', hx''⟩ := h2 j' i' (decide_eq_true hv)
        exact ⟨j'', i'', by omega, of_decide_eq_true hx''⟩
    rcases hx with hx | hx | hx
    · exact step (Or.inl hx)
    · exact step (Or.inr hx)
    · obtain ⟨j', i', hb, hx'⟩ := h2 j i (decide_eq_true hx)
      exact ⟨j', i', hb, of_decide_eq_true hx'⟩

theorem a_eq57 (n : ℕ) : a n = ((N13_57 n).filter (FO57 n p1_57 p4_57)).card := by
  have hA : a n = ((Finset.univ : Finset (Fin n → Fin 2 → Fin 6)).filter
      (fun x => noClash n x ∧ topLeftZero n x ∧ oneFirst n x ∧ twoBeforeThree n x)).card := rfl
  have e : (Finset.univ : Finset (Fin n → Fin 2 → Fin 6)).filter
      (fun x => noClash n x ∧ topLeftZero n x ∧ oneFirst n x ∧ twoBeforeThree n x) =
      (N13_57 n).filter (FO57 n p1_57 p4_57) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, memN13_57, memN1_57, memT57, oneFirst_iff57,
      twoB_iff57]
    constructor
    · rintro ⟨-, h1, h2, ⟨h3, h4⟩, h5⟩
      exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h5⟩, h4⟩
    · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h5⟩, h4⟩
      exact ⟨Finset.mem_univ _, h1, h2, ⟨h3, h4⟩, h5⟩
  rw [hA, e]

theorem count57 (n : ℕ) : 8 * a n = (T57 n).card + 2 * (U57 n).card + 5 * (Z57 n).card := by
  have hA := a_eq57 n
  have hStA : 2 * ((N13_57 n).filter (FO57 n p1_57 p4_57)).card =
      (N13_57 n).card + ((N13_57 n).filter (NoV57 n p1_57 p4_57)).card := by
    refine twiceFO57 n p1_57 p4_57 tA57 tA57_inv tA57_12 tA57_21 dA57 fA57 (N13_57 n) ?_
    intro x hx
    rw [memN13_57, memN1_57] at hx ⊢
    exact ⟨⟨mapT57 n tA57 tA57_cl tA57_0 x hx.1.1,
      (FO57_map n p14_57 p23_57 tA57 tA57_p14 tA57_p23 x).2 hx.1.2⟩,
      (FO57_map n p2_57 p3_57 tA57 tA57_p2 tA57_p3 x).2 hx.2⟩
  have hStB : 2 * (N13_57 n).card = (N1_57 n).card + ((N1_57 n).filter (NoV57 n p2_57 p3_57)).card := by
    refine twiceFO57 n p2_57 p3_57 tB57 tB57_inv tB57_12 tB57_21 dB57 fB57 (N1_57 n) ?_
    intro x hx
    rw [memN1_57] at hx ⊢
    exact ⟨mapT57 n tB57 tB57_cl tB57_0 x hx.1,
      (FO57_map n p14_57 p23_57 tB57 tB57_p14 tB57_p23 x).2 hx.2⟩
  have hStC : 2 * (N1_57 n).card = (T57 n).card + (Z57 n).card :=
    twiceFO57 n p14_57 p23_57 tC57 tC57_inv tC57_12 tC57_21 dC57 fC57 (T57 n)
      (fun x hx => mapT57 n tC57 tC57_cl tC57_0 x hx)
  have eU : (N1_57 n).filter (NoV57 n p2_57 p3_57) = U57 n := by
    ext x
    unfold U57
    rw [Finset.mem_filter, Finset.mem_filter, memN1_57]
    constructor
    · rintro ⟨⟨hT, -⟩, hN⟩
      exact ⟨hT, hN⟩
    · rintro ⟨hT, hN⟩
      refine ⟨⟨hT, fun j i hv => ?_⟩, hN⟩
      exact (Bool.false_ne_true ((oU57 _ (hN j i).1 (hN j i).2).symm.trans hv)).elim
  have eZ : (N13_57 n).filter (NoV57 n p1_57 p4_57) = Z57 n := by
    ext x
    unfold Z57
    rw [Finset.mem_filter, Finset.mem_filter, memN13_57, memN1_57]
    constructor
    · rintro ⟨⟨⟨hT, hC⟩, -⟩, hN⟩
      refine ⟨hT, fun j i => ⟨oZ1_57 _ (hN j i).1 (hN j i).2, ?_⟩⟩
      rw [Bool.eq_false_iff]
      intro hv
      obtain ⟨j', i', -, hv'⟩ := hC j i hv
      exact Bool.false_ne_true ((oZ1_57 _ (hN j' i').1 (hN j' i').2).symm.trans hv')
    · rintro ⟨hT, hN⟩
      refine ⟨⟨⟨hT, fun j i hv => ?_⟩, fun j i hv => ?_⟩, fun j i => ⟨?_, ?_⟩⟩
      · exact (Bool.false_ne_true ((hN j i).2.symm.trans hv)).elim
      · exact (Bool.false_ne_true ((oZ2_57 _ (hN j i).2).symm.trans hv)).elim
      · exact oZ3_57 _ (hN j i).1
      · exact oZ4_57 _ (hN j i).1
  rw [eU] at hStB
  rw [eZ] at hStA
  omega

/-- Arrays of m+1 columns (each column a pair: top, bottom) whose first column satisfies F,
whose columns all satisfy K, and whose consecutive columns satisfy R. -/
def W57 (R : Fin 6 × Fin 6 → Fin 6 × Fin 6 → Bool) (F K : Fin 6 × Fin 6 → Bool) (m : ℕ) :
    Finset (Fin (m + 1) → Fin 6 × Fin 6) :=
  Finset.univ.filter (fun y => F (y ⟨0, Nat.succ_pos m⟩) = true ∧ (∀ j, K (y j) = true) ∧
    ∀ j : Fin m, R (y j.castSucc) (y j.succ) = true)

theorem memW57 (R : Fin 6 × Fin 6 → Fin 6 × Fin 6 → Bool) (F K : Fin 6 × Fin 6 → Bool) (m : ℕ)
    (y : Fin (m + 1) → Fin 6 × Fin 6) :
    y ∈ W57 R F K m ↔ F (y ⟨0, Nat.succ_pos m⟩) = true ∧ (∀ j, K (y j) = true) ∧
      ∀ j : Fin m, R (y j.castSucc) (y j.succ) = true := by
  unfold W57
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem memW57_snoc (R : Fin 6 × Fin 6 → Fin 6 × Fin 6 → Bool) (F K : Fin 6 × Fin 6 → Bool)
    (m : ℕ) (t : Fin (m + 1) → Fin 6 × Fin 6) (c : Fin 6 × Fin 6) :
    (Fin.snoc t c : Fin (m + 1 + 1) → Fin 6 × Fin 6) ∈ W57 R F K (m + 1) ↔
      t ∈ W57 R F K m ∧ K c = true ∧ R (t (Fin.last m)) c = true := by
  rw [memW57, memW57]
  have e : (⟨0, Nat.succ_pos (m + 1)⟩ : Fin (m + 1 + 1)) =
      Fin.castSucc (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) := Fin.ext rfl
  rw [e, Fin.snoc_castSucc]
  constructor
  · rintro ⟨hF, hK, hR⟩
    refine ⟨⟨hF, fun j => ?_, fun j => ?_⟩, ?_, ?_⟩
    · have h := hK j.castSucc
      rw [Fin.snoc_castSucc] at h
      exact h
    · have h := hR j.castSucc
      rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc] at h
      exact h
    · have h := hK (Fin.last (m + 1))
      rw [Fin.snoc_last] at h
      exact h
    · have h := hR (Fin.last m)
      rw [show (Fin.last m).succ = Fin.last (m + 1) from Fin.succ_last m, Fin.snoc_last,
        Fin.snoc_castSucc] at h
      exact h
  · rintro ⟨⟨hF, hK, hR⟩, hc, hl⟩
    refine ⟨hF, fun j => ?_, fun j => ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        exact hK j'
      · rw [Fin.snoc_last]
        exact hc
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hR j'
      · rw [show (Fin.last m).succ = Fin.last (m + 1) from Fin.succ_last m, Fin.snoc_last,
          Fin.snoc_castSucc]
        exact hl

/-- One transfer step: remove the last column. -/
theorem stepW57 (R : Fin 6 × Fin 6 → Fin 6 × Fin 6 → Bool) (F K P : Fin 6 × Fin 6 → Bool)
    (m : ℕ) :
    ((W57 R F K (m + 1)).filter (fun y => P (y (Fin.last (m + 1))) = true)).card =
      ∑ t ∈ W57 R F K m, (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
        K c = true ∧ R (t (Fin.last m)) c = true ∧ P c = true)).card := by
  have H : (((W57 R F K (m + 1)).filter (fun y => P (y (Fin.last (m + 1))) = true) :
      Finset (Fin (m + 1 + 1) → Fin 6 × Fin 6)) : Set (Fin (m + 1 + 1) → Fin 6 × Fin 6)).MapsTo
      (fun y : Fin (m + 1 + 1) → Fin 6 × Fin 6 => Fin.init y)
      ((W57 R F K m : Finset (Fin (m + 1) → Fin 6 × Fin 6)) :
        Set (Fin (m + 1) → Fin 6 × Fin 6)) := by
    intro y hy
    have hy1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).1
    have e : y = (Fin.snoc (Fin.init y) (y (Fin.last (m + 1))) :
        Fin (m + 1 + 1) → Fin 6 × Fin 6) := (Fin.snoc_init_self y).symm
    rw [e, memW57_snoc] at hy1
    exact Finset.mem_coe.2 hy1.1
  rw [Finset.card_eq_sum_card_fiberwise H]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.card_nbij' (fun y : Fin (m + 1 + 1) → Fin 6 × Fin 6 => y (Fin.last (m + 1)))
    (fun c : Fin 6 × Fin 6 => (Fin.snoc t c : Fin (m + 1 + 1) → Fin 6 × Fin 6))
  · intro y hy
    have hy' := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
    have hyW := (Finset.mem_filter.1 hy'.1).1
    have hP := (Finset.mem_filter.1 hy'.1).2
    have hyt : Fin.init y = t := hy'.2
    have e : y = (Fin.snoc (Fin.init y) (y (Fin.last (m + 1))) :
        Fin (m + 1 + 1) → Fin 6 × Fin 6) := (Fin.snoc_init_self y).symm
    rw [e, memW57_snoc] at hyW
    obtain ⟨-, hK, hR⟩ := hyW
    rw [hyt] at hR
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hK, hR, hP⟩)
  · intro c hc
    obtain ⟨hK, hR, hP⟩ := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
    have hW := (memW57_snoc R F K m t c).2 ⟨ht, hK, hR⟩
    have hP' : P ((Fin.snoc t c : Fin (m + 1 + 1) → Fin 6 × Fin 6) (Fin.last (m + 1))) = true := by
      rw [Fin.snoc_last]
      exact hP
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hW, hP'⟩, Fin.init_snoc _ _⟩)
  · intro y hy
    have hyt : Fin.init y = t := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    show (Fin.snoc t (y (Fin.last (m + 1))) : Fin (m + 1 + 1) → Fin 6 × Fin 6) = y
    rw [← hyt]
    exact Fin.snoc_init_self y
  · intro c _
    show (Fin.snoc t c : Fin (m + 1 + 1) → Fin 6 × Fin 6) (Fin.last (m + 1)) = c
    rw [Fin.snoc_last]

/-- The arrays with one column. -/
theorem baseW57 (R : Fin 6 × Fin 6 → Fin 6 × Fin 6 → Bool) (F K P : Fin 6 × Fin 6 → Bool) :
    ((W57 R F K 0).filter (fun y => P (y (Fin.last 0)) = true)).card =
      (Finset.univ.filter (fun c : Fin 6 × Fin 6 => F c = true ∧ K c = true ∧ P c = true)).card := by
  apply Finset.card_nbij' (fun y : Fin (0 + 1) → Fin 6 × Fin 6 => y (Fin.last 0))
    (fun c : Fin 6 × Fin 6 => fun _ : Fin (0 + 1) => c)
  · intro y hy
    have hy' := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
    obtain ⟨hF, hK, -⟩ := (memW57 R F K 0 y).1 hy'.1
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hF, hK _, hy'.2⟩)
  · intro c hc
    obtain ⟨hF, hK, hP⟩ := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
    exact Finset.mem_coe.2 (Finset.mem_filter.2
      ⟨(memW57 R F K 0 _).2 ⟨hF, fun _ => hK, fun j => j.elim0⟩, hP⟩)
  · intro y _
    funext j
    show y (Fin.last 0) = y j
    have hj : j = Fin.last 0 := Fin.ext (by have := j.isLt; rw [Fin.val_last]; omega)
    rw [hj]
  · intro c _
    rfl

/-- The transfer step when the weights depend only on whether Q holds at the last column. -/
theorem classStep57 (R : Fin 6 × Fin 6 → Fin 6 × Fin 6 → Bool) (F K P Q : Fin 6 × Fin 6 → Bool)
    (wa wb m : ℕ)
    (hw : ∀ d : Fin 6 × Fin 6, K d = true →
      (Finset.univ.filter (fun c : Fin 6 × Fin 6 => K c = true ∧ R d c = true ∧ P c = true)).card =
        if Q d = true then wa else wb) :
    ((W57 R F K (m + 1)).filter (fun y => P (y (Fin.last (m + 1))) = true)).card =
      ((W57 R F K m).filter (fun y => Q (y (Fin.last m)) = true)).card * wa +
        ((W57 R F K m).filter (fun y => ¬ (Q (y (Fin.last m)) = true))).card * wb := by
  rw [stepW57]
  have e : ∀ t ∈ W57 R F K m,
      (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
        K c = true ∧ R (t (Fin.last m)) c = true ∧ P c = true)).card =
        if Q (t (Fin.last m)) = true then wa else wb :=
    fun t ht => hw (t (Fin.last m)) (((memW57 R F K m t).1 ht).2.1 (Fin.last m))
  rw [Finset.sum_congr rfl e, Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul,
    smul_eq_mul]

/-- The columns of an array, as pairs (top, bottom). -/
def toP57 (n : ℕ) (x : Fin n → Fin 2 → Fin 6) : Fin n → Fin 6 × Fin 6 := fun j => (x j 0, x j 1)

theorem card_toP57 (n : ℕ) (S : Finset (Fin n → Fin 6 × Fin 6)) :
    (Finset.univ.filter (fun x : Fin n → Fin 2 → Fin 6 => toP57 n x ∈ S)).card = S.card := by
  apply Finset.card_nbij' (toP57 n)
    (fun y : Fin n → Fin 6 × Fin 6 => fun j i => if i = 0 then (y j).1 else (y j).2)
  · intro x hx
    exact Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
  · intro y hy
    have e : toP57 n (fun j i => if i = 0 then (y j).1 else (y j).2) = y := by
      funext j
      show ((if (0 : Fin 2) = 0 then (y j).1 else (y j).2),
        (if (1 : Fin 2) = 0 then (y j).1 else (y j).2)) = y j
      have e0 : (if (0 : Fin 2) = 0 then (y j).1 else (y j).2) = (y j).1 := if_pos rfl
      have e1 : (if (1 : Fin 2) = 0 then (y j).1 else (y j).2) = (y j).2 :=
        if_neg (show ¬ ((1 : Fin 2) = 0) by decide)
      exact (congrArg₂ Prod.mk e0 e1).trans Prod.mk.eta
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    show toP57 n (fun j i => if i = 0 then (y j).1 else (y j).2) ∈ S
    rw [e]
    exact Finset.mem_coe.1 hy
  · intro x _
    funext j i
    show (if i = 0 then x j 0 else x j 1) = x j i
    have hj : ∀ i : Fin 2, (if i = 0 then x j 0 else x j 1) = x j i :=
      Fin.forall_fin_two.2 ⟨if_pos rfl, if_neg (show ¬ ((1 : Fin 2) = 0) by decide)⟩
    exact hj i
  · intro y _
    funext j
    show ((if (0 : Fin 2) = 0 then (y j).1 else (y j).2),
      (if (1 : Fin 2) = 0 then (y j).1 else (y j).2)) = y j
    have e0 : (if (0 : Fin 2) = 0 then (y j).1 else (y j).2) = (y j).1 := if_pos rfl
    have e1 : (if (1 : Fin 2) = 0 then (y j).1 else (y j).2) = (y j).2 :=
      if_neg (show ¬ ((1 : Fin 2) = 0) by decide)
    exact (congrArg₂ Prod.mk e0 e1).trans Prod.mk.eta

/-- The clash relation between consecutive columns d, c (as pairs). -/
def R57 (d c : Fin 6 × Fin 6) : Bool :=
  decide (¬ clash d.1 c.1 ∧ ¬ clash d.2 c.2 ∧ ¬ clash d.2 c.1)

/-- The first column has top element zero. -/
def F57 (c : Fin 6 × Fin 6) : Bool := decide (c.1 = 0)

/-- No condition on the columns. -/
def KT57 (_c : Fin 6 × Fin 6) : Bool := true

/-- The column has no entry 2 or 3. -/
def KU57 (c : Fin 6 × Fin 6) : Bool :=
  decide ((p2_57 c.1 = false ∧ p3_57 c.1 = false) ∧ (p2_57 c.2 = false ∧ p3_57 c.2 = false))

/-- The column has entries in {0, 5} only. -/
def KZ57 (c : Fin 6 × Fin 6) : Bool :=
  decide ((p14_57 c.1 = false ∧ p23_57 c.1 = false) ∧ (p14_57 c.2 = false ∧ p23_57 c.2 = false))

/-- The two entries of the column clash (lie in the same pair). -/
def QS57 (c : Fin 6 × Fin 6) : Bool := decide (clash c.1 c.2)

/-- They do not. -/
def QN57 (c : Fin 6 × Fin 6) : Bool := decide (¬ clash c.1 c.2)

theorem nc_iff57 (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 6) :
    noClash (m + 1) x ↔
      ∀ j : Fin m, R57 (toP57 (m + 1) x j.castSucc) (toP57 (m + 1) x j.succ) = true := by
  constructor
  · intro h j
    obtain ⟨h1, h2⟩ := h j.castSucc j.succ rfl
    unfold R57
    exact decide_eq_true ⟨h1 0, h1 1, h2⟩
  · intro h j k hk
    have hj : j.val < m := by
      have := k.isLt
      omega
    have e1 : (⟨j.val, hj⟩ : Fin m).castSucc = j := Fin.ext rfl
    have e2 : (⟨j.val, hj⟩ : Fin m).succ = k := Fin.ext (by rw [Fin.val_succ]; exact hk.symm)
    have h' := of_decide_eq_true (h ⟨j.val, hj⟩)
    rw [e1, e2] at h'
    obtain ⟨h1, h2, h3⟩ := h'
    exact ⟨Fin.forall_fin_two.2 ⟨h1, h2⟩, h3⟩

theorem tl_iff57 (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 6) :
    topLeftZero (m + 1) x ↔ F57 (toP57 (m + 1) x ⟨0, Nat.succ_pos m⟩) = true := by
  constructor
  · intro h
    unfold F57
    exact decide_eq_true (h ⟨0, Nat.succ_pos m⟩ rfl)
  · intro h j hj
    have e : j = ⟨0, Nat.succ_pos m⟩ := Fin.ext hj
    rw [e]
    exact of_decide_eq_true h

theorem kp57 (K : Fin 6 × Fin 6 → Bool) (P : Fin 6 → Prop)
    (hK : ∀ p q : Fin 6, K (p, q) = true ↔ (P p ∧ P q)) (m : ℕ)
    (x : Fin (m + 1) → Fin 2 → Fin 6) :
    (∀ j : Fin (m + 1), ∀ i : Fin 2, P (x j i)) ↔ ∀ j, K (toP57 (m + 1) x j) = true := by
  constructor
  · intro h j
    exact (hK (x j 0) (x j 1)).2 ⟨h j 0, h j 1⟩
  · intro h j
    exact Fin.forall_fin_two.2 ((hK (x j 0) (x j 1)).1 (h j))

theorem hKU57 : ∀ p q : Fin 6, KU57 (p, q) = true ↔
    ((p2_57 p = false ∧ p3_57 p = false) ∧ (p2_57 q = false ∧ p3_57 q = false)) := by
  intro p q
  unfold KU57
  exact ⟨of_decide_eq_true, decide_eq_true⟩

theorem hKZ57 : ∀ p q : Fin 6, KZ57 (p, q) = true ↔
    ((p14_57 p = false ∧ p23_57 p = false) ∧ (p14_57 q = false ∧ p23_57 q = false)) := by
  intro p q
  unfold KZ57
  exact ⟨of_decide_eq_true, decide_eq_true⟩

theorem cardT57 (m : ℕ) : (T57 (m + 1)).card = (W57 R57 F57 KT57 m).card := by
  have e : T57 (m + 1) = Finset.univ.filter
      (fun x : Fin (m + 1) → Fin 2 → Fin 6 => toP57 (m + 1) x ∈ W57 R57 F57 KT57 m) := by
    ext x
    rw [memT57, Finset.mem_filter, memW57, nc_iff57, tl_iff57]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨Finset.mem_univ _, h2, fun _ => rfl, h1⟩
    · rintro ⟨-, h2, -, h1⟩
      exact ⟨h1, h2⟩
  rw [e, card_toP57]

theorem cardU57 (m : ℕ) : (U57 (m + 1)).card = (W57 R57 F57 KU57 m).card := by
  have e : U57 (m + 1) = Finset.univ.filter
      (fun x : Fin (m + 1) → Fin 2 → Fin 6 => toP57 (m + 1) x ∈ W57 R57 F57 KU57 m) := by
    ext x
    unfold U57
    rw [Finset.mem_filter, Finset.mem_filter, memT57, memW57, nc_iff57, tl_iff57]
    have hk := kp57 KU57 (fun v => p2_57 v = false ∧ p3_57 v = false) hKU57 m x
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨Finset.mem_univ _, h2, hk.1 h3, h1⟩
    · rintro ⟨-, h2, h3, h1⟩
      exact ⟨⟨h1, h2⟩, hk.2 h3⟩
  rw [e, card_toP57]

theorem cardZ57 (m : ℕ) : (Z57 (m + 1)).card = (W57 R57 F57 KZ57 m).card := by
  have e : Z57 (m + 1) = Finset.univ.filter
      (fun x : Fin (m + 1) → Fin 2 → Fin 6 => toP57 (m + 1) x ∈ W57 R57 F57 KZ57 m) := by
    ext x
    unfold Z57
    rw [Finset.mem_filter, Finset.mem_filter, memT57, memW57, nc_iff57, tl_iff57]
    have hk := kp57 KZ57 (fun v => p14_57 v = false ∧ p23_57 v = false) hKZ57 m x
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨Finset.mem_univ _, h2, hk.1 h3, h1⟩
    · rintro ⟨-, h2, h3, h1⟩
      exact ⟨⟨h1, h2⟩, hk.2 h3⟩
  rw [e, card_toP57]

theorem wTs57 : ∀ d : Fin 6 × Fin 6, KT57 d = true →
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      KT57 c = true ∧ R57 d c = true ∧ QS57 c = true)).card = if QS57 d = true then 8 else 4 := by
  decide +kernel

theorem wTn57 : ∀ d : Fin 6 × Fin 6, KT57 d = true →
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      KT57 c = true ∧ R57 d c = true ∧ QN57 c = true)).card = if QS57 d = true then 8 else 4 := by
  decide +kernel

theorem wUs57 : ∀ d : Fin 6 × Fin 6, KU57 d = true →
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      KU57 c = true ∧ R57 d c = true ∧ QS57 c = true)).card = if QS57 d = true then 4 else 0 := by
  decide +kernel

theorem wUn57 : ∀ d : Fin 6 × Fin 6, KU57 d = true →
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      KU57 c = true ∧ R57 d c = true ∧ QN57 c = true)).card = if QS57 d = true then 0 else 0 := by
  decide +kernel

theorem wZs57 : ∀ d : Fin 6 × Fin 6, KZ57 d = true →
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      KZ57 c = true ∧ R57 d c = true ∧ QS57 c = true)).card = if QS57 d = true then 0 else 0 := by
  decide +kernel

theorem wZn57 : ∀ d : Fin 6 × Fin 6, KZ57 d = true →
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      KZ57 c = true ∧ R57 d c = true ∧ QN57 c = true)).card = if QS57 d = true then 0 else 0 := by
  decide +kernel

theorem bases57 :
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      F57 c = true ∧ KT57 c = true ∧ QS57 c = true)).card = 2 ∧
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      F57 c = true ∧ KT57 c = true ∧ QN57 c = true)).card = 4 ∧
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      F57 c = true ∧ KU57 c = true ∧ QS57 c = true)).card = 2 ∧
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      F57 c = true ∧ KU57 c = true ∧ QN57 c = true)).card = 2 ∧
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      F57 c = true ∧ KZ57 c = true ∧ QS57 c = true)).card = 2 ∧
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      F57 c = true ∧ KZ57 c = true ∧ QN57 c = true)).card = 0 := by
  decide +kernel

theorem qn57 : ∀ c : Fin 6 × Fin 6, QN57 c = true ↔ ¬ (QS57 c = true) := by
  decide

theorem filtNeg57 (K : Fin 6 × Fin 6 → Bool) (m : ℕ) :
    (W57 R57 F57 K m).filter (fun y => ¬ (QS57 (y (Fin.last m)) = true)) =
      (W57 R57 F57 K m).filter (fun y => QN57 (y (Fin.last m)) = true) :=
  Finset.filter_congr (fun y _ => (qn57 (y (Fin.last m))).symm)

theorem steps57 (K : Fin 6 × Fin 6 → Bool) (m : ℕ) (e1 e2 n1 n2 : ℕ)
    (hwe : ∀ d : Fin 6 × Fin 6, K d = true →
      (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
        K c = true ∧ R57 d c = true ∧ QS57 c = true)).card = if QS57 d = true then e1 else e2)
    (hwn : ∀ d : Fin 6 × Fin 6, K d = true →
      (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
        K c = true ∧ R57 d c = true ∧ QN57 c = true)).card = if QS57 d = true then n1 else n2) :
    ((W57 R57 F57 K (m + 1)).filter (fun y => QS57 (y (Fin.last (m + 1))) = true)).card =
      ((W57 R57 F57 K m).filter (fun y => QS57 (y (Fin.last m)) = true)).card * e1 +
        ((W57 R57 F57 K m).filter (fun y => ¬ (QS57 (y (Fin.last m)) = true))).card * e2 ∧
    ((W57 R57 F57 K (m + 1)).filter (fun y => ¬ (QS57 (y (Fin.last (m + 1))) = true))).card =
      ((W57 R57 F57 K m).filter (fun y => QS57 (y (Fin.last m)) = true)).card * n1 +
        ((W57 R57 F57 K m).filter (fun y => ¬ (QS57 (y (Fin.last m)) = true))).card * n2 := by
  refine ⟨classStep57 R57 F57 K QS57 QS57 e1 e2 m hwe, ?_⟩
  rw [filtNeg57 K (m + 1)]
  exact classStep57 R57 F57 K QN57 QS57 n1 n2 m hwn

theorem OMA.solution : type_of% @OMA.S_oeis_a233257.main := by
  obtain ⟨ce, hce⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W57 R57 F57 KT57 m).filter (fun y => QS57 (y (Fin.last m)) = true)).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨cn, hcn⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W57 R57 F57 KT57 m).filter (fun y => ¬ (QS57 (y (Fin.last m)) = true))).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨ue, hue⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W57 R57 F57 KU57 m).filter (fun y => QS57 (y (Fin.last m)) = true)).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨un, hun⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W57 R57 F57 KU57 m).filter (fun y => ¬ (QS57 (y (Fin.last m)) = true))).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨ze, hze⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W57 R57 F57 KZ57 m).filter (fun y => QS57 (y (Fin.last m)) = true)).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨zn, hzn⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W57 R57 F57 KZ57 m).filter (fun y => ¬ (QS57 (y (Fin.last m)) = true))).card :=
    ⟨_, fun _ => rfl⟩
  have rT : ∀ m, ce (m + 1) = ce m * 8 + cn m * 4 ∧ cn (m + 1) = ce m * 8 + cn m * 4 := by
    intro m
    rw [hce (m + 1), hcn (m + 1), hce m, hcn m]
    exact steps57 KT57 m 8 4 8 4 wTs57 wTn57
  have rU : ∀ m, ue (m + 1) = ue m * 4 + un m * 0 ∧ un (m + 1) = ue m * 0 + un m * 0 := by
    intro m
    rw [hue (m + 1), hun (m + 1), hue m, hun m]
    exact steps57 KU57 m 4 0 0 0 wUs57 wUn57
  have rZ : ∀ m, ze (m + 1) = ze m * 0 + zn m * 0 ∧ zn (m + 1) = ze m * 0 + zn m * 0 := by
    intro m
    rw [hze (m + 1), hzn (m + 1), hze m, hzn m]
    exact steps57 KZ57 m 0 0 0 0 wZs57 wZn57
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := bases57
  have ce0 : ce 0 = 2 := by
    rw [hce 0, baseW57 R57 F57 KT57 QS57]
    exact b1
  have cn0 : cn 0 = 4 := by
    rw [hcn 0, filtNeg57 KT57 0, baseW57 R57 F57 KT57 QN57]
    exact b2
  have ue0 : ue 0 = 2 := by
    rw [hue 0, baseW57 R57 F57 KU57 QS57]
    exact b3
  have un0 : un 0 = 2 := by
    rw [hun 0, filtNeg57 KU57 0, baseW57 R57 F57 KU57 QN57]
    exact b4
  have ze0 : ze 0 = 2 := by
    rw [hze 0, baseW57 R57 F57 KZ57 QS57]
    exact b5
  have zn0 : zn 0 = 0 := by
    rw [hzn 0, filtNeg57 KZ57 0, baseW57 R57 F57 KZ57 QN57]
    exact b6
  have hT : ∀ k, ce (k + 1) = 32 * 12 ^ k ∧ cn (k + 1) = 32 * 12 ^ k := by
    intro k
    induction k with
    | zero =>
      obtain ⟨r1, r2⟩ := rT 0
      rw [pow_zero]
      omega
    | succ k ih =>
      obtain ⟨r1, r2⟩ := rT (k + 1)
      obtain ⟨i1, i2⟩ := ih
      rw [pow_succ]
      omega
  have hU : ∀ k, ue (k + 1) = 8 * 4 ^ k ∧ un (k + 1) = 0 := by
    intro k
    induction k with
    | zero =>
      obtain ⟨r1, r2⟩ := rU 0
      rw [pow_zero]
      omega
    | succ k ih =>
      obtain ⟨r1, r2⟩ := rU (k + 1)
      obtain ⟨i1, i2⟩ := ih
      rw [pow_succ]
      omega
  have hZ : ∀ k, ze (k + 1) = 0 ∧ zn (k + 1) = 0 := by
    intro k
    obtain ⟨r1, r2⟩ := rZ k
    omega
  have htot : ∀ m, 8 * a (m + 1) =
      ce m + cn m + 2 * (ue m + un m) + 5 * (ze m + zn m) := by
    intro m
    have h1 := count57 (m + 1)
    have h2 := Finset.card_filter_add_card_filter_not (s := W57 R57 F57 KT57 m)
      (fun y => QS57 (y (Fin.last m)) = true)
    have h3 := Finset.card_filter_add_card_filter_not (s := W57 R57 F57 KU57 m)
      (fun y => QS57 (y (Fin.last m)) = true)
    have h4 := Finset.card_filter_add_card_filter_not (s := W57 R57 F57 KZ57 m)
      (fun y => QS57 (y (Fin.last m)) = true)
    rw [cardT57 m, cardU57 m, cardZ57 m, ← h2, ← h3, ← h4] at h1
    rw [hce m, hcn m, hue m, hun m, hze m, hzn m]
    omega
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℕ, ∀ n, a n = b n := ⟨a, fun _ => rfl⟩
  have htotb : ∀ m, 8 * b (m + 1) =
      ce m + cn m + 2 * (ue m + un m) + 5 * (ze m + zn m) := by
    intro m
    rw [← hb]
    exact htot m
  have v1 : b 1 = 3 := by
    have h := htotb 0
    rw [show (0 : ℕ) + 1 = 1 from rfl] at h
    omega
  have hk : ∀ k, b (k + 2) = 8 * 12 ^ k + 2 * 4 ^ k := by
    intro k
    have h := htotb (k + 1)
    rw [show k + 1 + 1 = k + 2 by omega] at h
    obtain ⟨t1, t2⟩ := hT k
    obtain ⟨u1, u2⟩ := hU k
    obtain ⟨z1, z2⟩ := hZ k
    omega
  have hq : ∀ k, (b (k + 2) : ℚ) = 8 * 12 ^ k + 2 * 4 ^ k := by
    intro k
    exact_mod_cast hk k
  have v2 : b 2 = 10 := by
    have h := hk 0
    rw [show (0 : ℕ) + 2 = 2 from rfl] at h
    rw [h]
    norm_num
  have v3 : b 3 = 104 := by
    have h := hk 1
    rw [show (1 : ℕ) + 2 = 3 from rfl] at h
    rw [h]
    norm_num
  refine ⟨?_, ?_⟩
  · obtain ⟨f, hf⟩ : ∃ f : ℕ → ℚ, ∀ n, f n = if n = 0 then (0 : ℚ) else (a n : ℚ) :=
      ⟨_, fun _ => rfl⟩
    have hfun : (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = f :=
      funext fun n => (hf n).symm
    have f0 : f 0 = 0 := by rw [hf, if_pos (rfl : (0 : ℕ) = 0)]
    have f1 : f 1 = 3 := by
      rw [hf, if_neg (show ¬ ((1 : ℕ) = 0) by norm_num), hb]
      exact_mod_cast v1
    have f2 : f 2 = 10 := by
      rw [hf, if_neg (show ¬ ((2 : ℕ) = 0) by norm_num), hb]
      exact_mod_cast v2
    have f3 : f 3 = 104 := by
      rw [hf, if_neg (show ¬ ((3 : ℕ) = 0) by norm_num), hb]
      exact_mod_cast v3
    have frec : ∀ k, f (k + 4) = 16 * f (k + 3) - 48 * f (k + 2) := by
      intro k
      rw [hf, hf, hf, if_neg (show ¬ (k + 4 = 0) by omega), if_neg (show ¬ (k + 3 = 0) by omega),
        if_neg (show ¬ (k + 2 = 0) by omega)]
      simp only [hb]
      have q4 := hq (k + 2)
      have q3 := hq (k + 1)
      have q2 := hq k
      rw [show k + 2 + 2 = k + 4 by omega] at q4
      rw [show k + 1 + 2 = k + 3 by omega] at q3
      linear_combination q4 - 16 * q3 + 48 * q2
    rw [show PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = PowerSeries.mk f
      from congrArg PowerSeries.mk hfun]
    have e : PowerSeries.mk f * ((1 - 4 * PowerSeries.X) * (1 - 12 * PowerSeries.X)) =
        PowerSeries.mk f
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 16 * (PowerSeries.mk f * PowerSeries.X ^ 1)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 48 * (PowerSeries.mk f * PowerSeries.X ^ 2) := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 16,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 48]
      ring
    have e2 : (PowerSeries.X * (3 - 38 * PowerSeries.X + 88 * PowerSeries.X ^ 2) :
        PowerSeries ℚ) =
        PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3
          - PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 38
          + PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 88 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 38,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 88]
      ring
    rw [e, e2]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n
      · norm_num [f0]
      · norm_num [f0, f1]
      · norm_num [f0, f1, f2]
      · norm_num [f1, f2, f3]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      rw [if_pos (show 1 ≤ k + 4 by omega), if_pos (show 2 ≤ k + 4 by omega),
        if_pos (show 1 ≤ k + 4 by omega), if_pos (show 2 ≤ k + 4 by omega),
        if_pos (show 3 ≤ k + 4 by omega),
        if_neg (show ¬ (k + 4 - 1 = 0) by omega), if_neg (show ¬ (k + 4 - 2 = 0) by omega),
        if_neg (show ¬ (k + 4 - 3 = 0) by omega),
        show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, frec k]
      ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have h := hq k
    have e12 : (12 : ℚ) ^ k = (2 ^ k) ^ 2 * 3 ^ k := by
      rw [sq, ← mul_pow, ← mul_pow]
      norm_num
    have e4 : (4 : ℚ) ^ k = (2 ^ k) ^ 2 := by
      rw [sq, ← mul_pow]
      norm_num
    have e2 : (2 : ℚ) ^ (2 * k + 1) = 2 * (2 ^ k) ^ 2 := by
      rw [pow_succ (2 : ℚ) (2 * k), pow_mul' (2 : ℚ) 2 k]
      ring
    rw [e12, e4] at h
    rw [hb, show 2 * (k + 2) - 3 = 2 * k + 1 by omega, e2, eq_div_iff (by norm_num)]
    linear_combination 9 * h
