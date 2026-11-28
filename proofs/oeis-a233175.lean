import OMAStatements.S_oeis_a233175

-- Problem: A233175: Number of 2 X n 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally, diagonally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabelled 6-colorings with no clashing color pairs).
-- Upstream: formal-conjectures statements/oeis-a233175.lean:0 (declaration OMA.S_oeis_a233175.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: three involutions (1 2)(4 3), (2 3), (1 4) remove the row-major order conditions,
-- giving 8*a(n) = T(n) + 2*U(n) + 5*Z(n) where T, U, Z count arrays without order conditions with
-- entries in 0..5, {0,1,4,5}, {0,5}. Splitting columns by whether the two entries clash gives a
-- 2-state transfer count for each: T satisfies T(m+2) = 8*T(m+1) + 32*T(m), U(k+1) = 8*4^k, and
-- Z(k+1) = 0. Hence 8*a(k+2) = T(k+1) + 16*4^k and a(1) = 3. The g.f. follows by comparing
-- coefficients, and the closed form over ℝ follows by two-step induction with (Real.sqrt 3)^2 = 3.

open OMA.S_oeis_a233175

theorem bef75_lt (n : ℕ) (i i' : Fin 2) (j j' : Fin n)
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
def mapA75 (n : ℕ) (τ : Fin 6 → Fin 6) (x : Fin n → Fin 2 → Fin 6) : Fin n → Fin 2 → Fin 6 :=
  fun j i => τ (x j i)

theorem mapA75_inv (n : ℕ) (τ : Fin 6 → Fin 6) (hτ : ∀ v, τ (τ v) = v)
    (x : Fin n → Fin 2 → Fin 6) : mapA75 n τ (mapA75 n τ x) = x := by
  funext j i
  exact hτ (x j i)

/-- Every entry with V2 has an entry with V1 before it in row major order. -/
def FO75 (n : ℕ) (V1 V2 : Fin 6 → Bool) (x : Fin n → Fin 2 → Fin 6) : Prop :=
  ∀ j : Fin n, ∀ i : Fin 2, V2 (x j i) = true →
    ∃ j' : Fin n, ∃ i' : Fin 2, (i'.val < i.val ∨ (i'.val = i.val ∧ j'.val < j.val)) ∧
      V1 (x j' i') = true

instance (n : ℕ) (V1 V2 : Fin 6 → Bool) (x : Fin n → Fin 2 → Fin 6) :
    Decidable (FO75 n V1 V2 x) := by
  unfold FO75
  infer_instance

/-- No entry has V1 or V2. -/
def NoV75 (n : ℕ) (V1 V2 : Fin 6 → Bool) (x : Fin n → Fin 2 → Fin 6) : Prop :=
  ∀ j : Fin n, ∀ i : Fin 2, V1 (x j i) = false ∧ V2 (x j i) = false

instance (n : ℕ) (V1 V2 : Fin 6 → Bool) (x : Fin n → Fin 2 → Fin 6) :
    Decidable (NoV75 n V1 V2 x) := by
  unfold NoV75
  infer_instance

theorem FO75_or (n : ℕ) (V1 V2 : Fin 6 → Bool) (τ : Fin 6 → Fin 6)
    (h12 : ∀ v, V1 (τ v) = V2 v) (h21 : ∀ v, V2 (τ v) = V1 v)
    (hdisj : ∀ v, V1 v = true → V2 v = true → False)
    (x : Fin n → Fin 2 → Fin 6) : FO75 n V1 V2 x ∨ FO75 n V1 V2 (mapA75 n τ x) := by
  by_contra hc
  have h1 : ¬ FO75 n V1 V2 x := fun h => hc (Or.inl h)
  have h2 : ¬ FO75 n V1 V2 (mapA75 n τ x) := fun h => hc (Or.inr h)
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

theorem FO75_both (n : ℕ) (V1 V2 : Fin 6 → Bool) (τ : Fin 6 → Fin 6)
    (h12 : ∀ v, V1 (τ v) = V2 v) (h21 : ∀ v, V2 (τ v) = V1 v)
    (x : Fin n → Fin 2 → Fin 6) (h1 : FO75 n V1 V2 x) (h2 : FO75 n V1 V2 (mapA75 n τ x)) :
    NoV75 n V1 V2 x := by
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
          (Nat.lt_of_lt_of_le (bef75_lt n i i' j j' hb) (Nat.le_of_lt_succ hm))).2.symm.trans hv)
      · rw [Bool.eq_false_iff]
        intro hx
        obtain ⟨j', i', hb, hx'⟩ := h1 j i hx
        exact Bool.false_ne_true ((ih j' i'
          (Nat.lt_of_lt_of_le (bef75_lt n i i' j j' hb) (Nat.le_of_lt_succ hm))).1.symm.trans hx')
  intro j i
  exact key _ j i (Nat.lt_succ_self _)

theorem FO75_map (n : ℕ) (V1 V2 : Fin 6 → Bool) (τ : Fin 6 → Fin 6)
    (hp1 : ∀ v, V1 (τ v) = V1 v) (hp2 : ∀ v, V2 (τ v) = V2 v) (x : Fin n → Fin 2 → Fin 6) :
    FO75 n V1 V2 (mapA75 n τ x) ↔ FO75 n V1 V2 x := by
  constructor
  · intro h j i hx
    obtain ⟨j', i', hb, hx'⟩ := h j i ((hp2 (x j i)).trans hx)
    exact ⟨j', i', hb, (hp1 (x j' i')).symm.trans hx'⟩
  · intro h j i hx
    obtain ⟨j', i', hb, hx'⟩ := h j i ((hp2 (x j i)).symm.trans hx)
    exact ⟨j', i', hb, (hp1 (x j' i')).trans hx'⟩

/-- The involution argument: 2 N(FO) = |S| + N(no V1, V2). -/
theorem twiceFO75 (n : ℕ) (V1 V2 : Fin 6 → Bool) (τ : Fin 6 → Fin 6) (hτ : ∀ v, τ (τ v) = v)
    (h12 : ∀ v, V1 (τ v) = V2 v) (h21 : ∀ v, V2 (τ v) = V1 v)
    (hdisj : ∀ v, V1 v = true → V2 v = true → False)
    (hfix : ∀ v, V1 v = false → V2 v = false → τ v = v)
    (S : Finset (Fin n → Fin 2 → Fin 6)) (hS : ∀ x, x ∈ S → mapA75 n τ x ∈ S) :
    2 * (S.filter (FO75 n V1 V2)).card = S.card + (S.filter (NoV75 n V1 V2)).card := by
  have hinj : Function.Injective (mapA75 n τ) := by
    intro x y hxy
    rw [← mapA75_inv n τ hτ x, hxy, mapA75_inv n τ hτ y]
  have hI : ((S.filter (FO75 n V1 V2)).image (mapA75 n τ)).card = (S.filter (FO75 n V1 V2)).card :=
    Finset.card_image_of_injective _ hinj
  have memI : ∀ y, y ∈ (S.filter (FO75 n V1 V2)).image (mapA75 n τ) ↔
      y ∈ S ∧ FO75 n V1 V2 (mapA75 n τ y) := by
    intro y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Finset.mem_filter] at hx
      rw [mapA75_inv n τ hτ]
      exact ⟨hS x hx.1, hx.2⟩
    · rintro ⟨hy, hf⟩
      exact ⟨mapA75 n τ y, Finset.mem_filter.2 ⟨hS y hy, hf⟩, mapA75_inv n τ hτ y⟩
  have hU : S.filter (FO75 n V1 V2) ∪ (S.filter (FO75 n V1 V2)).image (mapA75 n τ) = S := by
    ext y
    rw [Finset.mem_union, memI, Finset.mem_filter]
    constructor
    · rintro (⟨hy, -⟩ | ⟨hy, -⟩)
      · exact hy
      · exact hy
    · intro hy
      rcases FO75_or n V1 V2 τ h12 h21 hdisj y with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
  have hN : S.filter (FO75 n V1 V2) ∩ (S.filter (FO75 n V1 V2)).image (mapA75 n τ) =
      S.filter (NoV75 n V1 V2) := by
    ext y
    rw [Finset.mem_inter, memI, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hy, h1⟩, -, h2⟩
      exact ⟨hy, FO75_both n V1 V2 τ h12 h21 y h1 h2⟩
    · rintro ⟨hy, hz⟩
      have hf : FO75 n V1 V2 y := fun j i hx => (Bool.false_ne_true ((hz j i).2.symm.trans hx)).elim
      have hs : mapA75 n τ y = y := by
        funext j i
        exact hfix (y j i) (hz j i).1 (hz j i).2
      refine ⟨⟨hy, hf⟩, hy, ?_⟩
      rw [hs]
      exact hf
  have hc := Finset.card_union_add_card_inter (S.filter (FO75 n V1 V2))
    ((S.filter (FO75 n V1 V2)).image (mapA75 n τ))
  rw [hU, hN, hI] at hc
  omega

theorem noClash_map75 (n : ℕ) (τ : Fin 6 → Fin 6) (hcl : ∀ u v, clash (τ u) (τ v) ↔ clash u v)
    (x : Fin n → Fin 2 → Fin 6) : noClash n (mapA75 n τ x) ↔ noClash n x := by
  constructor
  · intro h j k hk
    obtain ⟨h1, h2, h3⟩ := h j k hk
    exact ⟨fun i hc => h1 i ((hcl (x j i) (x k i)).2 hc),
      fun hc => h2 ((hcl (x j 0) (x k 1)).2 hc),
      fun hc => h3 ((hcl (x j 1) (x k 0)).2 hc)⟩
  · intro h j k hk
    obtain ⟨h1, h2, h3⟩ := h j k hk
    exact ⟨fun i hc => h1 i ((hcl (x j i) (x k i)).1 hc),
      fun hc => h2 ((hcl (x j 0) (x k 1)).1 hc),
      fun hc => h3 ((hcl (x j 1) (x k 0)).1 hc)⟩

theorem tl_map75 (n : ℕ) (τ : Fin 6 → Fin 6) (h0 : ∀ v, τ v = 0 ↔ v = 0)
    (x : Fin n → Fin 2 → Fin 6) : topLeftZero n (mapA75 n τ x) ↔ topLeftZero n x := by
  constructor
  · intro h j hj
    exact (h0 (x j 0)).1 (h j hj)
  · intro h j hj
    exact (h0 (x j 0)).2 (h j hj)

/-- The value sets and maps of the three involution steps. -/
def p1_75 (v : Fin 6) : Bool := decide (v = 1)
def p4_75 (v : Fin 6) : Bool := decide (v = 4)
def p2_75 (v : Fin 6) : Bool := decide (v = 2)
def p3_75 (v : Fin 6) : Bool := decide (v = 3)
def p14_75 (v : Fin 6) : Bool := decide (v = 1 ∨ v = 4)
def p23_75 (v : Fin 6) : Bool := decide (v = 2 ∨ v = 3)
def tA75 (v : Fin 6) : Fin 6 := if v = 1 then 4 else if v = 4 then 1 else v
def tB75 (v : Fin 6) : Fin 6 := if v = 2 then 3 else if v = 3 then 2 else v
def tC75 (v : Fin 6) : Fin 6 :=
  if v = 1 then 2 else if v = 2 then 1 else if v = 3 then 4 else if v = 4 then 3 else v

theorem tA75_inv : ∀ v, tA75 (tA75 v) = v := by decide
theorem tB75_inv : ∀ v, tB75 (tB75 v) = v := by decide
theorem tC75_inv : ∀ v, tC75 (tC75 v) = v := by decide
theorem tA75_cl : ∀ u v, clash (tA75 u) (tA75 v) ↔ clash u v := by decide
theorem tB75_cl : ∀ u v, clash (tB75 u) (tB75 v) ↔ clash u v := by decide
theorem tC75_cl : ∀ u v, clash (tC75 u) (tC75 v) ↔ clash u v := by decide
theorem tA75_0 : ∀ v, tA75 v = 0 ↔ v = 0 := by decide
theorem tB75_0 : ∀ v, tB75 v = 0 ↔ v = 0 := by decide
theorem tC75_0 : ∀ v, tC75 v = 0 ↔ v = 0 := by decide
theorem tA75_12 : ∀ v, p1_75 (tA75 v) = p4_75 v := by decide
theorem tA75_21 : ∀ v, p4_75 (tA75 v) = p1_75 v := by decide
theorem tB75_12 : ∀ v, p2_75 (tB75 v) = p3_75 v := by decide
theorem tB75_21 : ∀ v, p3_75 (tB75 v) = p2_75 v := by decide
theorem tC75_12 : ∀ v, p14_75 (tC75 v) = p23_75 v := by decide
theorem tC75_21 : ∀ v, p23_75 (tC75 v) = p14_75 v := by decide
theorem dA75 : ∀ v, p1_75 v = true → p4_75 v = true → False := by decide
theorem dB75 : ∀ v, p2_75 v = true → p3_75 v = true → False := by decide
theorem dC75 : ∀ v, p14_75 v = true → p23_75 v = true → False := by decide
theorem fA75 : ∀ v, p1_75 v = false → p4_75 v = false → tA75 v = v := by decide
theorem fB75 : ∀ v, p2_75 v = false → p3_75 v = false → tB75 v = v := by decide
theorem fC75 : ∀ v, p14_75 v = false → p23_75 v = false → tC75 v = v := by decide
theorem tA75_p14 : ∀ v, p14_75 (tA75 v) = p14_75 v := by decide
theorem tA75_p23 : ∀ v, p23_75 (tA75 v) = p23_75 v := by decide
theorem tA75_p2 : ∀ v, p2_75 (tA75 v) = p2_75 v := by decide
theorem tA75_p3 : ∀ v, p3_75 (tA75 v) = p3_75 v := by decide
theorem tB75_p14 : ∀ v, p14_75 (tB75 v) = p14_75 v := by decide
theorem tB75_p23 : ∀ v, p23_75 (tB75 v) = p23_75 v := by decide
theorem oU75 : ∀ v, p2_75 v = false → p3_75 v = false → p23_75 v = false := by decide
theorem oZ1_75 : ∀ v, p1_75 v = false → p4_75 v = false → p14_75 v = false := by decide
theorem oZ2_75 : ∀ v, p23_75 v = false → p3_75 v = false := by decide
theorem oZ3_75 : ∀ v, p14_75 v = false → p1_75 v = false := by decide
theorem oZ4_75 : ∀ v, p14_75 v = false → p4_75 v = false := by decide

/-- The arrays without the order conditions. -/
def T75 (n : ℕ) : Finset (Fin n → Fin 2 → Fin 6) :=
  Finset.univ.filter (fun x => noClash n x ∧ topLeftZero n x)

def N1_75 (n : ℕ) : Finset (Fin n → Fin 2 → Fin 6) := (T75 n).filter (FO75 n p14_75 p23_75)

def N13_75 (n : ℕ) : Finset (Fin n → Fin 2 → Fin 6) := (N1_75 n).filter (FO75 n p2_75 p3_75)

/-- Those with values in {0, 1, 4, 5}. -/
def U75 (n : ℕ) : Finset (Fin n → Fin 2 → Fin 6) := (T75 n).filter (NoV75 n p2_75 p3_75)

/-- Those with values in {0, 5}. -/
def Z75 (n : ℕ) : Finset (Fin n → Fin 2 → Fin 6) := (T75 n).filter (NoV75 n p14_75 p23_75)

theorem memT75 (n : ℕ) (x : Fin n → Fin 2 → Fin 6) :
    x ∈ T75 n ↔ noClash n x ∧ topLeftZero n x := by
  unfold T75
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem memN1_75 (n : ℕ) (x : Fin n → Fin 2 → Fin 6) :
    x ∈ N1_75 n ↔ x ∈ T75 n ∧ FO75 n p14_75 p23_75 x := by
  unfold N1_75
  exact Finset.mem_filter

theorem memN13_75 (n : ℕ) (x : Fin n → Fin 2 → Fin 6) :
    x ∈ N13_75 n ↔ x ∈ N1_75 n ∧ FO75 n p2_75 p3_75 x := by
  unfold N13_75
  exact Finset.mem_filter

theorem mapT75 (n : ℕ) (τ : Fin 6 → Fin 6) (hcl : ∀ u v, clash (τ u) (τ v) ↔ clash u v)
    (h0 : ∀ v, τ v = 0 ↔ v = 0) (x : Fin n → Fin 2 → Fin 6) (hx : x ∈ T75 n) :
    mapA75 n τ x ∈ T75 n := by
  rw [memT75] at hx ⊢
  exact ⟨(noClash_map75 n τ hcl x).2 hx.1, (tl_map75 n τ h0 x).2 hx.2⟩

theorem twoB_iff75 (n : ℕ) (x : Fin n → Fin 2 → Fin 6) :
    twoBeforeThree n x ↔ FO75 n p2_75 p3_75 x := by
  constructor
  · intro h j i hx
    obtain ⟨j', i', hb, hx'⟩ := h j i (of_decide_eq_true hx)
    exact ⟨j', i', hb, decide_eq_true hx'⟩
  · intro h j i hx
    obtain ⟨j', i', hb, hx'⟩ := h j i (decide_eq_true hx)
    exact ⟨j', i', hb, of_decide_eq_true hx'⟩

theorem oneFirst_iff75 (n : ℕ) (x : Fin n → Fin 2 → Fin 6) :
    oneFirst n x ↔ FO75 n p14_75 p23_75 x ∧ FO75 n p1_75 p4_75 x := by
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

theorem a_eq75 (n : ℕ) : a n = ((N13_75 n).filter (FO75 n p1_75 p4_75)).card := by
  have hA : a n = ((Finset.univ : Finset (Fin n → Fin 2 → Fin 6)).filter
      (fun x => noClash n x ∧ topLeftZero n x ∧ oneFirst n x ∧ twoBeforeThree n x)).card := rfl
  have e : (Finset.univ : Finset (Fin n → Fin 2 → Fin 6)).filter
      (fun x => noClash n x ∧ topLeftZero n x ∧ oneFirst n x ∧ twoBeforeThree n x) =
      (N13_75 n).filter (FO75 n p1_75 p4_75) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, memN13_75, memN1_75, memT75, oneFirst_iff75,
      twoB_iff75]
    constructor
    · rintro ⟨-, h1, h2, ⟨h3, h4⟩, h5⟩
      exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h5⟩, h4⟩
    · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h5⟩, h4⟩
      exact ⟨Finset.mem_univ _, h1, h2, ⟨h3, h4⟩, h5⟩
  rw [hA, e]

theorem count75 (n : ℕ) : 8 * a n = (T75 n).card + 2 * (U75 n).card + 5 * (Z75 n).card := by
  have hA := a_eq75 n
  have hStA : 2 * ((N13_75 n).filter (FO75 n p1_75 p4_75)).card =
      (N13_75 n).card + ((N13_75 n).filter (NoV75 n p1_75 p4_75)).card := by
    refine twiceFO75 n p1_75 p4_75 tA75 tA75_inv tA75_12 tA75_21 dA75 fA75 (N13_75 n) ?_
    intro x hx
    rw [memN13_75, memN1_75] at hx ⊢
    exact ⟨⟨mapT75 n tA75 tA75_cl tA75_0 x hx.1.1,
      (FO75_map n p14_75 p23_75 tA75 tA75_p14 tA75_p23 x).2 hx.1.2⟩,
      (FO75_map n p2_75 p3_75 tA75 tA75_p2 tA75_p3 x).2 hx.2⟩
  have hStB : 2 * (N13_75 n).card = (N1_75 n).card + ((N1_75 n).filter (NoV75 n p2_75 p3_75)).card := by
    refine twiceFO75 n p2_75 p3_75 tB75 tB75_inv tB75_12 tB75_21 dB75 fB75 (N1_75 n) ?_
    intro x hx
    rw [memN1_75] at hx ⊢
    exact ⟨mapT75 n tB75 tB75_cl tB75_0 x hx.1,
      (FO75_map n p14_75 p23_75 tB75 tB75_p14 tB75_p23 x).2 hx.2⟩
  have hStC : 2 * (N1_75 n).card = (T75 n).card + (Z75 n).card :=
    twiceFO75 n p14_75 p23_75 tC75 tC75_inv tC75_12 tC75_21 dC75 fC75 (T75 n)
      (fun x hx => mapT75 n tC75 tC75_cl tC75_0 x hx)
  have eU : (N1_75 n).filter (NoV75 n p2_75 p3_75) = U75 n := by
    ext x
    unfold U75
    rw [Finset.mem_filter, Finset.mem_filter, memN1_75]
    constructor
    · rintro ⟨⟨hT, -⟩, hN⟩
      exact ⟨hT, hN⟩
    · rintro ⟨hT, hN⟩
      refine ⟨⟨hT, fun j i hv => ?_⟩, hN⟩
      exact (Bool.false_ne_true ((oU75 _ (hN j i).1 (hN j i).2).symm.trans hv)).elim
  have eZ : (N13_75 n).filter (NoV75 n p1_75 p4_75) = Z75 n := by
    ext x
    unfold Z75
    rw [Finset.mem_filter, Finset.mem_filter, memN13_75, memN1_75]
    constructor
    · rintro ⟨⟨⟨hT, hC⟩, -⟩, hN⟩
      refine ⟨hT, fun j i => ⟨oZ1_75 _ (hN j i).1 (hN j i).2, ?_⟩⟩
      rw [Bool.eq_false_iff]
      intro hv
      obtain ⟨j', i', -, hv'⟩ := hC j i hv
      exact Bool.false_ne_true ((oZ1_75 _ (hN j' i').1 (hN j' i').2).symm.trans hv')
    · rintro ⟨hT, hN⟩
      refine ⟨⟨⟨hT, fun j i hv => ?_⟩, fun j i hv => ?_⟩, fun j i => ⟨?_, ?_⟩⟩
      · exact (Bool.false_ne_true ((hN j i).2.symm.trans hv)).elim
      · exact (Bool.false_ne_true ((oZ2_75 _ (hN j i).2).symm.trans hv)).elim
      · exact oZ3_75 _ (hN j i).1
      · exact oZ4_75 _ (hN j i).1
  rw [eU] at hStB
  rw [eZ] at hStA
  omega

/-- Arrays of m+1 columns (each column a pair: top, bottom) whose first column satisfies F,
whose columns all satisfy K, and whose consecutive columns satisfy R. -/
def W75 (R : Fin 6 × Fin 6 → Fin 6 × Fin 6 → Bool) (F K : Fin 6 × Fin 6 → Bool) (m : ℕ) :
    Finset (Fin (m + 1) → Fin 6 × Fin 6) :=
  Finset.univ.filter (fun y => F (y ⟨0, Nat.succ_pos m⟩) = true ∧ (∀ j, K (y j) = true) ∧
    ∀ j : Fin m, R (y j.castSucc) (y j.succ) = true)

theorem memW75 (R : Fin 6 × Fin 6 → Fin 6 × Fin 6 → Bool) (F K : Fin 6 × Fin 6 → Bool) (m : ℕ)
    (y : Fin (m + 1) → Fin 6 × Fin 6) :
    y ∈ W75 R F K m ↔ F (y ⟨0, Nat.succ_pos m⟩) = true ∧ (∀ j, K (y j) = true) ∧
      ∀ j : Fin m, R (y j.castSucc) (y j.succ) = true := by
  unfold W75
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem memW75_snoc (R : Fin 6 × Fin 6 → Fin 6 × Fin 6 → Bool) (F K : Fin 6 × Fin 6 → Bool)
    (m : ℕ) (t : Fin (m + 1) → Fin 6 × Fin 6) (c : Fin 6 × Fin 6) :
    (Fin.snoc t c : Fin (m + 1 + 1) → Fin 6 × Fin 6) ∈ W75 R F K (m + 1) ↔
      t ∈ W75 R F K m ∧ K c = true ∧ R (t (Fin.last m)) c = true := by
  rw [memW75, memW75]
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
theorem stepW75 (R : Fin 6 × Fin 6 → Fin 6 × Fin 6 → Bool) (F K P : Fin 6 × Fin 6 → Bool)
    (m : ℕ) :
    ((W75 R F K (m + 1)).filter (fun y => P (y (Fin.last (m + 1))) = true)).card =
      ∑ t ∈ W75 R F K m, (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
        K c = true ∧ R (t (Fin.last m)) c = true ∧ P c = true)).card := by
  have H : (((W75 R F K (m + 1)).filter (fun y => P (y (Fin.last (m + 1))) = true) :
      Finset (Fin (m + 1 + 1) → Fin 6 × Fin 6)) : Set (Fin (m + 1 + 1) → Fin 6 × Fin 6)).MapsTo
      (fun y : Fin (m + 1 + 1) → Fin 6 × Fin 6 => Fin.init y)
      ((W75 R F K m : Finset (Fin (m + 1) → Fin 6 × Fin 6)) :
        Set (Fin (m + 1) → Fin 6 × Fin 6)) := by
    intro y hy
    have hy1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).1
    have e : y = (Fin.snoc (Fin.init y) (y (Fin.last (m + 1))) :
        Fin (m + 1 + 1) → Fin 6 × Fin 6) := (Fin.snoc_init_self y).symm
    rw [e, memW75_snoc] at hy1
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
    rw [e, memW75_snoc] at hyW
    obtain ⟨-, hK, hR⟩ := hyW
    rw [hyt] at hR
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hK, hR, hP⟩)
  · intro c hc
    obtain ⟨hK, hR, hP⟩ := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
    have hW := (memW75_snoc R F K m t c).2 ⟨ht, hK, hR⟩
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
theorem baseW75 (R : Fin 6 × Fin 6 → Fin 6 × Fin 6 → Bool) (F K P : Fin 6 × Fin 6 → Bool) :
    ((W75 R F K 0).filter (fun y => P (y (Fin.last 0)) = true)).card =
      (Finset.univ.filter (fun c : Fin 6 × Fin 6 => F c = true ∧ K c = true ∧ P c = true)).card := by
  apply Finset.card_nbij' (fun y : Fin (0 + 1) → Fin 6 × Fin 6 => y (Fin.last 0))
    (fun c : Fin 6 × Fin 6 => fun _ : Fin (0 + 1) => c)
  · intro y hy
    have hy' := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
    obtain ⟨hF, hK, -⟩ := (memW75 R F K 0 y).1 hy'.1
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hF, hK _, hy'.2⟩)
  · intro c hc
    obtain ⟨hF, hK, hP⟩ := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
    exact Finset.mem_coe.2 (Finset.mem_filter.2
      ⟨(memW75 R F K 0 _).2 ⟨hF, fun _ => hK, fun j => j.elim0⟩, hP⟩)
  · intro y _
    funext j
    show y (Fin.last 0) = y j
    have hj : j = Fin.last 0 := Fin.ext (by have := j.isLt; rw [Fin.val_last]; omega)
    rw [hj]
  · intro c _
    rfl

/-- The transfer step when the weights depend only on whether Q holds at the last column. -/
theorem classStep75 (R : Fin 6 × Fin 6 → Fin 6 × Fin 6 → Bool) (F K P Q : Fin 6 × Fin 6 → Bool)
    (wa wb m : ℕ)
    (hw : ∀ d : Fin 6 × Fin 6, K d = true →
      (Finset.univ.filter (fun c : Fin 6 × Fin 6 => K c = true ∧ R d c = true ∧ P c = true)).card =
        if Q d = true then wa else wb) :
    ((W75 R F K (m + 1)).filter (fun y => P (y (Fin.last (m + 1))) = true)).card =
      ((W75 R F K m).filter (fun y => Q (y (Fin.last m)) = true)).card * wa +
        ((W75 R F K m).filter (fun y => ¬ (Q (y (Fin.last m)) = true))).card * wb := by
  rw [stepW75]
  have e : ∀ t ∈ W75 R F K m,
      (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
        K c = true ∧ R (t (Fin.last m)) c = true ∧ P c = true)).card =
        if Q (t (Fin.last m)) = true then wa else wb :=
    fun t ht => hw (t (Fin.last m)) (((memW75 R F K m t).1 ht).2.1 (Fin.last m))
  rw [Finset.sum_congr rfl e, Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul,
    smul_eq_mul]

/-- The columns of an array, as pairs (top, bottom). -/
def toP75 (n : ℕ) (x : Fin n → Fin 2 → Fin 6) : Fin n → Fin 6 × Fin 6 := fun j => (x j 0, x j 1)

theorem card_toP75 (n : ℕ) (S : Finset (Fin n → Fin 6 × Fin 6)) :
    (Finset.univ.filter (fun x : Fin n → Fin 2 → Fin 6 => toP75 n x ∈ S)).card = S.card := by
  apply Finset.card_nbij' (toP75 n)
    (fun y : Fin n → Fin 6 × Fin 6 => fun j i => if i = 0 then (y j).1 else (y j).2)
  · intro x hx
    exact Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
  · intro y hy
    have e : toP75 n (fun j i => if i = 0 then (y j).1 else (y j).2) = y := by
      funext j
      show ((if (0 : Fin 2) = 0 then (y j).1 else (y j).2),
        (if (1 : Fin 2) = 0 then (y j).1 else (y j).2)) = y j
      have e0 : (if (0 : Fin 2) = 0 then (y j).1 else (y j).2) = (y j).1 := if_pos rfl
      have e1 : (if (1 : Fin 2) = 0 then (y j).1 else (y j).2) = (y j).2 :=
        if_neg (show ¬ ((1 : Fin 2) = 0) by decide)
      exact (congrArg₂ Prod.mk e0 e1).trans Prod.mk.eta
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    show toP75 n (fun j i => if i = 0 then (y j).1 else (y j).2) ∈ S
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
def R75 (d c : Fin 6 × Fin 6) : Bool :=
  decide (¬ clash d.1 c.1 ∧ ¬ clash d.2 c.2 ∧ ¬ clash d.1 c.2 ∧ ¬ clash d.2 c.1)

/-- The first column has top element zero. -/
def F75 (c : Fin 6 × Fin 6) : Bool := decide (c.1 = 0)

/-- No condition on the columns. -/
def KT75 (_c : Fin 6 × Fin 6) : Bool := true

/-- The column has no entry 2 or 3. -/
def KU75 (c : Fin 6 × Fin 6) : Bool :=
  decide ((p2_75 c.1 = false ∧ p3_75 c.1 = false) ∧ (p2_75 c.2 = false ∧ p3_75 c.2 = false))

/-- The column has entries in {0, 5} only. -/
def KZ75 (c : Fin 6 × Fin 6) : Bool :=
  decide ((p14_75 c.1 = false ∧ p23_75 c.1 = false) ∧ (p14_75 c.2 = false ∧ p23_75 c.2 = false))

/-- The two entries of the column clash (lie in the same pair). -/
def QS75 (c : Fin 6 × Fin 6) : Bool := decide (clash c.1 c.2)

/-- They do not. -/
def QN75 (c : Fin 6 × Fin 6) : Bool := decide (¬ clash c.1 c.2)

theorem nc_iff75 (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 6) :
    noClash (m + 1) x ↔
      ∀ j : Fin m, R75 (toP75 (m + 1) x j.castSucc) (toP75 (m + 1) x j.succ) = true := by
  constructor
  · intro h j
    obtain ⟨h1, h2, h3⟩ := h j.castSucc j.succ rfl
    unfold R75
    exact decide_eq_true ⟨h1 0, h1 1, h2, h3⟩
  · intro h j k hk
    have hj : j.val < m := by
      have := k.isLt
      omega
    have e1 : (⟨j.val, hj⟩ : Fin m).castSucc = j := Fin.ext rfl
    have e2 : (⟨j.val, hj⟩ : Fin m).succ = k := Fin.ext (by rw [Fin.val_succ]; exact hk.symm)
    have h' := of_decide_eq_true (h ⟨j.val, hj⟩)
    rw [e1, e2] at h'
    obtain ⟨h1, h2, h3, h4⟩ := h'
    exact ⟨Fin.forall_fin_two.2 ⟨h1, h2⟩, h3, h4⟩

theorem tl_iff75 (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 6) :
    topLeftZero (m + 1) x ↔ F75 (toP75 (m + 1) x ⟨0, Nat.succ_pos m⟩) = true := by
  constructor
  · intro h
    unfold F75
    exact decide_eq_true (h ⟨0, Nat.succ_pos m⟩ rfl)
  · intro h j hj
    have e : j = ⟨0, Nat.succ_pos m⟩ := Fin.ext hj
    rw [e]
    exact of_decide_eq_true h

theorem kp75 (K : Fin 6 × Fin 6 → Bool) (P : Fin 6 → Prop)
    (hK : ∀ p q : Fin 6, K (p, q) = true ↔ (P p ∧ P q)) (m : ℕ)
    (x : Fin (m + 1) → Fin 2 → Fin 6) :
    (∀ j : Fin (m + 1), ∀ i : Fin 2, P (x j i)) ↔ ∀ j, K (toP75 (m + 1) x j) = true := by
  constructor
  · intro h j
    exact (hK (x j 0) (x j 1)).2 ⟨h j 0, h j 1⟩
  · intro h j
    exact Fin.forall_fin_two.2 ((hK (x j 0) (x j 1)).1 (h j))

theorem hKU75 : ∀ p q : Fin 6, KU75 (p, q) = true ↔
    ((p2_75 p = false ∧ p3_75 p = false) ∧ (p2_75 q = false ∧ p3_75 q = false)) := by
  intro p q
  unfold KU75
  exact ⟨of_decide_eq_true, decide_eq_true⟩

theorem hKZ75 : ∀ p q : Fin 6, KZ75 (p, q) = true ↔
    ((p14_75 p = false ∧ p23_75 p = false) ∧ (p14_75 q = false ∧ p23_75 q = false)) := by
  intro p q
  unfold KZ75
  exact ⟨of_decide_eq_true, decide_eq_true⟩

theorem cardT75 (m : ℕ) : (T75 (m + 1)).card = (W75 R75 F75 KT75 m).card := by
  have e : T75 (m + 1) = Finset.univ.filter
      (fun x : Fin (m + 1) → Fin 2 → Fin 6 => toP75 (m + 1) x ∈ W75 R75 F75 KT75 m) := by
    ext x
    rw [memT75, Finset.mem_filter, memW75, nc_iff75, tl_iff75]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨Finset.mem_univ _, h2, fun _ => rfl, h1⟩
    · rintro ⟨-, h2, -, h1⟩
      exact ⟨h1, h2⟩
  rw [e, card_toP75]

theorem cardU75 (m : ℕ) : (U75 (m + 1)).card = (W75 R75 F75 KU75 m).card := by
  have e : U75 (m + 1) = Finset.univ.filter
      (fun x : Fin (m + 1) → Fin 2 → Fin 6 => toP75 (m + 1) x ∈ W75 R75 F75 KU75 m) := by
    ext x
    unfold U75
    rw [Finset.mem_filter, Finset.mem_filter, memT75, memW75, nc_iff75, tl_iff75]
    have hk := kp75 KU75 (fun v => p2_75 v = false ∧ p3_75 v = false) hKU75 m x
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨Finset.mem_univ _, h2, hk.1 h3, h1⟩
    · rintro ⟨-, h2, h3, h1⟩
      exact ⟨⟨h1, h2⟩, hk.2 h3⟩
  rw [e, card_toP75]

theorem cardZ75 (m : ℕ) : (Z75 (m + 1)).card = (W75 R75 F75 KZ75 m).card := by
  have e : Z75 (m + 1) = Finset.univ.filter
      (fun x : Fin (m + 1) → Fin 2 → Fin 6 => toP75 (m + 1) x ∈ W75 R75 F75 KZ75 m) := by
    ext x
    unfold Z75
    rw [Finset.mem_filter, Finset.mem_filter, memT75, memW75, nc_iff75, tl_iff75]
    have hk := kp75 KZ75 (fun v => p14_75 v = false ∧ p23_75 v = false) hKZ75 m x
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨Finset.mem_univ _, h2, hk.1 h3, h1⟩
    · rintro ⟨-, h2, h3, h1⟩
      exact ⟨⟨h1, h2⟩, hk.2 h3⟩
  rw [e, card_toP75]

theorem wTs75 : ∀ d : Fin 6 × Fin 6, KT75 d = true →
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      KT75 c = true ∧ R75 d c = true ∧ QS75 c = true)).card = if QS75 d = true then 8 else 4 := by
  decide +kernel

theorem wTn75 : ∀ d : Fin 6 × Fin 6, KT75 d = true →
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      KT75 c = true ∧ R75 d c = true ∧ QN75 c = true)).card = if QS75 d = true then 8 else 0 := by
  decide +kernel

theorem wUs75 : ∀ d : Fin 6 × Fin 6, KU75 d = true →
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      KU75 c = true ∧ R75 d c = true ∧ QS75 c = true)).card = if QS75 d = true then 4 else 0 := by
  decide +kernel

theorem wUn75 : ∀ d : Fin 6 × Fin 6, KU75 d = true →
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      KU75 c = true ∧ R75 d c = true ∧ QN75 c = true)).card = if QS75 d = true then 0 else 0 := by
  decide +kernel

theorem wZs75 : ∀ d : Fin 6 × Fin 6, KZ75 d = true →
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      KZ75 c = true ∧ R75 d c = true ∧ QS75 c = true)).card = if QS75 d = true then 0 else 0 := by
  decide +kernel

theorem wZn75 : ∀ d : Fin 6 × Fin 6, KZ75 d = true →
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      KZ75 c = true ∧ R75 d c = true ∧ QN75 c = true)).card = if QS75 d = true then 0 else 0 := by
  decide +kernel

theorem bases75 :
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      F75 c = true ∧ KT75 c = true ∧ QS75 c = true)).card = 2 ∧
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      F75 c = true ∧ KT75 c = true ∧ QN75 c = true)).card = 4 ∧
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      F75 c = true ∧ KU75 c = true ∧ QS75 c = true)).card = 2 ∧
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      F75 c = true ∧ KU75 c = true ∧ QN75 c = true)).card = 2 ∧
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      F75 c = true ∧ KZ75 c = true ∧ QS75 c = true)).card = 2 ∧
    (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
      F75 c = true ∧ KZ75 c = true ∧ QN75 c = true)).card = 0 := by
  decide +kernel

theorem qn75 : ∀ c : Fin 6 × Fin 6, QN75 c = true ↔ ¬ (QS75 c = true) := by
  decide

theorem filtNeg75 (K : Fin 6 × Fin 6 → Bool) (m : ℕ) :
    (W75 R75 F75 K m).filter (fun y => ¬ (QS75 (y (Fin.last m)) = true)) =
      (W75 R75 F75 K m).filter (fun y => QN75 (y (Fin.last m)) = true) :=
  Finset.filter_congr (fun y _ => (qn75 (y (Fin.last m))).symm)

theorem steps75 (K : Fin 6 × Fin 6 → Bool) (m : ℕ) (e1 e2 n1 n2 : ℕ)
    (hwe : ∀ d : Fin 6 × Fin 6, K d = true →
      (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
        K c = true ∧ R75 d c = true ∧ QS75 c = true)).card = if QS75 d = true then e1 else e2)
    (hwn : ∀ d : Fin 6 × Fin 6, K d = true →
      (Finset.univ.filter (fun c : Fin 6 × Fin 6 =>
        K c = true ∧ R75 d c = true ∧ QN75 c = true)).card = if QS75 d = true then n1 else n2) :
    ((W75 R75 F75 K (m + 1)).filter (fun y => QS75 (y (Fin.last (m + 1))) = true)).card =
      ((W75 R75 F75 K m).filter (fun y => QS75 (y (Fin.last m)) = true)).card * e1 +
        ((W75 R75 F75 K m).filter (fun y => ¬ (QS75 (y (Fin.last m)) = true))).card * e2 ∧
    ((W75 R75 F75 K (m + 1)).filter (fun y => ¬ (QS75 (y (Fin.last (m + 1))) = true))).card =
      ((W75 R75 F75 K m).filter (fun y => QS75 (y (Fin.last m)) = true)).card * n1 +
        ((W75 R75 F75 K m).filter (fun y => ¬ (QS75 (y (Fin.last m)) = true))).card * n2 := by
  refine ⟨classStep75 R75 F75 K QS75 QS75 e1 e2 m hwe, ?_⟩
  rw [filtNeg75 K (m + 1)]
  exact classStep75 R75 F75 K QN75 QS75 n1 n2 m hwn

theorem closedT75 (T : ℕ → ℕ) (h1 : T 1 = 48) (h2 : T 2 = 576)
    (hrec : ∀ m, T (m + 2) = 8 * T (m + 1) + 32 * T m) :
    ∀ k : ℕ, (T (k + 1) : ℝ) = (1 / 4 : ℝ) * Real.sqrt 3 *
      (-((4 - 4 * Real.sqrt 3) ^ (k + 2)) + (4 * (1 + Real.sqrt 3)) ^ (k + 2)) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr1 : (4 * (1 + Real.sqrt 3)) ^ 2 = 8 * (4 * (1 + Real.sqrt 3)) + 32 := by
    linear_combination 16 * hs
  have hr2 : (4 - 4 * Real.sqrt 3) ^ 2 = 8 * (4 - 4 * Real.sqrt 3) + 32 := by
    linear_combination 16 * hs
  have hpair : ∀ k : ℕ,
      (T (k + 1) : ℝ) = (1 / 4 : ℝ) * Real.sqrt 3 *
        (-((4 - 4 * Real.sqrt 3) ^ (k + 2)) + (4 * (1 + Real.sqrt 3)) ^ (k + 2)) ∧
      (T (k + 2) : ℝ) = (1 / 4 : ℝ) * Real.sqrt 3 *
        (-((4 - 4 * Real.sqrt 3) ^ (k + 3)) + (4 * (1 + Real.sqrt 3)) ^ (k + 3)) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [show (0 : ℕ) + 1 = 1 from rfl, h1]
        norm_num
        linear_combination -16 * hs
      · rw [show (0 : ℕ) + 2 = 2 from rfl, h2]
        norm_num
        linear_combination (-32 * (Real.sqrt 3 ^ 2 + 6)) * hs
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hR := hrec (k + 1)
      rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at hR
      have hRr : (T (k + 3) : ℝ) = 8 * (T (k + 2) : ℝ) + 32 * (T (k + 1) : ℝ) := by
        exact_mod_cast hR
      have p1 : (4 * (1 + Real.sqrt 3)) ^ (k + 4) =
          8 * (4 * (1 + Real.sqrt 3)) ^ (k + 3) + 32 * (4 * (1 + Real.sqrt 3)) ^ (k + 2) := by
        rw [show k + 4 = (k + 2) + 2 by omega, show k + 3 = (k + 2) + 1 by omega, pow_add,
          pow_succ, hr1]
        ring
      have p2 : (4 - 4 * Real.sqrt 3) ^ (k + 4) =
          8 * (4 - 4 * Real.sqrt 3) ^ (k + 3) + 32 * (4 - 4 * Real.sqrt 3) ^ (k + 2) := by
        rw [show k + 4 = (k + 2) + 2 by omega, show k + 3 = (k + 2) + 1 by omega, pow_add,
          pow_succ, hr2]
        ring
      rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 3 = k + 4 by omega, hRr, ih.1, ih.2, p1, p2]
      ring
  intro k
  exact (hpair k).1

theorem OMA.solution : type_of% @OMA.S_oeis_a233175.main := by
  obtain ⟨ce, hce⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W75 R75 F75 KT75 m).filter (fun y => QS75 (y (Fin.last m)) = true)).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨cn, hcn⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W75 R75 F75 KT75 m).filter (fun y => ¬ (QS75 (y (Fin.last m)) = true))).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨ue, hue⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W75 R75 F75 KU75 m).filter (fun y => QS75 (y (Fin.last m)) = true)).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨un, hun⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W75 R75 F75 KU75 m).filter (fun y => ¬ (QS75 (y (Fin.last m)) = true))).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨ze, hze⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W75 R75 F75 KZ75 m).filter (fun y => QS75 (y (Fin.last m)) = true)).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨zn, hzn⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W75 R75 F75 KZ75 m).filter (fun y => ¬ (QS75 (y (Fin.last m)) = true))).card :=
    ⟨_, fun _ => rfl⟩
  have rT : ∀ m, ce (m + 1) = ce m * 8 + cn m * 4 ∧ cn (m + 1) = ce m * 8 + cn m * 0 := by
    intro m
    rw [hce (m + 1), hcn (m + 1), hce m, hcn m]
    exact steps75 KT75 m 8 4 8 0 wTs75 wTn75
  have rU : ∀ m, ue (m + 1) = ue m * 4 + un m * 0 ∧ un (m + 1) = ue m * 0 + un m * 0 := by
    intro m
    rw [hue (m + 1), hun (m + 1), hue m, hun m]
    exact steps75 KU75 m 4 0 0 0 wUs75 wUn75
  have rZ : ∀ m, ze (m + 1) = ze m * 0 + zn m * 0 ∧ zn (m + 1) = ze m * 0 + zn m * 0 := by
    intro m
    rw [hze (m + 1), hzn (m + 1), hze m, hzn m]
    exact steps75 KZ75 m 0 0 0 0 wZs75 wZn75
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := bases75
  have ce0 : ce 0 = 2 := by
    rw [hce 0, baseW75 R75 F75 KT75 QS75]
    exact b1
  have cn0 : cn 0 = 4 := by
    rw [hcn 0, filtNeg75 KT75 0, baseW75 R75 F75 KT75 QN75]
    exact b2
  have ue0 : ue 0 = 2 := by
    rw [hue 0, baseW75 R75 F75 KU75 QS75]
    exact b3
  have un0 : un 0 = 2 := by
    rw [hun 0, filtNeg75 KU75 0, baseW75 R75 F75 KU75 QN75]
    exact b4
  have ze0 : ze 0 = 2 := by
    rw [hze 0, baseW75 R75 F75 KZ75 QS75]
    exact b5
  have zn0 : zn 0 = 0 := by
    rw [hzn 0, filtNeg75 KZ75 0, baseW75 R75 F75 KZ75 QN75]
    exact b6
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = ce m + cn m := ⟨_, fun _ => rfl⟩
  have hT0 : T 0 = 6 := by rw [hTdef 0]; omega
  have hT1 : T 1 = 48 := by
    obtain ⟨r1, r2⟩ : ce 1 = ce 0 * 8 + cn 0 * 4 ∧ cn 1 = ce 0 * 8 + cn 0 * 0 := rT 0
    rw [hTdef 1]
    omega
  have hT2 : T 2 = 576 := by
    obtain ⟨r1, r2⟩ : ce 1 = ce 0 * 8 + cn 0 * 4 ∧ cn 1 = ce 0 * 8 + cn 0 * 0 := rT 0
    obtain ⟨s1, s2⟩ : ce 2 = ce 1 * 8 + cn 1 * 4 ∧ cn 2 = ce 1 * 8 + cn 1 * 0 := rT 1
    rw [hTdef 2]
    omega
  have hT3 : T 3 = 6144 := by
    obtain ⟨r1, r2⟩ : ce 1 = ce 0 * 8 + cn 0 * 4 ∧ cn 1 = ce 0 * 8 + cn 0 * 0 := rT 0
    obtain ⟨s1, s2⟩ : ce 2 = ce 1 * 8 + cn 1 * 4 ∧ cn 2 = ce 1 * 8 + cn 1 * 0 := rT 1
    obtain ⟨t1, t2⟩ : ce 3 = ce 2 * 8 + cn 2 * 4 ∧ cn 3 = ce 2 * 8 + cn 2 * 0 := rT 2
    rw [hTdef 3]
    omega
  have hTrec : ∀ m, T (m + 2) = 8 * T (m + 1) + 32 * T m := by
    intro m
    obtain ⟨r1, r2⟩ := rT m
    obtain ⟨s1, s2⟩ : ce (m + 2) = ce (m + 1) * 8 + cn (m + 1) * 4 ∧
        cn (m + 2) = ce (m + 1) * 8 + cn (m + 1) * 0 := rT (m + 1)
    rw [hTdef (m + 2), hTdef (m + 1), hTdef m]
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
  have htot : ∀ m, 8 * a (m + 1) = T m + 2 * (ue m + un m) + 5 * (ze m + zn m) := by
    intro m
    have h1 := count75 (m + 1)
    have h2 := Finset.card_filter_add_card_filter_not (s := W75 R75 F75 KT75 m)
      (fun y => QS75 (y (Fin.last m)) = true)
    have h3 := Finset.card_filter_add_card_filter_not (s := W75 R75 F75 KU75 m)
      (fun y => QS75 (y (Fin.last m)) = true)
    have h4 := Finset.card_filter_add_card_filter_not (s := W75 R75 F75 KZ75 m)
      (fun y => QS75 (y (Fin.last m)) = true)
    rw [cardT75 m, cardU75 m, cardZ75 m, ← h2, ← h3, ← h4] at h1
    rw [hTdef m, hce m, hcn m, hue m, hun m, hze m, hzn m]
    omega
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℕ, ∀ n, a n = b n := ⟨a, fun _ => rfl⟩
  have htotb : ∀ m, 8 * b (m + 1) = T m + 2 * (ue m + un m) + 5 * (ze m + zn m) := by
    intro m
    rw [← hb]
    exact htot m
  have h8b : ∀ k, 8 * b (k + 2) = T (k + 1) + 16 * 4 ^ k := by
    intro k
    have h := htotb (k + 1)
    rw [show k + 1 + 1 = k + 2 by omega] at h
    obtain ⟨u1, u2⟩ := hU k
    obtain ⟨z1, z2⟩ := hZ k
    omega
  have v1 : b 1 = 3 := by
    have h := htotb 0
    rw [show (0 : ℕ) + 1 = 1 from rfl] at h
    omega
  have v2 : b 2 = 8 := by
    have h := h8b 0
    rw [show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl, pow_zero] at h
    omega
  have v3 : b 3 = 80 := by
    have h := h8b 1
    rw [show (1 : ℕ) + 2 = 3 from rfl, show (1 : ℕ) + 1 = 2 from rfl, pow_one] at h
    omega
  have v4 : b 4 = 800 := by
    have h := h8b 2
    rw [show (2 : ℕ) + 2 = 4 from rfl, show (2 : ℕ) + 1 = 3 from rfl] at h
    norm_num at h
    omega
  refine ⟨?_, ?_⟩
  · obtain ⟨f, hf⟩ : ∃ f : ℕ → ℚ, ∀ n, f n = if n = 0 then (0 : ℚ) else (a n : ℚ) :=
      ⟨_, fun _ => rfl⟩
    have hfun : (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = f :=
      funext fun n => (hf n).symm
    have f0 : f 0 = 0 := by rw [hf, if_pos (rfl : (0 : ℕ) = 0)]
    have f1 : f 1 = 3 := by
      rw [hf, if_neg (show ¬ ((1 : ℕ) = 0) by norm_num), hb]
      exact_mod_cast v1
    have f2 : f 2 = 8 := by
      rw [hf, if_neg (show ¬ ((2 : ℕ) = 0) by norm_num), hb]
      exact_mod_cast v2
    have f3 : f 3 = 80 := by
      rw [hf, if_neg (show ¬ ((3 : ℕ) = 0) by norm_num), hb]
      exact_mod_cast v3
    have f4 : f 4 = 800 := by
      rw [hf, if_neg (show ¬ ((4 : ℕ) = 0) by norm_num), hb]
      exact_mod_cast v4
    have frec : ∀ k, f (k + 5) = 12 * f (k + 4) - 128 * f (k + 2) := by
      intro k
      rw [hf, hf, hf, if_neg (show ¬ (k + 5 = 0) by omega), if_neg (show ¬ (k + 4 = 0) by omega),
        if_neg (show ¬ (k + 2 = 0) by omega)]
      simp only [hb]
      have q5 : (8 * b (k + 5) : ℚ) = (T (k + 4) : ℚ) + 16 * (4 : ℚ) ^ (k + 3) := by
        have h := h8b (k + 3)
        rw [show k + 3 + 2 = k + 5 by omega, show k + 3 + 1 = k + 4 by omega] at h
        exact_mod_cast h
      have q4 : (8 * b (k + 4) : ℚ) = (T (k + 3) : ℚ) + 16 * (4 : ℚ) ^ (k + 2) := by
        have h := h8b (k + 2)
        rw [show k + 2 + 2 = k + 4 by omega, show k + 2 + 1 = k + 3 by omega] at h
        exact_mod_cast h
      have q2 : (8 * b (k + 2) : ℚ) = (T (k + 1) : ℚ) + 16 * (4 : ℚ) ^ k := by
        exact_mod_cast h8b k
      have tr4 : (T (k + 4) : ℚ) = 8 * (T (k + 3) : ℚ) + 32 * (T (k + 2) : ℚ) := by
        have h := hTrec (k + 2)
        rw [show k + 2 + 2 = k + 4 by omega, show k + 2 + 1 = k + 3 by omega] at h
        exact_mod_cast h
      have tr3 : (T (k + 3) : ℚ) = 8 * (T (k + 2) : ℚ) + 32 * (T (k + 1) : ℚ) := by
        have h := hTrec (k + 1)
        rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at h
        exact_mod_cast h
      have p3 : (4 : ℚ) ^ (k + 3) = 64 * (4 : ℚ) ^ k := by
        rw [pow_add]
        norm_num
        ring
      have p2 : (4 : ℚ) ^ (k + 2) = 16 * (4 : ℚ) ^ k := by
        rw [pow_add]
        norm_num
        ring
      rw [p3] at q5
      rw [p2] at q4
      linear_combination (q5 - 12 * q4 + 128 * q2 + tr4 - 4 * tr3) / 8
    rw [show PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = PowerSeries.mk f
      from congrArg PowerSeries.mk hfun]
    have e : PowerSeries.mk f *
        ((1 - 4 * PowerSeries.X) * (1 - 8 * PowerSeries.X - 32 * PowerSeries.X ^ 2)) =
        PowerSeries.mk f
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 12 * (PowerSeries.mk f * PowerSeries.X ^ 1)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 128 * (PowerSeries.mk f * PowerSeries.X ^ 3) := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 12,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 128]
      ring
    have e2 : (PowerSeries.X *
        (3 - 28 * PowerSeries.X - 16 * PowerSeries.X ^ 2 + 224 * PowerSeries.X ^ 3) :
        PowerSeries ℚ) =
        PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3
          - PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 28
          - PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 16
          + PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 224 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 28,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 16,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 224]
      ring
    rw [e, e2]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C]
    rcases Nat.lt_or_ge n 5 with hn | hn
    · interval_cases n
      · norm_num [f0]
      · norm_num [f0, f1]
      · norm_num [f1, f2]
      · norm_num [f0, f2, f3]
      · norm_num [f1, f3, f4]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      rw [if_pos (show 1 ≤ k + 5 by omega), if_pos (show 3 ≤ k + 5 by omega),
        if_pos (show 1 ≤ k + 5 by omega), if_pos (show 2 ≤ k + 5 by omega),
        if_pos (show 3 ≤ k + 5 by omega), if_pos (show 4 ≤ k + 5 by omega),
        if_neg (show ¬ (k + 5 - 1 = 0) by omega), if_neg (show ¬ (k + 5 - 2 = 0) by omega),
        if_neg (show ¬ (k + 5 - 3 = 0) by omega), if_neg (show ¬ (k + 5 - 4 = 0) by omega),
        show k + 5 - 1 = k + 4 by omega, show k + 5 - 3 = k + 2 by omega, frec k]
      ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have h8 : (8 : ℝ) * (b (k + 2) : ℝ) = (T (k + 1) : ℝ) + 16 * (4 : ℝ) ^ k := by
      exact_mod_cast h8b k
    have hT := closedT75 T hT1 hT2 hTrec k
    have e2 : (2 : ℝ) ^ (2 * k + 1) = 2 * (4 : ℝ) ^ k := by
      rw [pow_succ (2 : ℝ) (2 * k), pow_mul (2 : ℝ) 2 k]
      norm_num
      ring
    rw [hb, show 2 * (k + 2) - 3 = 2 * k + 1 by omega, e2]
    linear_combination (h8 + hT) / 8
