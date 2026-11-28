import OMAStatements.S_oeis_a211715

-- Problem: A211715: Number of (n+1) X (n+1) -11..11 symmetric matrices with every 2 X 2 subblock having sum zero and two or four distinct values.
-- Upstream: formal-conjectures statements/oeis-a211715.lean:0 (declaration OMA.S_oeis_a211715.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with N(x, y) = (-1)^(x+y) M(x, y) the block sums say N(x, y) = N(x, 0) + N(0, y) - N(0, 0),
-- and symmetry gives 2 M(i, j) = (-1)^(i+j) (d i + d j) for the diagonal d, whose entries have one
-- parity. So the matrices correspond to diagonals d, and the distinct-values condition of the
-- block (i, j) is a condition on d i, d (i+1), d j, d (j+1). The diagonal blocks force consecutive
-- entries to be equal and nonzero or in ratio -3; so all values lie in one of the components
-- {1, -3, 9}, {-1, 3, -9}, {2, -6}, {-2, 6} or a singleton, and the off-diagonal blocks forbid
-- 1 and 9 (and -1 and -9) together. The value set of a valid diagonal is therefore one of 22
-- singletons or 6 pairs, and conversely every such diagonal is valid (finite checks by decide):
-- 22 + 6 (2^(n+1) - 2) = 10 + 3 * 2^(n+2). The g.f. follows by comparing coefficients.

/-- Two consecutive diagonal entries are compatible. -/
abbrev kst211715 (x y : ℤ) : Prop := (x = y ∧ x ≠ 0) ∨ (x ≠ y ∧ (y = -3 * x ∨ x = -3 * y))

/-- The distinct-values condition of a block, in terms of the diagonal entries. -/
abbrev kQ211715 (x y u v : ℤ) : Prop :=
  ({(x + u) / 2, -((y + u) / 2), -((x + v) / 2), (y + v) / 2} : Finset ℤ).card ∈
    ({2, 4} : Finset ℕ)

/-- The component of a value for the compatibility relation. -/
def kcomp211715 (x : ℤ) : Finset ℤ :=
  if x ∈ ({1, -3, 9} : Finset ℤ) then {1, -3, 9} else
  if x ∈ ({-1, 3, -9} : Finset ℤ) then {-1, 3, -9} else
  if x ∈ ({2, -6} : Finset ℤ) then {2, -6} else
  if x ∈ ({-2, 6} : Finset ℤ) then {-2, 6} else {x}

/-- The possible value sets of a valid diagonal. -/
def kFam211715 : Finset (Finset ℤ) :=
  {{-11}, {-10}, {-9}, {-8}, {-7}, {-6}, {-5}, {-4}, {-3}, {-2}, {-1}, {1}, {2}, {3}, {4}, {5},
    {6}, {7}, {8}, {9}, {10}, {11}, {1, -3}, {-1, 3}, {2, -6}, {-2, 6}, {3, -9}, {-3, 9}}

theorem kF1211715 : ∀ x ∈ Finset.Icc (-11 : ℤ) 11, ∀ y ∈ Finset.Icc (-11 : ℤ) 11,
    x % 2 = y % 2 → kQ211715 x y x y → kst211715 x y := by
  decide +kernel

theorem kFc211715 : ∀ x ∈ Finset.Icc (-11 : ℤ) 11, ∀ y ∈ Finset.Icc (-11 : ℤ) 11,
    kst211715 x y → kcomp211715 y = kcomp211715 x := by
  decide +kernel

theorem kFs211715 : ∀ x ∈ Finset.Icc (-11 : ℤ) 11, x ∈ kcomp211715 x := by
  decide +kernel

theorem kFf211715 : ∀ x ∈ Finset.Icc (-11 : ℤ) 11, ∀ V ∈ (kcomp211715 x).powerset, x ∈ V →
    (0 : ℤ) ∉ V → ¬ ((1 : ℤ) ∈ V ∧ (9 : ℤ) ∈ V) → ¬ ((-1 : ℤ) ∈ V ∧ (-9 : ℤ) ∈ V) →
    V ∈ kFam211715 := by
  decide +kernel

theorem kF3211715 : ∀ S ∈ kFam211715, ∀ x ∈ S, ∀ y ∈ S, ∀ u ∈ S, ∀ v ∈ S,
    kQ211715 x y u v := by
  decide +kernel

theorem kFr211715 : ∀ S ∈ kFam211715, ∀ x ∈ S, (-11 ≤ x ∧ x ≤ 11) ∧ ∀ y ∈ S, x % 2 = y % 2 := by
  decide +kernel

theorem kF2211715 :
    ¬ (kQ211715 1 (-3) (-3) 9 ∧ kQ211715 (-3) 9 1 (-3)) ∧
    ¬ (kQ211715 1 (-3) 9 (-3) ∧ kQ211715 9 (-3) 1 (-3)) ∧
    ¬ (kQ211715 (-3) 1 (-3) 9 ∧ kQ211715 (-3) 9 (-3) 1) ∧
    ¬ (kQ211715 (-3) 1 9 (-3) ∧ kQ211715 9 (-3) (-3) 1) ∧
    ¬ (kQ211715 (-1) 3 3 (-9) ∧ kQ211715 3 (-9) (-1) 3) ∧
    ¬ (kQ211715 (-1) 3 (-9) 3 ∧ kQ211715 (-9) 3 (-1) 3) ∧
    ¬ (kQ211715 3 (-1) 3 (-9) ∧ kQ211715 3 (-9) 3 (-1)) ∧
    ¬ (kQ211715 3 (-1) (-9) 3 ∧ kQ211715 (-9) 3 3 (-1)) := by
  decide +kernel

theorem kFk211715 : (kFam211715.filter (fun S => S.card = 1)).card = 22 ∧
    (kFam211715.filter (fun S => ¬ S.card = 1)).card = 6 ∧
    ∀ S ∈ kFam211715, S.card = 1 ∨ S.card = 2 := by
  decide +kernel

theorem ksq211715 (k : ℕ) : ((-1 : ℤ) ^ k) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem kkey211715 (n : ℕ) (M : Fin (n + 1) → Fin (n + 1) → ℤ) (hs : ∀ i j, M i j = M j i)
    (hb : ∀ i j : Fin n, M i.castSucc j.castSucc + M i.succ j.castSucc + M i.castSucc j.succ +
      M i.succ j.succ = 0) :
    ∀ i j : Fin (n + 1), 2 * M i j = (-1) ^ (i.val + j.val) * (M i i + M j j) := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → Fin (n + 1), ∀ x, c x = ⟨min x n, by omega⟩ := ⟨_, fun _ => rfl⟩
  have hcv : ∀ x, x ≤ n → (c x).val = x := by
    intro x hx
    rw [hc x]
    exact Nat.min_eq_left hx
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℕ → ℤ, ∀ x y, N x y = (-1) ^ (x + y) * M (c x) (c y) :=
    ⟨_, fun _ _ => rfl⟩
  have hcs : ∀ x (hx : x < n), (⟨x, hx⟩ : Fin n).castSucc = c x := by
    intro x hx
    apply Fin.ext
    rw [Fin.val_castSucc, hcv x (by omega)]
  have hsu : ∀ x (hx : x < n), (⟨x, hx⟩ : Fin n).succ = c (x + 1) := by
    intro x hx
    apply Fin.ext
    rw [Fin.val_succ, hcv (x + 1) (by omega)]
  have hblock : ∀ x y, x < n → y < n →
      N (x + 1) (y + 1) = N x (y + 1) + N (x + 1) y - N x y := by
    intro x y hx hy
    have hb' : M (c x) (c y) + M (c (x + 1)) (c y) + M (c x) (c (y + 1)) +
        M (c (x + 1)) (c (y + 1)) = 0 := by
      have h := hb ⟨x, hx⟩ ⟨y, hy⟩
      rw [hcs x hx, hcs y hy, hsu x hx, hsu y hy] at h
      exact h
    have e11 := hN (x + 1) (y + 1)
    have e01 := hN x (y + 1)
    have e10 := hN (x + 1) y
    have e00 := hN x y
    linear_combination e11 - e01 - e10 + e00 + (-1 : ℤ) ^ (x + y) * hb'
  have hL : ∀ x y, x ≤ n → y ≤ n → N x y = N x 0 + N 0 y - N 0 0 := by
    intro x
    induction x with
    | zero =>
      intro y _ _
      ring
    | succ x ihx =>
      intro y
      induction y with
      | zero =>
        intro _ _
        ring
      | succ y ihy =>
        intro hx hy
        have h1 := hblock x y (by omega) (by omega)
        have h2 := ihx (y + 1) (by omega) hy
        have h3 := ihx y (by omega) (by omega)
        have h4 := ihy hx (by omega)
        linear_combination h1 + h2 + h4 - h3
  have hNs : ∀ x y, N x y = N y x := by
    intro x y
    rw [hN x y, hN y x, hs (c x) (c y), add_comm x y]
  intro i j
  have hi := i.isLt
  have hj := j.isLt
  have ci : c i.val = i := Fin.ext (hcv _ (by omega))
  have cj : c j.val = j := Fin.ext (hcv _ (by omega))
  have Nij := hN i.val j.val
  have Nii := hN i.val i.val
  have Njj := hN j.val j.val
  rw [ci, cj] at Nij
  rw [ci] at Nii
  rw [cj] at Njj
  have L1 := hL i.val j.val (by omega) (by omega)
  have L2 := hL i.val i.val (by omega) (by omega)
  have L3 := hL j.val j.val (by omega) (by omega)
  have S1 := hNs i.val 0
  have S2 := hNs j.val 0
  have E : 2 * N i.val j.val = N i.val i.val + N j.val j.val := by
    linear_combination 2 * L1 - L2 - L3 + S1 - S2
  rw [Nij, Nii, Njj] at E
  have qu := ksq211715 i.val
  have qv := ksq211715 j.val
  linear_combination (-1 : ℤ) ^ (i.val + j.val) * E +
    ((-1 : ℤ) ^ i.val * (-1 : ℤ) ^ j.val * M i i - 2 * ((-1 : ℤ) ^ j.val) ^ 2 * M i j) * qu +
    ((-1 : ℤ) ^ i.val * (-1 : ℤ) ^ j.val * M j j - 2 * M i j) * qv

theorem kblk211715 (s : ℤ) (hs : s ≠ 0) (A B C D : ℤ) :
    ({s * A, -s * B, -s * C, s * D} : Finset ℤ).card = ({A, -B, -C, D} : Finset ℤ).card := by
  have e : ({s * A, -s * B, -s * C, s * D} : Finset ℤ) =
      ({A, -B, -C, D} : Finset ℤ).image (fun z => s * z) := by
    simp only [Finset.image_insert, Finset.image_singleton, mul_neg, neg_mul]
  rw [e, Finset.card_image_of_injective _ (mul_right_injective₀ hs)]

/-- The block condition of the matrix built from a diagonal. -/
theorem kbq211715 (n : ℕ) (d : Fin (n + 1) → ℤ) (i j : Fin n) :
    ({(-1) ^ (i.castSucc.val + j.castSucc.val) * ((d i.castSucc + d j.castSucc) / 2),
      (-1) ^ (i.succ.val + j.castSucc.val) * ((d i.succ + d j.castSucc) / 2),
      (-1) ^ (i.castSucc.val + j.succ.val) * ((d i.castSucc + d j.succ) / 2),
      (-1) ^ (i.succ.val + j.succ.val) * ((d i.succ + d j.succ) / 2)} : Finset ℤ).card =
    ({(d i.castSucc + d j.castSucc) / 2, -((d i.succ + d j.castSucc) / 2),
      -((d i.castSucc + d j.succ) / 2), (d i.succ + d j.succ) / 2} : Finset ℤ).card := by
  rw [Fin.val_castSucc, Fin.val_castSucc, Fin.val_succ, Fin.val_succ]
  have p1 : (-1 : ℤ) ^ (i.val + 1 + j.val) = -(-1) ^ (i.val + j.val) := by ring
  have p2 : (-1 : ℤ) ^ (i.val + (j.val + 1)) = -(-1) ^ (i.val + j.val) := by ring
  have p3 : (-1 : ℤ) ^ (i.val + 1 + (j.val + 1)) = (-1) ^ (i.val + j.val) := by ring
  rw [p1, p2, p3]
  exact kblk211715 _ (pow_ne_zero _ (by norm_num)) _ _ _ _

theorem kprop211715 (n : ℕ) (d : Fin (n + 1) → ℤ) (P : ℤ → Prop)
    (h : ∀ k : Fin n, P (d k.castSucc) ↔ P (d k.succ)) : ∀ i, P (d i) ↔ P (d 0) := by
  have key : ∀ m (hm : m < n + 1), P (d ⟨m, hm⟩) ↔ P (d 0) := by
    intro m
    induction m with
    | zero =>
      intro hm
      have e0 : (⟨0, hm⟩ : Fin (n + 1)) = 0 := by
        ext
        simp
      rw [e0]
    | succ m ih =>
      intro hm
      have hk := h ⟨m, by omega⟩
      have e1 : (⟨m, by omega⟩ : Fin n).castSucc = ⟨m, by omega⟩ := rfl
      have e2 : (⟨m, by omega⟩ : Fin n).succ = ⟨m + 1, hm⟩ := rfl
      rw [e1, e2] at hk
      exact hk.symm.trans (ih (by omega))
  intro i
  exact key i.val i.isLt

theorem kbd211715 (n : ℕ) (d : Fin (n + 1) → ℤ) (v : ℤ) (h1 : ∃ i, d i = v)
    (h2 : ∃ j, d j ≠ v) :
    ∃ k : Fin n, (d k.castSucc = v ∧ d k.succ ≠ v) ∨ (d k.castSucc ≠ v ∧ d k.succ = v) := by
  by_contra hc
  have hiff : ∀ k : Fin n, d k.castSucc = v ↔ d k.succ = v := by
    intro k
    constructor
    · intro hk
      by_contra hk'
      exact hc ⟨k, Or.inl ⟨hk, hk'⟩⟩
    · intro hk
      by_contra hk'
      exact hc ⟨k, Or.inr ⟨hk', hk⟩⟩
  have hall := kprop211715 n d (fun x => x = v) hiff
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := h2
  exact hj ((hall j).2 ((hall i).1 hi))

/-- Sequences with exactly the values of S. -/
theorem kE1211715 (n : ℕ) (x : ℤ) :
    ((Fintype.piFinset fun _ : Fin (n + 1) => ({x} : Finset ℤ)).filter
      (fun d => ∀ y ∈ ({x} : Finset ℤ), ∃ i, d i = y)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨fun _ => x, ?_⟩
  ext d
  rw [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩
    funext i
    exact Finset.mem_singleton.1 (h i)
  · rintro rfl
    refine ⟨fun _ => Finset.mem_singleton_self x, fun y hy => ⟨0, ?_⟩⟩
    rw [Finset.mem_singleton] at hy
    exact hy.symm

theorem kE2211715 (n : ℕ) (x y : ℤ) (hxy : x ≠ y) :
    ((Fintype.piFinset fun _ : Fin (n + 1) => ({x, y} : Finset ℤ)).filter
      (fun d => ∀ z ∈ ({x, y} : Finset ℤ), ∃ i, d i = z)).card = 2 ^ (n + 1) - 2 := by
  have htot : (Fintype.piFinset fun _ : Fin (n + 1) => ({x, y} : Finset ℤ)).card = 2 ^ (n + 1) := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.card_pair hxy]
  have hneg : ((Fintype.piFinset fun _ : Fin (n + 1) => ({x, y} : Finset ℤ)).filter
      (fun d => ¬ ∀ z ∈ ({x, y} : Finset ℤ), ∃ i, d i = z)).card = 2 := by
    rw [Finset.card_eq_two]
    refine ⟨fun _ => x, fun _ => y, fun h => hxy (congrFun h 0), ?_⟩
    ext d
    rw [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, hn⟩
      have key : (∀ i, d i ≠ x) ∨ (∀ i, d i ≠ y) := by
        by_contra hc
        apply hn
        intro z hz
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz | hz
        · rw [hz]
          by_contra h2
          apply hc
          left
          intro i hi
          exact h2 ⟨i, hi⟩
        · rw [hz]
          by_contra h2
          apply hc
          right
          intro i hi
          exact h2 ⟨i, hi⟩
      rcases key with h | h
      · right
        funext i
        have hdi := hd i
        rw [Finset.mem_insert, Finset.mem_singleton] at hdi
        rcases hdi with h' | h'
        · exact absurd h' (h i)
        · exact h'
      · left
        funext i
        have hdi := hd i
        rw [Finset.mem_insert, Finset.mem_singleton] at hdi
        rcases hdi with h' | h'
        · exact h'
        · exact absurd h' (h i)
    · rintro (rfl | rfl)
      · refine ⟨fun _ => Finset.mem_insert_self x _, fun h => ?_⟩
        obtain ⟨i, hi⟩ := h y (by simp)
        exact hxy hi
      · refine ⟨fun _ => by simp, fun h => ?_⟩
        obtain ⟨i, hi⟩ := h x (by simp)
        exact hxy hi.symm
  have hsum : ((Fintype.piFinset fun _ : Fin (n + 1) => ({x, y} : Finset ℤ)).filter
      (fun d => ∀ z ∈ ({x, y} : Finset ℤ), ∃ i, d i = z)).card +
      ((Fintype.piFinset fun _ : Fin (n + 1) => ({x, y} : Finset ℤ)).filter
        (fun d => ¬ ∀ z ∈ ({x, y} : Finset ℤ), ∃ i, d i = z)).card =
      (Fintype.piFinset fun _ : Fin (n + 1) => ({x, y} : Finset ℤ)).card :=
    Finset.card_filter_add_card_filter_not _
  omega

/-- The valid diagonals are the sequences whose value set is in kFam211715. -/
theorem kchar211715 (n : ℕ) (hn : 1 ≤ n) :
    (Fintype.piFinset fun _ : Fin (n + 1) => Finset.Icc (-11 : ℤ) 11).filter
      (fun d => (∀ i, d i % 2 = d 0 % 2) ∧
        ∀ i j : Fin n, kQ211715 (d i.castSucc) (d i.succ) (d j.castSucc) (d j.succ)) =
    kFam211715.biUnion (fun S => (Fintype.piFinset fun _ : Fin (n + 1) => S).filter
      (fun d => ∀ z ∈ S, ∃ i, d i = z)) := by
  ext d
  rw [Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨hdI, hpar, hQ⟩
    have hr : ∀ i, -11 ≤ d i ∧ d i ≤ 11 := fun i =>
      Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hdI i)
    have hst : ∀ k : Fin n, kst211715 (d k.castSucc) (d k.succ) := fun k =>
      kF1211715 _ (Finset.mem_Icc.2 (hr _)) _ (Finset.mem_Icc.2 (hr _))
        ((hpar _).trans (hpar _).symm) (hQ k k)
    have hcomp : ∀ i, d i ∈ kcomp211715 (d 0) := by
      have hc := kprop211715 n d (fun x => kcomp211715 x = kcomp211715 (d 0)) (fun k => by
        show kcomp211715 (d k.castSucc) = kcomp211715 (d 0) ↔
          kcomp211715 (d k.succ) = kcomp211715 (d 0)
        rw [kFc211715 _ (Finset.mem_Icc.2 (hr _)) _ (Finset.mem_Icc.2 (hr _)) (hst k)])
      intro i
      have h1 : kcomp211715 (d i) = kcomp211715 (d 0) := (hc i).2 rfl
      have h2 := kFs211715 (d i) (Finset.mem_Icc.2 (hr i))
      rw [h1] at h2
      exact h2
    have hnz : ∀ i, d i ≠ 0 := by
      intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · have h := hst ⟨0, by omega⟩
        have e : (⟨0, by omega⟩ : Fin n).castSucc = 0 := by
          ext
          simp
        rw [e] at h
        unfold kst211715 at h
        omega
      · have h := hst j
        unfold kst211715 at h
        omega
    refine ⟨Finset.univ.image d, ?_, ?_⟩
    · apply kFf211715 (d 0) (Finset.mem_Icc.2 (hr 0))
      · rw [Finset.mem_powerset]
        intro z hz
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact hcomp i
      · exact Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩
      · intro h0
        obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h0
        exact hnz i hi
      · rintro ⟨h1, h9⟩
        obtain ⟨i1, -, hi1⟩ := Finset.mem_image.1 h1
        obtain ⟨i9, -, hi9⟩ := Finset.mem_image.1 h9
        obtain ⟨k1, hk1⟩ := kbd211715 n d 1 ⟨i1, hi1⟩ ⟨i9, by rw [hi9]; norm_num⟩
        obtain ⟨k2, hk2⟩ := kbd211715 n d 9 ⟨i9, hi9⟩ ⟨i1, by rw [hi1]; norm_num⟩
        have s1 := hst k1
        have s2 := hst k2
        unfold kst211715 at s1 s2
        have r3 := hr k2.castSucc
        have r4 := hr k2.succ
        have v1 : (d k1.castSucc = 1 ∧ d k1.succ = -3) ∨ (d k1.castSucc = -3 ∧ d k1.succ = 1) := by
          omega
        have v2 : (d k2.castSucc = -3 ∧ d k2.succ = 9) ∨ (d k2.castSucc = 9 ∧ d k2.succ = -3) := by
          omega
        have q12 := hQ k1 k2
        have q21 := hQ k2 k1
        obtain ⟨f1, f2, f3, f4, -, -, -, -⟩ := kF2211715
        rcases v1 with ⟨a1, a2⟩ | ⟨a1, a2⟩
        · rcases v2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
          · rw [a1, a2, b1, b2] at q12 q21
            exact f1 ⟨q12, q21⟩
          · rw [a1, a2, b1, b2] at q12 q21
            exact f2 ⟨q12, q21⟩
        · rcases v2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
          · rw [a1, a2, b1, b2] at q12 q21
            exact f3 ⟨q12, q21⟩
          · rw [a1, a2, b1, b2] at q12 q21
            exact f4 ⟨q12, q21⟩
      · rintro ⟨h1, h9⟩
        obtain ⟨i1, -, hi1⟩ := Finset.mem_image.1 h1
        obtain ⟨i9, -, hi9⟩ := Finset.mem_image.1 h9
        obtain ⟨k1, hk1⟩ := kbd211715 n d (-1) ⟨i1, hi1⟩ ⟨i9, by rw [hi9]; norm_num⟩
        obtain ⟨k2, hk2⟩ := kbd211715 n d (-9) ⟨i9, hi9⟩ ⟨i1, by rw [hi1]; norm_num⟩
        have s1 := hst k1
        have s2 := hst k2
        unfold kst211715 at s1 s2
        have r3 := hr k2.castSucc
        have r4 := hr k2.succ
        have v1 : (d k1.castSucc = -1 ∧ d k1.succ = 3) ∨ (d k1.castSucc = 3 ∧ d k1.succ = -1) := by
          omega
        have v2 : (d k2.castSucc = 3 ∧ d k2.succ = -9) ∨ (d k2.castSucc = -9 ∧ d k2.succ = 3) := by
          omega
        have q12 := hQ k1 k2
        have q21 := hQ k2 k1
        obtain ⟨-, -, -, -, f1, f2, f3, f4⟩ := kF2211715
        rcases v1 with ⟨a1, a2⟩ | ⟨a1, a2⟩
        · rcases v2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
          · rw [a1, a2, b1, b2] at q12 q21
            exact f1 ⟨q12, q21⟩
          · rw [a1, a2, b1, b2] at q12 q21
            exact f2 ⟨q12, q21⟩
        · rcases v2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
          · rw [a1, a2, b1, b2] at q12 q21
            exact f3 ⟨q12, q21⟩
          · rw [a1, a2, b1, b2] at q12 q21
            exact f4 ⟨q12, q21⟩
    · rw [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i => Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, fun z hz => ?_⟩
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hz
      exact ⟨i, hi⟩
  · rintro ⟨S, hS, hd⟩
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hd
    obtain ⟨hv, -⟩ := hd
    have hrS := kFr211715 S hS
    refine ⟨?_, fun i => ((hrS (d i) (hv i)).2 (d 0) (hv 0)), fun i j =>
      kF3211715 S hS _ (hv _) _ (hv _) _ (hv _) _ (hv _)⟩
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_Icc.2 (hrS (d i) (hv i)).1

/-- The matrices correspond to their diagonals. -/
theorem kset211715 (n : ℕ) (Φ : (Fin (n + 1) → ℤ) → Fin (n + 1) → Fin (n + 1) → ℤ)
    (hΦ : ∀ d i j, Φ d i j = (-1) ^ (i.val + j.val) * ((d i + d j) / 2)) :
    (Fintype.piFinset fun _ : Fin (n + 1) =>
      Fintype.piFinset fun _ : Fin (n + 1) => Finset.Icc (-11 : ℤ) 11).filter
    (fun M => (∀ i j, M i j = M j i) ∧
      ∀ i j : Fin n, M i.castSucc j.castSucc + M i.succ j.castSucc + M i.castSucc j.succ +
        M i.succ j.succ = 0 ∧
        ({M i.castSucc j.castSucc, M i.succ j.castSucc, M i.castSucc j.succ, M i.succ j.succ} :
          Finset ℤ).card ∈ ({2, 4} : Finset ℕ)) =
    ((Fintype.piFinset fun _ : Fin (n + 1) => Finset.Icc (-11 : ℤ) 11).filter
      (fun d => (∀ i, d i % 2 = d 0 % 2) ∧
        ∀ i j : Fin n, kQ211715 (d i.castSucc) (d i.succ) (d j.castSucc) (d j.succ))).image Φ := by
  ext M
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hM, hs, hb⟩
    have key := kkey211715 n M hs (fun i j => (hb i j).1)
    have hr : ∀ i, M i i ∈ Finset.Icc (-11 : ℤ) 11 := fun i =>
      Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hM i) i
    have hp : ∀ j, M j j % 2 = M 0 0 % 2 := by
      intro j
      have k0 := key 0 j
      rw [Fin.val_zero, zero_add] at k0
      rcases neg_one_pow_eq_or ℤ j.val with h | h
      · rw [h] at k0
        omega
      · rw [h] at k0
        omega
    have hMΦ : ∀ i j, M i j = Φ (fun x => M x x) i j := by
      intro i j
      rw [hΦ]
      show M i j = (-1) ^ (i.val + j.val) * ((M i i + M j j) / 2)
      have k1 := key i j
      rcases neg_one_pow_eq_or ℤ (i.val + j.val) with h | h
      · rw [h] at k1 ⊢
        omega
      · rw [h] at k1 ⊢
        omega
    refine ⟨fun i => M i i, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Fintype.mem_piFinset.2 hr, hp, fun i j => ?_⟩
      have hc := (hb i j).2
      rw [hMΦ i.castSucc j.castSucc, hMΦ i.succ j.castSucc, hMΦ i.castSucc j.succ,
        hMΦ i.succ j.succ, hΦ, hΦ, hΦ, hΦ, kbq211715 n (fun x => M x x) i j] at hc
      exact hc
    · funext i j
      exact (hMΦ i j).symm
  · rintro ⟨d, hd, rfl⟩
    rw [Finset.mem_filter] at hd
    obtain ⟨hdI, hpar, hQ⟩ := hd
    have hr : ∀ i, -11 ≤ d i ∧ d i ≤ 11 := fun i =>
      Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hdI i)
    refine ⟨?_, ?_, fun i j => ⟨?_, ?_⟩⟩
    · rw [Fintype.mem_piFinset]
      intro i
      rw [Fintype.mem_piFinset]
      intro j
      rw [hΦ, Finset.mem_Icc]
      have hi := hr i
      have hj := hr j
      rcases neg_one_pow_eq_or ℤ (i.val + j.val) with h | h
      · rw [h]
        omega
      · rw [h]
        omega
    · intro i j
      rw [hΦ, hΦ, add_comm i.val j.val, add_comm (d i) (d j)]
    · rw [hΦ, hΦ, hΦ, hΦ, Fin.val_castSucc, Fin.val_castSucc, Fin.val_succ, Fin.val_succ]
      have h1 := hpar i.castSucc
      have h2 := hpar i.succ
      have h3 := hpar j.castSucc
      have h4 := hpar j.succ
      have hABCD : (d i.castSucc + d j.castSucc) / 2 - (d i.succ + d j.castSucc) / 2 -
          (d i.castSucc + d j.succ) / 2 + (d i.succ + d j.succ) / 2 = 0 := by
        omega
      linear_combination (-1 : ℤ) ^ (i.val + j.val) * hABCD
    · rw [hΦ, hΦ, hΦ, hΦ, kbq211715 n d i j]
      exact hQ i j

theorem kinj211715 (n : ℕ) (Φ : (Fin (n + 1) → ℤ) → Fin (n + 1) → Fin (n + 1) → ℤ)
    (hΦ : ∀ d i j, Φ d i j = (-1) ^ (i.val + j.val) * ((d i + d j) / 2)) :
    Function.Injective Φ := by
  intro d d' h
  funext i
  have h1 := congrFun (congrFun h i) i
  rw [hΦ, hΦ, Even.neg_one_pow ⟨i.val, rfl⟩, one_mul, one_mul] at h1
  omega

theorem kcard211715 (n : ℕ) (hn : 1 ≤ n) :
    OMA.S_oeis_a211715.a n = 22 + 6 * (2 ^ (n + 1) - 2) := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin (n + 1) → ℤ) → Fin (n + 1) → Fin (n + 1) → ℤ,
      ∀ d i j, Φ d i j = (-1) ^ (i.val + j.val) * ((d i + d j) / 2) := ⟨_, fun _ _ _ => rfl⟩
  unfold OMA.S_oeis_a211715.a
  rw [kset211715 n Φ hΦ, Finset.card_image_of_injective _ (kinj211715 n Φ hΦ),
    kchar211715 n hn, Finset.card_biUnion]
  · obtain ⟨k1, k2, k3⟩ := kFk211715
    have hval : ∀ S ∈ kFam211715,
        ((Fintype.piFinset fun _ : Fin (n + 1) => S).filter (fun d => ∀ z ∈ S, ∃ i, d i = z)).card =
          if S.card = 1 then 1 else 2 ^ (n + 1) - 2 := by
      intro S hS
      rcases k3 S hS with h | h
      · rw [if_pos h]
        obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h
        exact kE1211715 n x
      · rw [if_neg (by omega)]
        obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 h
        exact kE2211715 n x y hxy
    rw [Finset.sum_congr rfl hval, Finset.sum_ite, Finset.sum_const, Finset.sum_const, k1, k2,
      smul_eq_mul, smul_eq_mul, mul_one]
  · intro S _ T _ hST
    exact Finset.disjoint_left.2 (fun d hdS hdT => by
      obtain ⟨hS1, hS2⟩ := Finset.mem_filter.1 hdS
      obtain ⟨hT1, hT2⟩ := Finset.mem_filter.1 hdT
      have hS3 := Fintype.mem_piFinset.1 hS1
      have hT3 := Fintype.mem_piFinset.1 hT1
      apply hST
      apply Finset.Subset.antisymm
      · intro z hz
        obtain ⟨i, hi⟩ := hS2 z hz
        rw [← hi]
        exact hT3 i
      · intro z hz
        obtain ⟨i, hi⟩ := hT2 z hz
        rw [← hi]
        exact hS3 i)

open OMA.S_oeis_a211715 in
theorem OMA.solution : type_of% @OMA.S_oeis_a211715.main := by
  have hc : ∀ n, 1 ≤ n → a n = 10 + 3 * 2 ^ (2 + n) := by
    intro n hn
    rw [kcard211715 n hn]
    have h2 : 2 ^ (2 + n) = 2 * 2 ^ (n + 1) := by ring
    have h3 : 2 ≤ 2 ^ (n + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have q1 : (a 1 : ℚ) = 34 := by
    have h : a 1 = 34 := (hc 1 le_rfl).trans (by norm_num)
    exact_mod_cast h
  have e : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X)) =
      PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 *
          (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * PowerSeries.X ^ 1)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
          (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * PowerSeries.X ^ 2) := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    ring
  have e2 : (2 * PowerSeries.X * (17 - 22 * PowerSeries.X) : PowerSeries ℚ) =
      PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 34
        - PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 44 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 34,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 44]
    ring
  refine ⟨hc, ?_⟩
  refine e.trans (Eq.trans ?_ e2.symm)
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C]
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · rw [if_pos (show (0 : ℕ) = 0 from rfl), if_neg (show ¬ (1 ≤ (0 : ℕ)) by decide),
        if_neg (show ¬ (2 ≤ (0 : ℕ)) by decide), if_neg (show ¬ (1 ≤ (0 : ℕ)) by decide),
        if_neg (show ¬ (2 ≤ (0 : ℕ)) by decide)]
      norm_num
    · rw [if_neg (show ¬ ((1 : ℕ) = 0) by decide), if_pos (show 1 ≤ (1 : ℕ) by decide),
        if_pos (show (1 : ℕ) - 1 = 0 by decide), if_neg (show ¬ (2 ≤ (1 : ℕ)) by decide),
        if_pos (show 1 ≤ (1 : ℕ) by decide), if_pos (show (1 : ℕ) - 1 = 0 by decide),
        if_neg (show ¬ (2 ≤ (1 : ℕ)) by decide), q1]
      norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have n0 : ¬ (k + 2 = 0) := by omega
    have p1 : 1 ≤ k + 2 := by omega
    have p2 : 2 ≤ k + 2 := by omega
    have m1 : ¬ (k + 2 - 1 = 0) := by omega
    rw [if_neg n0, if_pos p1, if_pos p1, if_neg m1, if_neg m1, if_pos p2, if_pos p2,
      show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have q2 : (a 2 : ℚ) = 58 := by
        have h : a 2 = 58 := (hc 2 (by norm_num)).trans (by norm_num)
        exact_mod_cast h
      rw [if_pos (show (0 : ℕ) = 0 from rfl), if_pos (show (0 : ℕ) = 0 from rfl),
        show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl, q2, q1]
      norm_num
    · have h1 := hc (k + 2) (by omega)
      have h2 := hc (k + 1) (by omega)
      have h0 := hc k hk
      have hk0 : ¬ (k = 0) := by omega
      rw [if_neg hk0, if_neg hk0]
      have e3 : (2 : ℕ) ^ (2 + (k + 2)) = 4 * 2 ^ (2 + k) := by ring
      have e4 : (2 : ℕ) ^ (2 + (k + 1)) = 2 * 2 ^ (2 + k) := by ring
      rw [e3] at h1
      rw [e4] at h2
      have g1 : (a (k + 2) : ℚ) = 10 + 3 * (4 * (2 : ℚ) ^ (2 + k)) := by exact_mod_cast h1
      have g2 : (a (k + 1) : ℚ) = 10 + 3 * (2 * (2 : ℚ) ^ (2 + k)) := by exact_mod_cast h2
      have g0 : (a k : ℚ) = 10 + 3 * (2 : ℚ) ^ (2 + k) := by exact_mod_cast h0
      rw [g1, g2, g0]
      ring
