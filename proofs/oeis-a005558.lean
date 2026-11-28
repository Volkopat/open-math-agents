import OMAStatements.S_oeis_a005558

-- Problem: A005558 (n-step walks on the square lattice in the octant 0 <= y <= x): Mathar's recurrence.
-- Credit: @wonsukchoi (the owner of the agent is credited as the solver)
-- Proof: reflection principle for the Weyl chamber of type B2. In the rotated coordinates
-- i = (n+x+y)/2, j = (n+x-y)/2 the two step directions decouple, so the number of octant walks
-- ending at (x,y) is an 8-term alternating sum of products of binomial coefficients (it satisfies
-- the walk recurrence and vanishes on the two walls y = -1 and y = x+1). Summing over the octant
-- telescopes to a(n) = C(n,h)^2 - C(n,h-1) C(n,h+1) with h = ceil(n/2), and the recurrence is an
-- identity of rational functions after expressing everything through C(2m, m).

namespace A005558

open OMA.S_oeis_a005558 Classical

/-- The octant `0 ≤ y ≤ x`. -/
def inR (p : ℤ × ℤ) : Prop := 0 ≤ p.2 ∧ p.2 ≤ p.1

theorem pos_snoc {n : ℕ} (w : Fin n → Fin 4) (d : Fin 4) :
    ∀ k, k ≤ n → walkPos (Fin.snoc (α := fun _ => Fin 4) w d) k = walkPos w k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have h1 : k < n + 1 := by omega
    have h2 : k < n := by omega
    simp only [walkPos, dif_pos h1, dif_pos h2]
    rw [ih (by omega)]
    have : (⟨k, h1⟩ : Fin (n + 1)) = Fin.castSucc ⟨k, h2⟩ := rfl
    rw [this, Fin.snoc_castSucc]

theorem pos_snoc_last {n : ℕ} (w : Fin n → Fin 4) (d : Fin 4) :
    walkPos (Fin.snoc (α := fun _ => Fin 4) w d) (n + 1) =
      ((walkPos w n).1 + (stepDir d).1, (walkPos w n).2 + (stepDir d).2) := by
  have h1 : n < n + 1 := by omega
  simp only [walkPos, dif_pos h1]
  rw [pos_snoc w d n le_rfl]
  have : (⟨n, h1⟩ : Fin (n + 1)) = Fin.last n := rfl
  rw [this, Fin.snoc_last]

theorem octant_snoc {n : ℕ} (w : Fin n → Fin 4) (d : Fin 4) :
    isOctantWalk (Fin.snoc (α := fun _ => Fin 4) w d) ↔
      isOctantWalk w ∧ inR ((walkPos w n).1 + (stepDir d).1, (walkPos w n).2 + (stepDir d).2) := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_⟩
    · have := h k (by omega)
      rwa [pos_snoc w d k hk] at this
    · have := h (n + 1) le_rfl
      rw [pos_snoc_last] at this
      exact this
  · rintro ⟨h, hl⟩ k hk
    rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
    · rw [pos_snoc w d k (by omega)]; exact h k (by omega)
    · have : k = n + 1 := by omega
      subst this
      rw [pos_snoc_last]; exact hl

/-- Number of octant walks of length `n` ending at `p`. -/
noncomputable def E (n : ℕ) (p : ℤ × ℤ) : ℤ :=
  ∑ w : Fin n → Fin 4, if isOctantWalk w ∧ walkPos w n = p then 1 else 0

theorem sum_snoc {n : ℕ} (g : (Fin (n + 1) → Fin 4) → ℤ) :
    ∑ f, g f = ∑ d : Fin 4, ∑ w : Fin n → Fin 4, g (Fin.snoc (α := fun _ => Fin 4) w d) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.snocEquiv (fun _ => Fin 4)) _ _ (fun _ => rfl)).symm

theorem E_succ (n : ℕ) (p : ℤ × ℤ) :
    E (n + 1) p = if inR p then
      ∑ d : Fin 4, E n (p.1 - (stepDir d).1, p.2 - (stepDir d).2) else 0 := by
  unfold E
  rw [sum_snoc]
  split_ifs with hp
  · refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun w _ => ?_
    rw [octant_snoc, pos_snoc_last]
    congr 1
    apply propext
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      refine ⟨h1, ?_⟩
      rw [← h2]; ext <;> simp
    · rintro ⟨h1, h2⟩
      rw [h2]
      refine ⟨⟨h1, ?_⟩, ?_⟩
      · simpa using hp
      · ext <;> simp
  · refine Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have := h1 (n + 1) le_rfl
    rw [h2] at this
    exact hp this

theorem E_zero (p : ℤ × ℤ) : E 0 p = if p = (0, 0) then 1 else 0 := by
  unfold E
  rw [Fintype.sum_unique]
  congr 1
  apply propext
  constructor
  · rintro ⟨-, h⟩; rw [← h]; rfl
  · rintro rfl
    refine ⟨fun k hk => ?_, rfl⟩
    have : k = 0 := by omega
    subst this
    simp [walkPos]

theorem E_out (n : ℕ) (p : ℤ × ℤ) (hp : ¬ inR p) : E n p = 0 := by
  cases n with
  | zero =>
    rw [E_zero, if_neg]
    rintro rfl
    exact hp ⟨le_rfl, le_rfl⟩
  | succ n => rw [E_succ, if_neg hp]


/-- Binomial coefficient with an integer lower index (zero below 0). -/
def cz (L : ℕ) (u : ℤ) : ℤ := if 0 ≤ u then (L.choose u.toNat : ℤ) else 0

theorem cz_nat (L m : ℕ) : cz L m = L.choose m := by simp [cz]

theorem cz_neg (L : ℕ) {u : ℤ} (h : u < 0) : cz L u = 0 := by simp [cz]; omega

theorem cz_big (L : ℕ) {u : ℤ} (h : (L : ℤ) < u) : cz L u = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, u = m := ⟨u.toNat, by omega⟩
  rw [cz_nat, Nat.choose_eq_zero_of_lt (by omega)]; rfl

theorem cz_succ (L : ℕ) (u : ℤ) : cz (L + 1) u = cz L (u - 1) + cz L u := by
  rcases lt_trichotomy u 0 with h | rfl | h
  · rw [cz_neg _ h, cz_neg _ h, cz_neg _ (by omega)]; rfl
  · rw [cz_neg L (show (0 : ℤ) - 1 < 0 by norm_num), show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl,
      cz_nat, cz_nat]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, u = ((m + 1 : ℕ) : ℤ) := ⟨(u - 1).toNat, by omega⟩
    rw [show ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) by push_cast; ring, cz_nat, cz_nat, cz_nat,
      Nat.choose_succ_succ]
    push_cast; ring

theorem cz_symm (L : ℕ) (k : ℤ) : cz L k = cz L (L - k) := by
  rcases lt_or_ge k 0 with h | h
  · rw [cz_neg _ h, cz_big _ (by omega)]
  rcases lt_or_ge (L : ℤ) k with h' | h'
  · rw [cz_big _ h', cz_neg _ (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m := ⟨k.toNat, by omega⟩
  have hm : m ≤ L := by omega
  rw [show (L : ℤ) - m = ((L - m : ℕ) : ℤ) by push_cast [hm]; ring, cz_nat, cz_nat,
    Nat.choose_symm hm]

/-- The reflection formula in the rotated coordinates `i = (n+x+y)/2`, `j = (n+x-y)/2`. -/
def Fq (n : ℕ) (i j : ℤ) : ℤ :=
  (cz n i - cz n (i + 3)) * (cz n j - cz n (j + 1)) -
    (cz n (i + 1) - cz n (i + 2)) * (cz n (j - 1) - cz n (j + 2))

def G (n : ℕ) (x y : ℤ) : ℤ :=
  if ((n : ℤ) + x + y) % 2 = 0 then Fq n (((n : ℤ) + x + y) / 2) (((n : ℤ) + x - y) / 2) else 0

theorem G_succ (n : ℕ) (x y : ℤ) :
    G (n + 1) x y = G n (x - 1) y + G n (x + 1) y + G n x (y - 1) + G n x (y + 1) := by
  unfold G
  push_cast
  by_cases hp : ((n : ℤ) + 1 + x + y) % 2 = 0
  · obtain ⟨i, hi⟩ : ∃ i : ℤ, 2 * i = (n : ℤ) + 1 + x + y := ⟨((n : ℤ) + 1 + x + y) / 2, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j : ℤ, 2 * j = (n : ℤ) + 1 + x - y := ⟨((n : ℤ) + 1 + x - y) / 2, by omega⟩
    rw [if_pos hp, if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      show ((n : ℤ) + 1 + x + y) / 2 = i by omega, show ((n : ℤ) + 1 + x - y) / 2 = j by omega,
      show ((n : ℤ) + (x - 1) + y) / 2 = i - 1 by omega,
      show ((n : ℤ) + (x - 1) - y) / 2 = j - 1 by omega,
      show ((n : ℤ) + (x + 1) + y) / 2 = i by omega,
      show ((n : ℤ) + (x + 1) - y) / 2 = j by omega,
      show ((n : ℤ) + x + (y - 1)) / 2 = i - 1 by omega,
      show ((n : ℤ) + x - (y - 1)) / 2 = j by omega,
      show ((n : ℤ) + x + (y + 1)) / 2 = i by omega,
      show ((n : ℤ) + x - (y + 1)) / 2 = j - 1 by omega]
    unfold Fq
    simp only [cz_succ]
    ring_nf
  · rw [if_neg hp, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring

theorem G_wall1 (n : ℕ) (x : ℤ) : G n x (-1) = 0 := by
  unfold G
  split_ifs with hp
  · rw [show ((n : ℤ) + x - -1) / 2 = ((n : ℤ) + x + -1) / 2 + 1 by omega]
    unfold Fq
    set i := ((n : ℤ) + x + -1) / 2
    rw [show i + 1 - 1 = i by ring, show i + 1 + 1 = i + 2 by ring, show i + 1 + 2 = i + 3 by ring]
    ring
  · rfl

theorem G_wall2 (n : ℕ) (x : ℤ) : G n x (x + 1) = 0 := by
  unfold G
  split_ifs with hp
  · set j := ((n : ℤ) + x - (x + 1)) / 2 with hj
    have h2 : 2 * j + 1 = n := by omega
    have e1 : cz n j = cz n (j + 1) := by rw [cz_symm n j]; congr 1; omega
    have e2 : cz n (j - 1) = cz n (j + 2) := by rw [cz_symm n (j - 1)]; congr 1; omega
    unfold Fq
    rw [e1, e2]
    ring
  · rfl

theorem G_zero (x y : ℤ) (h : inR (x, y)) : G 0 x y = if (x, y) = (0, 0) then 1 else 0 := by
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  unfold G Fq
  push_cast
  split_ifs with hp hz hz
  · simp only [Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    simp only [add_zero, sub_zero, show (0 : ℤ) / 2 = 0 from rfl, zero_add, zero_sub]
    rw [cz_big 0 (by norm_num : ((0 : ℕ) : ℤ) < 3), cz_big 0 (by norm_num : ((0 : ℕ) : ℤ) < 1),
      cz_big 0 (by norm_num : ((0 : ℕ) : ℤ) < 2), show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, cz_nat]
    simp
  · have hne : ¬ (x = 0 ∧ y = 0) := by simpa [Prod.mk.injEq] using hz
    rw [cz_big 0 (by push_cast; omega : ((0 : ℕ) : ℤ) < (0 + x + y) / 2 + 3),
      cz_big 0 (by push_cast; omega : ((0 : ℕ) : ℤ) < (0 + x - y) / 2 + 1),
      cz_big 0 (by push_cast; omega : ((0 : ℕ) : ℤ) < (0 + x + y) / 2 + 1),
      cz_big 0 (by push_cast; omega : ((0 : ℕ) : ℤ) < (0 + x + y) / 2 + 2)]
    rcases Classical.em ((0 + x + y) / 2 = 0) with h0 | h0
    · rw [cz_big 0 (by push_cast; omega : ((0 : ℕ) : ℤ) < (0 + x - y) / 2)]; ring
    · rw [cz_big 0 (by push_cast; omega : ((0 : ℕ) : ℤ) < (0 + x + y) / 2)]; ring
  · exfalso; simp only [Prod.mk.injEq] at hz; omega
  · rfl

theorem stepDir_vals : stepDir 0 = (1, 0) ∧ stepDir 1 = (-1, 0) ∧ stepDir 2 = (0, 1) ∧
    stepDir 3 = (0, -1) := ⟨rfl, rfl, rfl, rfl⟩

theorem E_eq_G (n : ℕ) : ∀ x y : ℤ, inR (x, y) → E n (x, y) = G n x y := by
  induction n with
  | zero => intro x y h; rw [E_zero, G_zero x y h]
  | succ n ih =>
    intro x y h
    rw [E_succ, if_pos h, Fin.sum_univ_four, G_succ]
    obtain ⟨s0, s1, s2, s3⟩ := stepDir_vals
    rw [s0, s1, s2, s3]
    simp only [sub_zero, sub_neg_eq_add]
    obtain ⟨h1, h2⟩ := h
    simp only at h1 h2
    have aux : ∀ u v : ℤ, (¬ inR (u, v) → G n u v = 0) → E n (u, v) = G n u v := by
      intro u v hw
      by_cases hr : inR (u, v)
      · exact ih u v hr
      · rw [E_out n _ hr, hw hr]
    have w1 : ¬ inR (x - 1, y) → G n (x - 1) y = 0 := by
      intro hr
      simp only [inR, not_and, not_le] at hr
      have hxy : x = y := by have := hr h1; omega
      subst hxy
      have := G_wall2 n (x - 1); rwa [sub_add_cancel] at this
    have w2 : ¬ inR (x + 1, y) → G n (x + 1) y = 0 := by
      intro hr
      simp only [inR, not_and, not_le] at hr
      have := hr h1; omega
    have w3 : ¬ inR (x, y - 1) → G n x (y - 1) = 0 := by
      intro hr
      simp only [inR, not_and, not_le] at hr
      have hy : y = 0 := by by_contra hne; have := hr (by omega); omega
      subst hy
      simpa using G_wall1 n x
    have w4 : ¬ inR (x, y + 1) → G n x (y + 1) = 0 := by
      intro hr
      simp only [inR, not_and, not_le] at hr
      have hxy : x = y := by have := hr (by omega); omega
      subst hxy
      exact G_wall2 n x
    rw [aux _ _ w1, aux _ _ w2, aux _ _ w3, aux _ _ w4]

theorem pos_facts {n : ℕ} (w : Fin n → Fin 4) :
    ∀ k, k ≤ n → (walkPos w k).1 + (walkPos w k).2 ≤ k ∧
      ((walkPos w k).1 + (walkPos w k).2 + k) % 2 = 0 := by
  intro k
  induction k with
  | zero => intro _; simp [walkPos]
  | succ k ih =>
    intro hk
    have h2 : k < n := by omega
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    simp only [walkPos, dif_pos h2]
    obtain ⟨s0, s1, s2, s3⟩ := stepDir_vals
    generalize w ⟨k, h2⟩ = d
    fin_cases d
    · simp only [Fin.zero_eta, s0]; push_cast; omega
    · simp only [Fin.mk_one, s1]; push_cast; omega
    · simp only [Fin.reduceFinMk, s2]; push_cast; omega
    · simp only [Fin.reduceFinMk, s3]; push_cast; omega

/-- The index set `h ≤ j ≤ i ≤ n`. -/
def T (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc ((n + 1) / 2) n ×ˢ Finset.Icc ((n + 1) / 2) n).filter (fun t => t.2 ≤ t.1)

def φ (n : ℕ) (t : ℕ × ℕ) : ℤ × ℤ := ((t.1 : ℤ) + t.2 - n, (t.1 : ℤ) - t.2)

theorem a_eq_sum (n : ℕ) : (a n : ℤ) = ∑ t ∈ T n, Fq n t.1 t.2 := by
  have h1 : (a n : ℤ) = ∑ w : Fin n → Fin 4, if isOctantWalk w then 1 else 0 := by
    unfold a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    push_cast; rfl
  have hinj : Set.InjOn (φ n) (T n : Set (ℕ × ℕ)) := by
    rintro ⟨i, j⟩ - ⟨i', j'⟩ - h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    ext <;> simp only <;> omega
  have hmem : ∀ w : Fin n → Fin 4, isOctantWalk w → walkPos w n ∈ (T n).image (φ n) := by
    intro w hw
    obtain ⟨hb, hpar⟩ := pos_facts w n le_rfl
    obtain ⟨hy, hyx⟩ := hw n le_rfl
    set x := (walkPos w n).1
    set y := (walkPos w n).2
    rw [Finset.mem_image]
    refine ⟨((((n : ℤ) + x + y) / 2).toNat, (((n : ℤ) + x - y) / 2).toNat), ?_, ?_⟩
    · simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      omega
    · simp only [φ]
      ext <;> simp only <;> omega
  have h2 : ∑ w : Fin n → Fin 4, (if isOctantWalk w then (1 : ℤ) else 0) =
      ∑ q ∈ (T n).image (φ n), E n q := by
    unfold E
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : isOctantWalk w
    · rw [if_pos hw]
      simp only [hw, true_and]
      rw [Finset.sum_ite_eq, if_pos (hmem w hw)]
    · rw [if_neg hw]
      simp [hw]
  rw [h1, h2, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨i, j⟩ := t
  simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht
  simp only [φ]
  rw [E_eq_G n _ _ (by simp only [inR]; omega)]
  unfold G
  rw [if_pos (by omega), show ((n : ℤ) + ((i : ℤ) + j - n) + (i - j)) / 2 = i by omega,
    show ((n : ℤ) + ((i : ℤ) + j - n) - (i - j)) / 2 = j by omega]

theorem inner_sum (n i h : ℕ) : ∀ N, h ≤ N → ∑ j ∈ Finset.Icc h N, Fq n i j =
    (cz n i - cz n (i + 3)) * (cz n h - cz n (N + 1)) -
      (cz n (i + 1) - cz n (i + 2)) *
        (cz n (h - 1) + cz n h + cz n (h + 1) - cz n N - cz n (N + 1) - cz n (N + 2)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rw [Finset.Icc_self, Finset.sum_singleton]; unfold Fq; ring
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    unfold Fq
    push_cast
    ring_nf

theorem outer_sum (n h : ℕ) : ∀ N, h ≤ N → ∑ i ∈ Finset.Icc h N,
    ((cz n i - cz n (i + 3)) * (cz n h - cz n (i + 1)) -
      (cz n (i + 1) - cz n (i + 2)) *
        (cz n (h - 1) + cz n h + cz n (h + 1) - cz n i - cz n (i + 1) - cz n (i + 2))) =
    cz n h * (cz n h + cz n (h + 1) + cz n (h + 2) - cz n (N + 1) - cz n (N + 2) - cz n (N + 3)) -
      (cz n (h - 1) + cz n h + cz n (h + 1)) * (cz n (h + 1) - cz n (N + 2)) +
      (cz n (N + 3) * cz n (N + 1) - cz n (h + 2) * cz n h) +
      (cz n (h + 1) ^ 2 - cz n (N + 2) ^ 2) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rw [Finset.Icc_self, Finset.sum_singleton]; ring
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring_nf

theorem a_closed (n : ℕ) :
    (a n : ℤ) = cz n ((n + 1) / 2 : ℕ) ^ 2 -
      cz n (((n + 1) / 2 : ℕ) - 1) * cz n (((n + 1) / 2 : ℕ) + 1) := by
  set h := (n + 1) / 2 with hh
  have hhn : h ≤ n ∨ n = 0 := by omega
  rw [a_eq_sum]
  have hT : ∑ t ∈ T n, Fq n t.1 t.2 = ∑ i ∈ Finset.Icc h n, ∑ j ∈ Finset.Icc h i, Fq n i j := by
    unfold T
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
    omega
  rw [hT]
  have hhn' : h ≤ n := by omega
  rw [Finset.sum_congr rfl fun i hi => inner_sum n i h i (Finset.mem_Icc.mp hi).1,
    outer_sum n h n hhn', cz_big n (by omega : (n : ℤ) < n + 1), cz_big n (by omega : (n : ℤ) < n + 2),
    cz_big n (by omega : (n : ℤ) < n + 3)]
  push_cast
  ring

theorem a_even (m : ℕ) : (a (2 * m) : ℚ) =
    ((2 * m).choose m : ℚ) ^ 2 - ((2 * m).choose (m + 1) : ℚ) ^ 2 := by
  have h := a_closed (2 * m)
  rw [show (2 * m + 1) / 2 = m by omega] at h
  rw [cz_symm (2 * m) ((m : ℕ) - 1 : ℤ), show (((2 * m : ℕ) : ℤ) - ((m : ℤ) - 1)) = ((m + 1 : ℕ) : ℤ) by
    push_cast; ring, show ((m : ℕ) : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring, cz_nat, cz_nat] at h
  have := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at this
  rw [this]; ring

theorem a_odd (m : ℕ) : (a (2 * m + 1) : ℚ) =
    ((2 * m + 1).choose (m + 1) : ℚ) ^ 2 -
      ((2 * m + 1).choose (m + 1) : ℚ) * ((2 * m + 1).choose (m + 2) : ℚ) := by
  have h := a_closed (2 * m + 1)
  rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega] at h
  rw [show (((m + 1 : ℕ) : ℤ) - 1) = ((m : ℕ) : ℤ) by push_cast; ring, cz_symm (2 * m + 1) ((m : ℕ) : ℤ),
    show (((2 * m + 1 : ℕ) : ℤ) - ((m : ℕ) : ℤ)) = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
    show ((m + 1 : ℕ) : ℤ) + 1 = ((m + 2 : ℕ) : ℤ) by push_cast; ring, cz_nat, cz_nat] at h
  have := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at this
  rw [this]

theorem r1 (m : ℕ) : ((2 * m).choose (m + 1) : ℚ) * ((m : ℚ) + 1) = ((2 * m).choose m : ℚ) * m := by
  have h := Nat.choose_succ_right_eq (2 * m) m
  rw [show 2 * m - m = m by omega] at h
  exact_mod_cast h

theorem r2 (m : ℕ) : ((2 * m + 1).choose (m + 2) : ℚ) * ((m : ℚ) + 2) =
    ((2 * m + 1).choose (m + 1) : ℚ) * m := by
  have h := Nat.choose_succ_right_eq (2 * m + 1) (m + 1)
  rw [show 2 * m + 1 - (m + 1) = m by omega] at h
  have := congrArg (fun z : ℕ => (z : ℚ)) h
  push_cast at this
  linarith

theorem r3 (m : ℕ) : ((2 * m + 1).choose (m + 1) : ℚ) = ((2 * m).choose m : ℚ) + ((2 * m).choose (m + 1) : ℚ) := by
  rw [Nat.choose_succ_succ]; push_cast; ring

theorem r4 (m : ℕ) : ((2 * (m + 1)).choose (m + 1) : ℚ) = 2 * ((2 * m + 1).choose (m + 1) : ℚ) := by
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.choose_succ_succ, Nat.choose_symm_half]
  push_cast; ring

open OMA.S_oeis_a005558 in
theorem solution : ∀ n : ℕ, 2 ≤ n →
    (2 * (n : ℤ) + 1) * ((n : ℤ) + 3) * ((n : ℤ) + 2) * (a n : ℤ)
      - 4 * (2 * (n : ℤ) ^ 2 + 4 * (n : ℤ) + 3) * (a (n - 1) : ℤ)
      - 16 * (n : ℤ) * (2 * (n : ℤ) + 3) * ((n : ℤ) - 1) * (a (n - 2) : ℤ) = 0 := by
  intro n hn
  suffices h : (2 * (n : ℚ) + 1) * ((n : ℚ) + 3) * ((n : ℚ) + 2) * (a n : ℚ)
      - 4 * (2 * (n : ℚ) ^ 2 + 4 * (n : ℚ) + 3) * (a (n - 1) : ℚ)
      - 16 * (n : ℚ) * (2 * (n : ℚ) + 3) * ((n : ℚ) - 1) * (a (n - 2) : ℚ) = 0 by
    exact_mod_cast h
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * (m + 1) ∨ n = 2 * (m + 1) + 1 := by
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · exact ⟨k - 1, Or.inl (by omega)⟩
    · exact ⟨k - 1, Or.inr (by omega)⟩
  · rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show 2 * (m + 1) - 2 = 2 * m by omega,
      a_even, a_even, a_odd]
    have e1 := r1 m
    have e1' := r1 (m + 1)
    have e2 := r2 m
    have e3 := r3 m
    have e4 := r4 m
    push_cast at e1' ⊢
    generalize ((2 * (m + 1)).choose (m + 1 + 1) : ℚ) = Y' at *
    generalize ((2 * (m + 1)).choose (m + 1) : ℚ) = X' at *
    generalize ((2 * m + 1).choose (m + 2) : ℚ) = W at *
    generalize ((2 * m + 1).choose (m + 1) : ℚ) = Z at *
    generalize ((2 * m).choose (m + 1) : ℚ) = Y at *
    generalize ((2 * m).choose m : ℚ) = X at *
    have hx : (0 : ℚ) ≤ m := Nat.cast_nonneg m
    generalize (m : ℚ) = x at *
    have hY : Y = X * x / (x + 1) := by rw [eq_div_iff (by positivity)]; linarith
    have hW : W = Z * x / (x + 2) := by rw [eq_div_iff (by positivity)]; linarith
    have hY' : Y' = X' * (x + 1) / (x + 2) := by rw [eq_div_iff (by positivity)]; linarith
    subst hY' e4
    subst hW
    subst e3
    subst hY
    field_simp
    ring
  · rw [show 2 * (m + 1) + 1 - 1 = 2 * (m + 1) by omega,
      show 2 * (m + 1) + 1 - 2 = 2 * m + 1 by omega, a_odd, a_even, a_odd]
    have e1' := r1 (m + 1)
    have e1 := r1 m
    have e2 := r2 m
    have e2' := r2 (m + 1)
    have e3 := r3 m
    have e3' := r3 (m + 1)
    have e4 := r4 m
    push_cast at e1' e2' e3' ⊢
    generalize ((2 * (m + 1) + 1).choose (m + 1 + 2) : ℚ) = W' at *
    generalize ((2 * (m + 1) + 1).choose (m + 1 + 1) : ℚ) = Z' at *
    generalize ((2 * (m + 1)).choose (m + 1 + 1) : ℚ) = Y' at *
    generalize ((2 * (m + 1)).choose (m + 1) : ℚ) = X' at *
    generalize ((2 * m + 1).choose (m + 2) : ℚ) = W at *
    generalize ((2 * m + 1).choose (m + 1) : ℚ) = Z at *
    generalize ((2 * m).choose (m + 1) : ℚ) = Y at *
    generalize ((2 * m).choose m : ℚ) = X at *
    have hx : (0 : ℚ) ≤ m := Nat.cast_nonneg m
    generalize (m : ℚ) = x at *
    have hY : Y = X * x / (x + 1) := by rw [eq_div_iff (by positivity)]; linarith
    have hW : W = Z * x / (x + 2) := by rw [eq_div_iff (by positivity)]; linarith
    have hY' : Y' = X' * (x + 1) / (x + 2) := by rw [eq_div_iff (by positivity)]; linarith
    have hW' : W' = Z' * (x + 1) / (x + 3) := by rw [eq_div_iff (by positivity)]; linarith
    subst hW'
    subst e3'
    subst hY'
    subst e4
    subst hW
    subst e3
    subst hY
    field_simp
    ring

end A005558

theorem OMA.solution : type_of% @OMA.S_oeis_a005558.main := A005558.solution
