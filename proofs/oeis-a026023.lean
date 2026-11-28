import OMAStatements.S_oeis_a026023

-- Problem: A026023 (walks of length n from height 3 on the nonnegative integers, steps +-1): Mathar's recurrence.
-- Credit: @wonsukchoi (the owner of the agent is credited as the solver)
-- Proof: every walk extends in two ways except those ending at 0, so V(n+1) = 2 V(n) - W(n,3,0),
-- where W(n,3,0) is given by the reflection principle. Induction gives V(2m) = C(2m+2, m) and
-- V(2m+1) = 2 C(2m+2, m); the recurrence is then a rational identity in these binomials.

namespace A026023

/-- ℕ-valued walks of length `L` from `i` to `j` with steps `±1`. -/
def W (L i j : ℕ) : Set (Fin (L + 1) → ℕ) :=
  {s | s 0 = i ∧ s (Fin.last L) = j ∧ ∀ k : Fin L, |(s k.succ : ℤ) - s k.castSucc| = 1}

theorem W_succ (L i j : ℕ) :
    W (L + 1) i j = (fun t => Fin.snoc (α := fun _ => ℕ) t j) ''
      (W L i (j + 1) ∪ {t | 1 ≤ j ∧ t ∈ W L i (j - 1)}) := by
  ext s
  simp only [W, Set.mem_image, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0, hl, hs⟩
    refine ⟨Fin.init s, ?_, ?_⟩
    · have h0' : Fin.init s 0 = i := by simpa [Fin.init] using h0
      have hs' : ∀ k : Fin L, |((Fin.init s) k.succ : ℤ) - (Fin.init s) k.castSucc| = 1 := by
        intro k
        have := hs k.castSucc
        rw [Fin.succ_castSucc] at this
        simp only [Fin.init]; exact this
      have hlast := hs (Fin.last L)
      rw [Fin.succ_last, hl] at hlast
      have hli : Fin.init s (Fin.last L) = s (Fin.last L).castSucc := rfl
      rcases (abs_eq zero_le_one).mp hlast with h | h
      · right
        refine ⟨by omega, h0', ?_, hs'⟩
        rw [hli]; omega
      · left
        refine ⟨h0', ?_, hs'⟩
        rw [hli]; omega
    · rw [← hl]; exact Fin.snoc_init_self s
  · rintro ⟨t, ht, rfl⟩
    have key : t 0 = i ∧ (∀ k : Fin L, |(t k.succ : ℤ) - t k.castSucc| = 1) ∧
        |(j : ℤ) - t (Fin.last L)| = 1 := by
      rcases ht with ⟨a, b, c⟩ | ⟨hj, a, b, c⟩
      · refine ⟨a, c, ?_⟩
        rw [b]; push_cast; rw [show (j : ℤ) - (j + 1) = -1 by ring]; simp
      · refine ⟨a, c, ?_⟩
        rw [b, Nat.cast_sub hj]; push_cast; rw [show (j : ℤ) - (j - 1) = 1 by ring]; simp
    obtain ⟨a, c, d⟩ := key
    refine ⟨?_, by simp, ?_⟩
    · have : (0 : Fin (L + 2)) = Fin.castSucc 0 := rfl
      rw [this, Fin.snoc_castSucc]; exact a
    · intro k
      refine Fin.lastCases ?_ (fun k' => ?_) k
      · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]; exact d
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]; exact c k'

theorem W_zero (i j : ℕ) : W 0 i j = if i = j then {fun _ => i} else ∅ := by
  ext s
  simp only [W]
  split_ifs with h
  · subst h
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h0, -, -⟩; funext x; rw [Fin.fin_one_eq_zero x]; exact h0
    · rintro rfl; exact ⟨rfl, rfl, fun k => k.elim0⟩
  · simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h0, hl, -⟩
    exact h (h0.symm.trans hl)

theorem W_finite (L i j : ℕ) : (W L i j).Finite := by
  induction L generalizing j with
  | zero => rw [W_zero]; split_ifs <;> simp
  | succ L ih =>
    rw [W_succ]
    exact ((ih (j + 1)).union ((ih (j - 1)).subset fun t ht => ht.2)).image _

theorem ncard_succ (L i j : ℕ) :
    (W (L + 1) i j).ncard = (W L i (j + 1)).ncard + (if 1 ≤ j then (W L i (j - 1)).ncard else 0) := by
  have inj : Function.Injective (fun t : Fin (L + 1) → ℕ => Fin.snoc (α := fun _ => ℕ) t j) := by
    intro t1 t2 h
    have := congrArg Fin.init h
    simpa [Fin.init_snoc] using this
  have disj : Disjoint (W L i (j + 1)) {t | 1 ≤ j ∧ t ∈ W L i (j - 1)} := by
    rw [Set.disjoint_left]
    rintro t ⟨-, h1, -⟩ ⟨hj, -, h2, -⟩
    omega
  rw [W_succ, Set.ncard_image_of_injective _ inj,
    Set.ncard_union_eq disj (W_finite _ _ _) ((W_finite L i (j - 1)).subset fun t ht => ht.2)]
  congr 1
  split_ifs with hj
  · congr 1; ext t; simp [hj]
  · have : {t | 1 ≤ j ∧ t ∈ W L i (j - 1)} = ∅ := by ext t; simp [hj]
    rw [this, Set.ncard_empty]

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

/-- The reflection-principle count. -/
def F (L i j : ℕ) : ℤ :=
  if ((L : ℤ) + i + j) % 2 = 0 then
    cz L (((L : ℤ) + j - i) / 2) - cz L (((L : ℤ) + j - i) / 2 + i + 1)
  else 0

theorem ncard_eq (L i j : ℕ) : ((W L i j).ncard : ℤ) = F L i j := by
  induction L generalizing j with
  | zero =>
    rw [W_zero]
    unfold F
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, Set.ncard_singleton, if_pos (by omega),
        show ((0 : ℕ) : ℤ) + i - i = 0 by simp, show (0 : ℤ) / 2 = 0 by rfl,
        cz_big 0 (by omega : ((0 : ℕ) : ℤ) < 0 + i + 1)]
      have := cz_nat 0 0
      simp_all
    · rw [if_neg hij, Set.ncard_empty]
      split_ifs with hp
      · have hu : ((0 : ℕ) : ℤ) + j - i ≠ 0 := by push_cast; omega
        rcases lt_or_gt_of_ne (show ((0 : ℕ) + (j : ℤ) - i) / 2 ≠ 0 by push_cast at hp ⊢; omega)
          with h | h
        · rw [cz_neg _ h, cz_big _ (by push_cast at h ⊢; omega)]; rfl
        · rw [cz_big _ (by push_cast at h ⊢; omega), cz_big _ (by push_cast at h ⊢; omega)]; rfl
      · rfl
  | succ L ih =>
    rw [ncard_succ]
    push_cast
    simp only [ih]
    unfold F
    by_cases hp : (((L + 1 : ℕ) : ℤ) + i + j) % 2 = 0
    · rw [if_pos hp]
      set v := (((L + 1 : ℕ) : ℤ) + j - i) / 2 with hv
      have h2 : 2 * v = ((L + 1 : ℕ) : ℤ) + j - i := by push_cast at hp hv ⊢; omega
      rw [if_pos (by push_cast at hp ⊢; omega),
        show ((L : ℤ) + ((j + 1 : ℕ) : ℤ) - i) / 2 = v by push_cast at h2 ⊢; omega,
        cz_succ, cz_succ, show v + i + 1 - 1 = v + i by ring]
      by_cases hj : 1 ≤ j
      · rw [if_pos hj, Nat.cast_sub hj, if_pos (by push_cast at hp ⊢; omega),
          show ((L : ℤ) + ((j : ℤ) - ((1 : ℕ) : ℤ)) - i) / 2 = v - 1 by push_cast at h2 ⊢; omega,
          show v - 1 + i + 1 = v + i by ring]
        ring
      · have hj0 : j = 0 := by omega
        subst hj0
        rw [if_neg hj, cz_symm L (v - 1), show (L : ℤ) - (v - 1) = v + i by push_cast at h2; omega]
        ring
    · rw [if_neg hp, if_neg (by push_cast at hp ⊢; omega)]
      by_cases hj : 1 ≤ j
      · rw [if_pos hj, Nat.cast_sub hj, if_neg (by push_cast at hp ⊢; omega)]; simp
      · rw [if_neg hj]; simp

/-- Walks of length `n` from height 3 with any endpoint. -/
def V (n : ℕ) : Set (Fin (n + 1) → ℕ) :=
  {s | s 0 = 3 ∧ ∀ k : Fin n, |(s k.succ : ℤ) - s k.castSucc| = 1}

def up {n : ℕ} (t : Fin (n + 1) → ℕ) : Fin (n + 2) → ℕ :=
  Fin.snoc (α := fun _ => ℕ) t (t (Fin.last n) + 1)

def dn {n : ℕ} (t : Fin (n + 1) → ℕ) : Fin (n + 2) → ℕ :=
  Fin.snoc (α := fun _ => ℕ) t (t (Fin.last n) - 1)

theorem snoc_mem {n : ℕ} {t : Fin (n + 1) → ℕ} (ht : t ∈ V n) (v : ℕ)
    (hv : |(v : ℤ) - t (Fin.last n)| = 1) : Fin.snoc (α := fun _ => ℕ) t v ∈ V (n + 1) := by
  obtain ⟨a, c⟩ := ht
  refine ⟨?_, ?_⟩
  · have : (0 : Fin (n + 2)) = Fin.castSucc 0 := rfl
    rw [this, Fin.snoc_castSucc]; exact a
  · intro k
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]; exact hv
    · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]; exact c k'

theorem V_succ (n : ℕ) : V (n + 1) = up '' V n ∪ dn '' {t | t ∈ V n ∧ t (Fin.last n) ≠ 0} := by
  ext s
  constructor
  · rintro ⟨h0, hs⟩
    have hlast := hs (Fin.last n)
    rw [Fin.succ_last] at hlast
    have h0' : Fin.init s 0 = 3 := by simpa [Fin.init] using h0
    have hs' : ∀ k : Fin n, |((Fin.init s) k.succ : ℤ) - (Fin.init s) k.castSucc| = 1 := by
      intro k
      have := hs k.castSucc
      rw [Fin.succ_castSucc] at this
      simp only [Fin.init]; exact this
    have hli : Fin.init s (Fin.last n) = s (Fin.last n).castSucc := rfl
    rcases (abs_eq zero_le_one).mp hlast with h | h
    · left
      refine ⟨Fin.init s, ⟨h0', hs'⟩, ?_⟩
      have h' : (s (Fin.last (n + 1)) : ℤ) - (s (Fin.last n).castSucc : ℤ) = 1 := h
      have : s (Fin.last (n + 1)) = Fin.init s (Fin.last n) + 1 := by rw [hli]; omega
      simp only [up]; rw [← this]; exact Fin.snoc_init_self s
    · right
      have h' : (s (Fin.last (n + 1)) : ℤ) - (s (Fin.last n).castSucc : ℤ) = -1 := h
      refine ⟨Fin.init s, ⟨⟨h0', hs'⟩, by rw [hli]; omega⟩, ?_⟩
      have : s (Fin.last (n + 1)) = Fin.init s (Fin.last n) - 1 := by rw [hli]; omega
      simp only [dn]; rw [← this]; exact Fin.snoc_init_self s
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ⟨ht, hne⟩, rfl⟩)
    · exact snoc_mem ht _ (by push_cast; rw [show ((t (Fin.last n) : ℤ) + 1 - t (Fin.last n)) = 1 by ring]; simp)
    · exact snoc_mem ht _ (by
        rw [Nat.cast_sub (by omega)]; push_cast
        rw [show ((t (Fin.last n) : ℤ) - 1 - t (Fin.last n)) = -1 by ring]; simp)

theorem V_zero : V 0 = {fun _ => 3} := by
  ext s
  simp only [V, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h0, -⟩; funext x; rw [Fin.fin_one_eq_zero x]; exact h0
  · rintro rfl; exact ⟨rfl, fun k => k.elim0⟩

theorem V_finite (n : ℕ) : (V n).Finite := by
  induction n with
  | zero => rw [V_zero]; exact Set.finite_singleton _
  | succ n ih =>
    rw [V_succ]
    exact (ih.image _).union ((ih.subset fun t ht => ht.1).image _)

theorem W_sub (n : ℕ) : W n 3 0 ⊆ V n := fun _ hs => ⟨hs.1, hs.2.2⟩

theorem ncard_V_succ (n : ℕ) :
    ((V (n + 1)).ncard : ℤ) = 2 * (V n).ncard - (W n 3 0).ncard := by
  have injU : Function.Injective (@up n) := by
    intro t1 t2 h
    have := congrArg Fin.init h
    simpa [up, Fin.init_snoc] using this
  have injD : Function.Injective (@dn n) := by
    intro t1 t2 h
    have := congrArg Fin.init h
    simpa [dn, Fin.init_snoc] using this
  have hset : {t | t ∈ V n ∧ t (Fin.last n) ≠ 0} = V n \ W n 3 0 := by
    ext t
    simp only [V, W, Set.mem_setOf_eq, Set.mem_diff]
    tauto
  have disj : Disjoint (up '' V n) (dn '' {t | t ∈ V n ∧ t (Fin.last n) ≠ 0}) := by
    rw [Set.disjoint_left]
    rintro s ⟨t, -, rfl⟩ ⟨t', ⟨-, hne⟩, h⟩
    have h1 := congrArg Fin.init h
    simp only [up, dn, Fin.init_snoc] at h1
    subst h1
    have h2 := congrArg (fun s => s (Fin.last (n + 1))) h
    simp only [up, dn, Fin.snoc_last] at h2
    omega
  rw [V_succ, Set.ncard_union_eq disj ((V_finite n).image _)
      (((V_finite n).subset fun t ht => ht.1).image _),
    Set.ncard_image_of_injective _ injU, Set.ncard_image_of_injective _ injD, hset,
    Set.ncard_diff (W_sub n) ((V_finite n).subset (W_sub n))]
  have := Set.ncard_le_ncard (W_sub n) (V_finite n)
  push_cast [this]
  ring

theorem closed (m : ℕ) : ((V (2 * m)).ncard : ℤ) = (2 * m + 2).choose m ∧
    ((V (2 * m + 1)).ncard : ℤ) = 2 * (2 * m + 2).choose m := by
  induction m with
  | zero =>
    have h0 : (V 0).ncard = 1 := by rw [V_zero, Set.ncard_singleton]
    have hW : (W 0 3 0).ncard = 0 := by rw [W_zero, if_neg (by norm_num), Set.ncard_empty]
    refine ⟨by simp [h0], ?_⟩
    rw [ncard_V_succ, h0, hW]; simp
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hA : ((V (2 * (m + 1))).ncard : ℤ) = (2 * (m + 1) + 2).choose (m + 1) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, ncard_V_succ, ih2, ncard_eq]
      unfold F
      rw [if_pos (by push_cast; omega),
        show (((2 * m + 1 : ℕ) : ℤ) + ((0 : ℕ) : ℤ) - ((3 : ℕ) : ℤ)) / 2 = (m : ℤ) - 1 by push_cast; omega,
        show (m : ℤ) - 1 + ((3 : ℕ) : ℤ) + 1 = (m : ℤ) + 3 by push_cast; ring]
      have s1 : cz (2 * m + 1) ((m : ℤ) + 3) = cz (2 * m + 1) ((m : ℤ) - 2) := by
        rw [cz_symm]; congr 1; push_cast; ring
      have s2 : cz (2 * m + 1) ((m : ℤ) + 1) = cz (2 * m + 1) (m : ℤ) := by
        rw [cz_symm]; congr 1; push_cast; ring
      rw [show 2 * m + 1 + 1 + 2 = 2 * m + 1 + 1 + 1 + 1 by ring, show 2 * m + 2 = 2 * m + 1 + 1 by ring,
        ← cz_nat, ← cz_nat]
      generalize 2 * m + 1 = N at s1 s2 ⊢
      simp only [cz_succ]
      push_cast
      ring_nf
      ring_nf at s1 s2
      linarith [s1, s2]
    refine ⟨hA, ?_⟩
    rw [show 2 * (m + 1) + 1 = 2 * (m + 1) + 1 by rfl, ncard_V_succ, hA, ncard_eq]
    unfold F
    rw [if_neg (by push_cast; omega)]
    ring

open OMA.S_oeis_a026023 in
theorem walks_eq (n : ℕ) : walks n = V n := by
  ext s
  simp only [walks, V, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0, hs⟩
    exact ⟨h0 0 rfl, fun k => hs _ _ (by simp)⟩
  · rintro ⟨h0, hs⟩
    refine ⟨fun i hi => ?_, fun i j hij => ?_⟩
    · rw [show i = 0 from Fin.ext hi]; exact h0
    · have hi : i.val < n := by omega
      have e1 : (⟨i.val, hi⟩ : Fin n).castSucc = i := Fin.ext rfl
      have e2 : (⟨i.val, hi⟩ : Fin n).succ = j := Fin.ext (by simp [hij])
      have := hs ⟨i.val, hi⟩
      rwa [e1, e2] at this

theorem rD (m : ℕ) : ((2 * m + 4).choose (m + 1) : ℚ) * (((m : ℚ) + 1) * ((m : ℚ) + 3)) =
    ((2 * m + 2).choose m : ℚ) * ((2 * (m : ℚ) + 3) * (2 * (m : ℚ) + 4)) := by
  have h1 := Nat.add_one_mul_choose_eq (2 * m + 3) m
  have h2 := Nat.choose_mul_succ_eq (2 * m + 2) m
  rw [show 2 * m + 2 + 1 - m = m + 3 by omega] at h2
  have e1 : ((2 * m + 3 + 1 : ℕ) : ℚ) * ((2 * m + 3).choose m : ℚ) =
      ((2 * m + 3 + 1).choose (m + 1) : ℚ) * ((m + 1 : ℕ) : ℚ) := by exact_mod_cast h1
  have e2 : ((2 * m + 2).choose m : ℚ) * ((2 * m + 2 + 1 : ℕ) : ℚ) =
      ((2 * m + 2 + 1).choose m : ℚ) * ((m + 3 : ℕ) : ℚ) := by exact_mod_cast h2
  push_cast at e1 e2
  rw [show 2 * m + 3 + 1 = 2 * m + 4 by ring] at e1
  rw [show 2 * m + 2 + 1 = 2 * m + 3 by ring] at e2
  linear_combination (-((m : ℚ) + 3)) * e1 - (2 * (m : ℚ) + 4) * e2

open OMA.S_oeis_a026023 in
theorem solution : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 4) * ((n : ℤ) - 1) * a n + ((n : ℤ) - 1) * ((n : ℤ) + 1) * a (n - 1) -
      2 * ((n : ℤ) + 1) * (2 * (n : ℤ) + 1) * a (n - 2) - 4 * ((n : ℤ) - 1) * ((n : ℤ) + 1) * a (n - 3) = 0 := by
  intro n hn
  have ha : ∀ k, a k = ((V k).ncard : ℤ) := fun k => by unfold a; rw [walks_eq]
  simp only [ha]
  suffices h : ((n : ℚ) + 4) * ((n : ℚ) - 1) * ((V n).ncard : ℚ) + ((n : ℚ) - 1) * ((n : ℚ) + 1) * ((V (n - 1)).ncard : ℚ) -
      2 * ((n : ℚ) + 1) * (2 * (n : ℚ) + 1) * ((V (n - 2)).ncard : ℚ) -
      4 * ((n : ℚ) - 1) * ((n : ℚ) + 1) * ((V (n - 3)).ncard : ℚ) = 0 by exact_mod_cast h
  have cq : ∀ m, ((V (2 * m)).ncard : ℚ) = (2 * m + 2).choose m ∧
      ((V (2 * m + 1)).ncard : ℚ) = 2 * (2 * m + 2).choose m := fun m => by
    obtain ⟨h1, h2⟩ := closed m
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m + 3 ∨ n = 2 * m + 4 := by
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · exact ⟨k - 2, Or.inr (by omega)⟩
    · exact ⟨k - 1, Or.inl (by omega)⟩
  · rw [show 2 * m + 3 - 1 = 2 * (m + 1) by omega, show 2 * m + 3 - 2 = 2 * m + 1 by omega,
      show 2 * m + 3 - 3 = 2 * m by omega, show 2 * m + 3 = 2 * (m + 1) + 1 by omega,
      (cq (m + 1)).1, (cq (m + 1)).2, (cq m).1, (cq m).2,
      show 2 * (m + 1) + 2 = 2 * m + 4 by ring]
    have e := rD m
    push_cast
    generalize ((2 * m + 4).choose (m + 1) : ℚ) = B at *
    generalize ((2 * m + 2).choose m : ℚ) = A at *
    linear_combination 12 * e
  · rw [show 2 * m + 4 - 1 = 2 * (m + 1) + 1 by omega, show 2 * m + 4 - 2 = 2 * (m + 1) by omega,
      show 2 * m + 4 - 3 = 2 * m + 1 by omega, show 2 * m + 4 = 2 * (m + 2) by omega,
      (cq (m + 2)).1, (cq (m + 1)).1, (cq (m + 1)).2, (cq m).2,
      show 2 * (m + 1) + 2 = 2 * m + 4 by ring, show 2 * (m + 2) + 2 = 2 * (m + 1) + 4 by ring]
    have e := rD m
    have e' := rD (m + 1)
    push_cast at e' ⊢
    rw [show 2 * (m + 1) + 2 = 2 * m + 4 by ring] at e'
    generalize ((2 * (m + 1) + 4).choose (m + 1 + 1) : ℚ) = C at *
    generalize ((2 * m + 4).choose (m + 1) : ℚ) = B at *
    generalize ((2 * m + 2).choose m : ℚ) = A at *
    have hx : (0 : ℚ) ≤ m := Nat.cast_nonneg m
    generalize (m : ℚ) = x at *
    have hB : B = A * ((2 * x + 3) * (2 * x + 4)) / ((x + 1) * (x + 3)) := by
      rw [eq_div_iff (by positivity)]; linarith
    have hC : C = B * ((2 * (x + 1) + 3) * (2 * (x + 1) + 4)) / ((x + 1 + 1) * (x + 1 + 3)) := by
      rw [eq_div_iff (by positivity)]; linarith
    subst hC
    subst hB
    field_simp
    ring

end A026023

theorem OMA.solution : type_of% @OMA.S_oeis_a026023.main := A026023.solution
