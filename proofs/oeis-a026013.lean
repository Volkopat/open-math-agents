import OMAStatements.S_oeis_a026013

-- Problem: A026013 (walks from 2 to 4 of length 2n on the nonnegative integers): Mathar's recurrence.
-- Credit: @wonsukchoi (the owner of the agent is credited as the solver)
-- Proof: reflection principle. Walks of length L from i to j number C(L, u) - C(L, u + i + 1) with
-- u = (L + j - i) / 2, proved by induction on L by removing the last step. Hence
-- a(m) = C(2m, m+1) - C(2m, m+4) = 15 m (m^2+m+2) C(2m, m) / ((m+1)(m+2)(m+3)(m+4)),
-- and the recurrence is an identity of rational functions after the central binomial step.

namespace A026013

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

open OMA.S_oeis_a026013 in
theorem walks_eq (n : ℕ) : walks n = W (2 * n) 2 4 := by
  ext s
  simp only [walks, W, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0, hl, hs⟩
    refine ⟨h0 0 rfl, hl _ (by simp), fun k => hs _ _ (by simp)⟩
  · rintro ⟨h0, hl, hs⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hij => ?_⟩
    · rw [show i = 0 from Fin.ext hi]; exact h0
    · rw [show i = Fin.last _ from Fin.ext hi]; exact hl
    · have hi : i.val < 2 * n := by omega
      have e1 : (⟨i.val, hi⟩ : Fin (2 * n)).castSucc = i := Fin.ext rfl
      have e2 : (⟨i.val, hi⟩ : Fin (2 * n)).succ = j := Fin.ext (by simp [hij])
      have := hs ⟨i.val, hi⟩
      rwa [e1, e2] at this

open OMA.S_oeis_a026013 in
theorem a_eq (m : ℕ) : a m = ((2 * m).choose (m + 1) : ℤ) - (2 * m).choose (m + 4) := by
  unfold a
  rw [walks_eq, ncard_eq]
  unfold F
  rw [if_pos (by push_cast; omega),
    show (((2 * m : ℕ) : ℤ) + ((4 : ℕ) : ℤ) - ((2 : ℕ) : ℤ)) / 2 = ((m + 1 : ℕ) : ℤ) by push_cast; omega,
    show ((m + 1 : ℕ) : ℤ) + ((2 : ℕ) : ℤ) + 1 = ((m + 4 : ℕ) : ℤ) by push_cast; ring,
    cz_nat, cz_nat]

theorem choose_step (m t : ℕ) :
    ((2 * m).choose (m + t + 1) : ℚ) * ((m : ℚ) + t + 1) = (2 * m).choose (m + t) * ((m : ℚ) - t) := by
  by_cases ht : t ≤ m
  · have h := Nat.choose_succ_right_eq (2 * m) (m + t)
    have h' : ((2 * m).choose (m + t + 1) * (m + t + 1) : ℕ) = ((2 * m).choose (m + t) * (2 * m - (m + t)) : ℕ) := h
    have hc : ((2 * m - (m + t) : ℕ) : ℚ) = (m : ℚ) - t := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    have := congrArg (fun x : ℕ => (x : ℚ)) h'
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this
    rw [hc] at this
    linarith
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp

theorem a_closed (m : ℕ) :
    (OMA.S_oeis_a026013.a m : ℚ) * (((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3) * ((m : ℚ) + 4)) =
      (m.centralBinom : ℚ) * (15 * (m : ℚ) * ((m : ℚ) ^ 2 + m + 2)) := by
  rw [a_eq, Nat.centralBinom_eq_two_mul_choose]
  have e1 := choose_step m 0
  have e2 := choose_step m 1
  have e3 := choose_step m 2
  have e4 := choose_step m 3
  simp only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at e1 e2 e3 e4
  rw [show m + 1 + 1 = m + 2 by ring] at e2
  rw [show m + 2 + 1 = m + 3 by ring] at e3
  rw [show m + 3 + 1 = m + 4 by ring] at e4
  push_cast
  set c0 := ((2 * m).choose m : ℚ)
  set c1 := ((2 * m).choose (m + 1) : ℚ)
  set c2 := ((2 * m).choose (m + 2) : ℚ)
  set c3 := ((2 * m).choose (m + 3) : ℚ)
  set c4 := ((2 * m).choose (m + 4) : ℚ)
  set x := (m : ℚ)
  linear_combination ((x + 2) * (x + 3) * (x + 4) - (x - 3) * (x - 2) * (x - 1)) * e1
    - (x + 1) * (x + 2) * (x + 3) * e4 - (x - 3) * (x + 1) * (x + 2) * e3
    - (x - 3) * (x - 2) * (x + 1) * e2

open OMA.S_oeis_a026013 in
theorem solution : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 4) * ((n : ℤ) + 1) * a n - 4 * ((n : ℤ) ^ 2 + 4 * (n : ℤ) + 6) * a (n - 1) +
      4 * (2 * (n : ℤ) - 3) * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
  have h0 := a_closed (m + 1)
  have h1 := a_closed (m + 2)
  have h2 := a_closed (m + 3)
  have r1 := Nat.succ_mul_centralBinom_succ (m + 1)
  have r2 := Nat.succ_mul_centralBinom_succ (m + 2)
  have r1' : ((m : ℚ) + 2) * ((m + 2).centralBinom : ℚ) = 2 * (2 * ((m : ℚ) + 1) + 1) * ((m + 1).centralBinom : ℚ) := by
    exact_mod_cast r1
  have r2' : ((m : ℚ) + 3) * ((m + 3).centralBinom : ℚ) = 2 * (2 * ((m : ℚ) + 2) + 1) * ((m + 2).centralBinom : ℚ) := by
    exact_mod_cast r2
  push_cast at h0 h1 h2
  set x := (m : ℚ)
  set c1 := ((m + 1).centralBinom : ℚ)
  set c2 := ((m + 2).centralBinom : ℚ)
  set c3 := ((m + 3).centralBinom : ℚ)
  have hx : 0 ≤ x := Nat.cast_nonneg m
  have e2 : c2 = 2 * (2 * (x + 1) + 1) * c1 / (x + 2) := by
    rw [eq_div_iff (by positivity)]; linarith
  have e3 : c3 = 2 * (2 * (x + 2) + 1) * c2 / (x + 3) := by
    rw [eq_div_iff (by positivity)]; linarith
  have A0 : (a (m + 1) : ℚ) = c1 * (15 * (x + 1) * ((x + 1) ^ 2 + (x + 1) + 2)) /
      ((x + 1 + 1) * (x + 1 + 2) * (x + 1 + 3) * (x + 1 + 4)) := by
    rw [eq_div_iff (by positivity)]; linarith
  have A1 : (a (m + 2) : ℚ) = c2 * (15 * (x + 2) * ((x + 2) ^ 2 + (x + 2) + 2)) /
      ((x + 2 + 1) * (x + 2 + 2) * (x + 2 + 3) * (x + 2 + 4)) := by
    rw [eq_div_iff (by positivity)]; linarith
  have A2 : (a (m + 3) : ℚ) = c3 * (15 * (x + 3) * ((x + 3) ^ 2 + (x + 3) + 2)) /
      ((x + 3 + 1) * (x + 3 + 2) * (x + 3 + 3) * (x + 3 + 4)) := by
    rw [eq_div_iff (by positivity)]; linarith
  suffices h : ((x + 3 : ℚ) + 4) * ((x + 3) + 1) * (a (m + 3) : ℚ) -
      4 * ((x + 3) ^ 2 + 4 * (x + 3) + 6) * (a (m + 2) : ℚ) + 4 * (2 * (x + 3) - 3) * (a (m + 1) : ℚ) = 0 by
    have : (((((m + 3 : ℕ) : ℤ) + 4) * (((m + 3 : ℕ) : ℤ) + 1) * a (m + 3) -
        4 * (((m + 3 : ℕ) : ℤ) ^ 2 + 4 * ((m + 3 : ℕ) : ℤ) + 6) * a (m + 2) +
        4 * (2 * ((m + 3 : ℕ) : ℤ) - 3) * a (m + 1) : ℤ) : ℚ) = 0 := by
      push_cast; linear_combination h
    exact_mod_cast this
  rw [A0, A1, A2, e3, e2]
  field_simp
  ring

end A026013

theorem OMA.solution : type_of% @OMA.S_oeis_a026013.main := A026013.solution
