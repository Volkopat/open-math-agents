import OMAStatements.S_oeis_a166213

-- Credit: @Dariusthedoggie
-- Proof: reduce by 120-degree rotational symmetry to 5 orbit variables, evaluate the nested lattice sum explicitly mod 6, and verify the recurrence and g.f.

namespace OMA.P166213

open OMA.S_oeis_a166213 PowerSeries Finset

/-- Orbit index of each cell under 120-degree rotation. -/
def orb (p : Cell) : Fin 5 :=
  if p.1.1 = 4 ∨ p.1.2.1 = 4 ∨ p.1.2.2 = 4 then 0
  else if (p.1.1 = 3 ∧ p.1.2.1 = 1) ∨ (p.1.2.1 = 3 ∧ p.1.2.2 = 1) ∨ (p.1.2.2 = 3 ∧ p.1.1 = 1) then 1
  else if (p.1.1 = 2 ∧ p.1.2.1 = 2) ∨ (p.1.2.1 = 2 ∧ p.1.2.2 = 2) ∨ (p.1.2.2 = 2 ∧ p.1.1 = 2) then 2
  else if (p.1.1 = 1 ∧ p.1.2.1 = 3) ∨ (p.1.2.1 = 1 ∧ p.1.2.2 = 3) ∨ (p.1.2.2 = 1 ∧ p.1.1 = 3) then 3
  else 4

/-- Canonical representative of each rotation orbit. -/
def rep : Fin 5 → Cell
  | 0 => ⟨(4, 0, 0), by decide⟩
  | 1 => ⟨(3, 1, 0), by decide⟩
  | 2 => ⟨(2, 2, 0), by decide⟩
  | 3 => ⟨(1, 3, 0), by decide⟩
  | 4 => ⟨(2, 1, 1), by decide⟩

lemma orb_rep : ∀ i : Fin 5, orb (rep i) = i := by decide
lemma orb_rot : ∀ p : Cell, orb (rot p) = orb p := by decide
lemma rot_orbit : ∀ p : Cell,
    p = rep (orb p) ∨ p = rot (rep (orb p)) ∨ p = rot (rot (rep (orb p))) := by decide

/-- Number of cells in orbit `i` equal to or adjacent to `p`. -/
def coeff (p : Cell) (i : Fin 5) : ℕ :=
  (Finset.univ.filter (fun q : Cell => (q = p ∨ adj p q) ∧ orb q = i)).card

lemma coeff_orb0 : ∀ p : Cell, orb p = 0 →
    coeff p 0 = 1 ∧ coeff p 1 = 1 ∧ coeff p 2 = 0 ∧ coeff p 3 = 1 ∧ coeff p 4 = 0 := by decide

lemma coeff_orb1 : ∀ p : Cell, orb p = 1 →
    coeff p 0 = 1 ∧ coeff p 1 = 1 ∧ coeff p 2 = 1 ∧ coeff p 3 = 1 ∧ coeff p 4 = 1 := by decide

lemma coeff_orb2 : ∀ p : Cell, orb p = 2 →
    coeff p 0 = 0 ∧ coeff p 1 = 1 ∧ coeff p 2 = 1 ∧ coeff p 3 = 1 ∧ coeff p 4 = 2 := by decide

lemma coeff_orb3 : ∀ p : Cell, orb p = 3 →
    coeff p 0 = 1 ∧ coeff p 1 = 1 ∧ coeff p 2 = 1 ∧ coeff p 3 = 1 ∧ coeff p 4 = 1 := by decide

lemma coeff_orb4 : ∀ p : Cell, orb p = 4 →
    coeff p 0 = 0 ∧ coeff p 1 = 1 ∧ coeff p 2 = 2 ∧ coeff p 3 = 1 ∧ coeff p 4 = 3 := by decide

lemma nbrSum_comp {n : ℕ} (v : Fin 5 → Fin (n + 1)) (p : Cell) :
    nbrSum (fun q => v (orb q)) p = ∑ i : Fin 5, coeff p i * (v i : ℕ) := by
  unfold nbrSum coeff
  have h1 : ∀ q : Cell,
      (if q = p ∨ adj p q then (v (orb q) : ℕ) else 0) =
      ∑ i : Fin 5, if (q = p ∨ adj p q) ∧ orb q = i then (v i : ℕ) else 0 := by
    intro q
    rw [Finset.sum_eq_single (orb q)]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]

/-- Reduced orbit-tuple condition equivalent to `valid n`. -/
def valid5 (n : ℕ) (v : Fin 5 → Fin (n + 1)) : Prop :=
  (v 0 : ℕ) + (v 1 : ℕ) + (v 2 : ℕ) + (v 3 : ℕ) + (v 4 : ℕ) ≤ n ∧
  (v 1 : ℕ) + 2 * (v 2 : ℕ) + (v 3 : ℕ) + 3 * (v 4 : ℕ) ≤ n

instance (n : ℕ) (v : Fin 5 → Fin (n + 1)) : Decidable (valid5 n v) := by
  unfold valid5
  infer_instance

lemma valid_iff_valid5 {n : ℕ} (v : Fin 5 → Fin (n + 1)) :
    valid n (fun q => v (orb q)) ↔ valid5 n v := by
  constructor
  · rintro ⟨_, hsum⟩
    refine ⟨?_, ?_⟩
    · have h := hsum (rep 1)
      rw [nbrSum_comp, Fin.sum_univ_five] at h
      have hc := coeff_orb1 (rep 1) (orb_rep 1)
      rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2] at h
      omega
    · have h := hsum (rep 4)
      rw [nbrSum_comp, Fin.sum_univ_five] at h
      have hc := coeff_orb4 (rep 4) (orb_rep 4)
      rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2] at h
      omega
  · rintro ⟨h1, h2⟩
    refine ⟨fun p => by dsimp; rw [orb_rot], fun p => ?_⟩
    rw [nbrSum_comp, Fin.sum_univ_five]
    have hp : orb p = 0 ∨ orb p = 1 ∨ orb p = 2 ∨ orb p = 3 ∨ orb p = 4 := by
      generalize orb p = i; fin_cases i <;> simp
    rcases hp with h | h | h | h | h
    · have hc := coeff_orb0 p h; rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2]; omega
    · have hc := coeff_orb1 p h; rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2]; omega
    · have hc := coeff_orb2 p h; rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2]; omega
    · have hc := coeff_orb3 p h; rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2]; omega
    · have hc := coeff_orb4 p h; rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2]; omega

lemma a_eq_card5 (n : ℕ) :
    a n = (Finset.univ.filter (valid5 n)).card := by
  unfold a
  apply Finset.card_bij (fun f _ => fun i => f (rep i))
  · intro f hf
    rw [Finset.mem_filter] at hf ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hrot : ∀ p : Cell, f p = f (rep (orb p)) := by
      intro p
      rcases rot_orbit p with h | h | h
      · conv_lhs => rw [h]
      · conv_lhs => rw [h, hf.2.1]
      · conv_lhs => rw [h, hf.2.1, hf.2.1]
    have hfun : (fun q => f (rep (orb q))) = f := funext (fun q => (hrot q).symm)
    rw [← valid_iff_valid5, hfun]
    exact hf.2
  · intro f1 hf1 f2 hf2 heq
    rw [Finset.mem_filter] at hf1 hf2
    funext p
    have h1 : f1 p = f1 (rep (orb p)) := by
      rcases rot_orbit p with h | h | h
      · conv_lhs => rw [h]
      · conv_lhs => rw [h, hf1.2.1]
      · conv_lhs => rw [h, hf1.2.1, hf1.2.1]
    have h2 : f2 p = f2 (rep (orb p)) := by
      rcases rot_orbit p with h | h | h
      · conv_lhs => rw [h]
      · conv_lhs => rw [h, hf2.2.1]
      · conv_lhs => rw [h, hf2.2.1, hf2.2.1]
    rw [h1, h2]
    exact congrFun heq (orb p)
  · intro v hv
    rw [Finset.mem_filter] at hv
    refine ⟨fun q => v (orb q), ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (valid_iff_valid5 v).mpr hv.2⟩
    · funext i
      dsimp
      rw [orb_rep]

lemma a_eq_sum5 (n : ℕ) :
    a n = ∑ x4 ∈ range (n + 1), ∑ x2 ∈ range (n + 1), ∑ x1 ∈ range (n + 1),
      ∑ x3 ∈ range (n + 1), ∑ x0 ∈ range (n + 1),
        if x0 + x1 + x2 + x3 + x4 ≤ n ∧ x1 + 2 * x2 + x3 + 3 * x4 ≤ n then 1 else 0 := by
  rw [a_eq_card5, Finset.card_filter]
  let e : (Fin 5 → Fin (n + 1)) ≃
      Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) :=
    { toFun := fun v => (v 4, v 2, v 1, v 3, v 0)
      invFun := fun t i => match i with
        | 0 => t.2.2.2.2
        | 1 => t.2.2.1
        | 2 => t.2.1
        | 3 => t.2.2.2.1
        | 4 => t.1
      left_inv := fun v => by funext i; fin_cases i <;> rfl
      right_inv := fun ⟨_, _, _, _, _⟩ => rfl }
  rw [← e.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  have hconv :
      (∑ x4 : Fin (n + 1), ∑ x2 : Fin (n + 1), ∑ x1 : Fin (n + 1),
        ∑ x3 : Fin (n + 1), ∑ x0 : Fin (n + 1),
          if valid5 n (e.symm (x4, x2, x1, x3, x0)) then 1 else 0) =
      ∑ x4 : Fin (n + 1), ∑ x2 : Fin (n + 1), ∑ x1 : Fin (n + 1),
        ∑ x3 : Fin (n + 1), ∑ x0 : Fin (n + 1),
          if (x0 : ℕ) + (x1 : ℕ) + (x2 : ℕ) + (x3 : ℕ) + (x4 : ℕ) ≤ n ∧
             (x1 : ℕ) + 2 * (x2 : ℕ) + (x3 : ℕ) + 3 * (x4 : ℕ) ≤ n then 1 else 0 := by
    apply Finset.sum_congr rfl; intro x4 _
    apply Finset.sum_congr rfl; intro x2 _
    apply Finset.sum_congr rfl; intro x1 _
    apply Finset.sum_congr rfl; intro x3 _
    apply Finset.sum_congr rfl; intro x0 _
    have hiff : valid5 n (e.symm (x4, x2, x1, x3, x0)) ↔
        (x0 : ℕ) + (x1 : ℕ) + (x2 : ℕ) + (x3 : ℕ) + (x4 : ℕ) ≤ n ∧
        (x1 : ℕ) + 2 * (x2 : ℕ) + (x3 : ℕ) + 3 * (x4 : ℕ) ≤ n := Iff.rfl
    by_cases h : (x0 : ℕ) + (x1 : ℕ) + (x2 : ℕ) + (x3 : ℕ) + (x4 : ℕ) ≤ n ∧
        (x1 : ℕ) + 2 * (x2 : ℕ) + (x3 : ℕ) + 3 * (x4 : ℕ) ≤ n
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun hv => h (hiff.mp hv)), if_neg h]
  rw [hconv]
  rw [Fin.sum_univ_eq_sum_range (fun x4 => ∑ x2 : Fin (n + 1), ∑ x1 : Fin (n + 1),
    ∑ x3 : Fin (n + 1), ∑ x0 : Fin (n + 1),
      if (x0 : ℕ) + (x1 : ℕ) + (x2 : ℕ) + (x3 : ℕ) + x4 ≤ n ∧
         (x1 : ℕ) + 2 * (x2 : ℕ) + (x3 : ℕ) + 3 * x4 ≤ n then 1 else 0)]
  apply Finset.sum_congr rfl; intro x4 _
  rw [Fin.sum_univ_eq_sum_range (fun x2 => ∑ x1 : Fin (n + 1),
    ∑ x3 : Fin (n + 1), ∑ x0 : Fin (n + 1),
      if (x0 : ℕ) + (x1 : ℕ) + x2 + (x3 : ℕ) + x4 ≤ n ∧
         (x1 : ℕ) + 2 * x2 + (x3 : ℕ) + 3 * x4 ≤ n then 1 else 0)]
  apply Finset.sum_congr rfl; intro x2 _
  rw [Fin.sum_univ_eq_sum_range (fun x1 => ∑ x3 : Fin (n + 1), ∑ x0 : Fin (n + 1),
      if (x0 : ℕ) + x1 + x2 + (x3 : ℕ) + x4 ≤ n ∧
         x1 + 2 * x2 + (x3 : ℕ) + 3 * x4 ≤ n then 1 else 0)]
  apply Finset.sum_congr rfl; intro x1 _
  rw [Fin.sum_univ_eq_sum_range (fun x3 => ∑ x0 : Fin (n + 1),
      if (x0 : ℕ) + x1 + x2 + x3 + x4 ≤ n ∧
         x1 + 2 * x2 + x3 + 3 * x4 ≤ n then 1 else 0)]
  apply Finset.sum_congr rfl; intro x3 _
  rw [Fin.sum_univ_eq_sum_range (fun x0 =>
      if x0 + x1 + x2 + x3 + x4 ≤ n ∧
         x1 + 2 * x2 + x3 + 3 * x4 ≤ n then 1 else 0)]

lemma sum_x0_x1_x3 (n x4 x2 : ℕ) (h24 : 2 * x2 + 3 * x4 ≤ n) :
    (∑ x1 ∈ range (n + 1), ∑ x3 ∈ range (n + 1), ∑ x0 ∈ range (n + 1),
      if x0 + x1 + x2 + x3 + x4 ≤ n ∧ x1 + 2 * x2 + x3 + 3 * x4 ≤ n then 1 else 0) =
    ∑ t ∈ range (n - 3 * x4 - 2 * x2 + 1), (t + 1) * (n + 1 - x2 - x4 - t) := by
  have hx0 : ∀ x1 x3 : ℕ,
      (∑ x0 ∈ range (n + 1),
        if x0 + x1 + x2 + x3 + x4 ≤ n ∧ x1 + 2 * x2 + x3 + 3 * x4 ≤ n then 1 else 0) =
      if x1 + x3 ≤ n - 3 * x4 - 2 * x2 then n + 1 - x2 - x4 - (x1 + x3) else 0 := by
    intro x1 x3
    by_cases h13 : x1 + x3 ≤ n - 3 * x4 - 2 * x2
    · rw [if_pos h13]
      have hfilt : (∑ x0 ∈ range (n + 1),
          if x0 + x1 + x2 + x3 + x4 ≤ n ∧ x1 + 2 * x2 + x3 + 3 * x4 ≤ n then 1 else 0) =
          ((range (n + 1)).filter (fun x0 => x0 < n + 1 - x2 - x4 - (x1 + x3))).card := by
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro x0 _
        have hiff : (x0 + x1 + x2 + x3 + x4 ≤ n ∧ x1 + 2 * x2 + x3 + 3 * x4 ≤ n) ↔
            x0 < n + 1 - x2 - x4 - (x1 + x3) := by omega
        simp only [hiff]
      rw [hfilt]
      have hsub : (range (n + 1)).filter (fun x0 => x0 < n + 1 - x2 - x4 - (x1 + x3)) =
          range (n + 1 - x2 - x4 - (x1 + x3)) := by
        ext x0; simp only [mem_filter, mem_range]; omega
      rw [hsub, card_range]
    · rw [if_neg h13]
      apply Finset.sum_eq_zero; intro x0 _; rw [if_neg]; omega
  simp_rw [hx0]
  set L := n - 3 * x4 - 2 * x2
  have h1 : ∀ x1 x3 : ℕ,
      (if x1 + x3 ≤ L then n + 1 - x2 - x4 - (x1 + x3) else 0) =
      ∑ t ∈ range (L + 1), if x1 + x3 = t then n + 1 - x2 - x4 - t else 0 := by
    intro x1 x3
    by_cases h : x1 + x3 ≤ L
    · rw [if_pos h, Finset.sum_eq_single (x1 + x3)]
      · simp
      · intro t _ ht; simp [Ne.symm ht]
      · intro ht; simp only [mem_range] at ht; omega
    · rw [if_neg h]
      symm
      apply Finset.sum_eq_zero
      intro t ht; simp only [mem_range] at ht; rw [if_neg]; omega
  simp_rw [h1]
  conv_lhs =>
    arg 2; ext x1
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [mem_range] at ht
  have h2 : ∀ x1 ∈ range (n + 1),
      (∑ x3 ∈ range (n + 1), if x1 + x3 = t then n + 1 - x2 - x4 - t else 0) =
      if x1 < t + 1 then n + 1 - x2 - x4 - t else 0 := by
    intro x1 _
    by_cases hx1 : x1 < t + 1
    · rw [if_pos hx1, Finset.sum_eq_single (t - x1)]
      · rw [if_pos (by omega)]
      · intro x3 _ hx3; rw [if_neg]; omega
      · intro hmem; simp only [mem_range] at hmem; omega
    · rw [if_neg hx1]
      apply Finset.sum_eq_zero; intro x3 _; rw [if_neg]; omega
  rw [Finset.sum_congr rfl h2, ← Finset.sum_filter]
  have hsub : (range (n + 1)).filter (fun x1 => x1 < t + 1) = range (t + 1) := by
    ext x1; simp only [mem_filter, mem_range]; omega
  rw [hsub, Finset.sum_const, Finset.card_range, smul_eq_mul]

lemma sum_t_poly (A L : ℕ) (h : L ≤ A) :
    6 * (∑ t ∈ range (L + 1), ((t + 1) * (A - t) : ℕ) : ℤ) =
    3 * ((L : ℤ) + 1) * ((L : ℤ) + 2) * (A : ℤ) - 2 * (L : ℤ) * ((L : ℤ) + 1) * ((L : ℤ) + 2) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, Nat.cast_add, mul_add, ih (by omega)]
    have hsub : ((A - (L + 1) : ℕ) : ℤ) = (A : ℤ) - ((L : ℤ) + 1) := by omega
    push_cast
    rw [hsub]
    ring

def gPoly (n x4 x2 : ℤ) : ℤ :=
  n ^ 3 - 3 * n ^ 2 * x2 - 3 * n ^ 2 * x4 + 6 * n ^ 2 - 6 * n * x2 * x4 - 15 * n * x2 -
    9 * n * x4 ^ 2 - 18 * n * x4 + 11 * n + 4 * x2 ^ 3 + 24 * x2 ^ 2 * x4 + 6 * x2 ^ 2 +
    45 * x2 * x4 ^ 2 + 9 * x2 * x4 - 16 * x2 + 27 * x4 ^ 3 - 21 * x4 + 6

lemma sum_gPoly (N X4 : ℤ) (m : ℕ) :
    2 * ∑ x2 ∈ range m, gPoly N X4 (x2 : ℤ) =
    2 * (m : ℤ) ^ 4 + 16 * (m : ℤ) ^ 3 * X4 - 3 * (m : ℤ) ^ 2 * N ^ 2 -
      6 * (m : ℤ) ^ 2 * N * X4 - 15 * (m : ℤ) ^ 2 * N + 45 * (m : ℤ) ^ 2 * X4 ^ 2 -
      15 * (m : ℤ) ^ 2 * X4 - 20 * (m : ℤ) ^ 2 + 2 * (m : ℤ) * N ^ 3 -
      6 * (m : ℤ) * N ^ 2 * X4 + 15 * (m : ℤ) * N ^ 2 - 18 * (m : ℤ) * N * X4 ^ 2 -
      30 * (m : ℤ) * N * X4 + 37 * (m : ℤ) * N + 54 * (m : ℤ) * X4 ^ 3 -
      45 * (m : ℤ) * X4 ^ 2 - 43 * (m : ℤ) * X4 + 30 * (m : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    unfold gPoly
    push_cast; ring

def inner2 (n x4 : ℕ) : ℕ :=
  ∑ x2 ∈ range ((n - 3 * x4) / 2 + 1),
    ∑ t ∈ range (n - 3 * x4 - 2 * x2 + 1), (t + 1) * (n + 1 - x2 - x4 - t)

lemma a_eq_sum_x4 (n : ℕ) : a n = ∑ x4 ∈ range (n / 3 + 1), inner2 n x4 := by
  rw [a_eq_sum5]
  have hx4 : ∀ x4 ∈ range (n + 1),
      (∑ x2 ∈ range (n + 1), ∑ x1 ∈ range (n + 1), ∑ x3 ∈ range (n + 1), ∑ x0 ∈ range (n + 1),
        if x0 + x1 + x2 + x3 + x4 ≤ n ∧ x1 + 2 * x2 + x3 + 3 * x4 ≤ n then 1 else 0) =
      if x4 < n / 3 + 1 then inner2 n x4 else 0 := by
    intro x4 _
    by_cases h4 : x4 < n / 3 + 1
    · rw [if_pos h4]
      unfold inner2
      have hx2 : ∀ x2 ∈ range (n + 1),
          (∑ x1 ∈ range (n + 1), ∑ x3 ∈ range (n + 1), ∑ x0 ∈ range (n + 1),
            if x0 + x1 + x2 + x3 + x4 ≤ n ∧ x1 + 2 * x2 + x3 + 3 * x4 ≤ n then 1 else 0) =
          if x2 < (n - 3 * x4) / 2 + 1 then
            ∑ t ∈ range (n - 3 * x4 - 2 * x2 + 1), (t + 1) * (n + 1 - x2 - x4 - t)
          else 0 := by
        intro x2 _
        by_cases h2 : x2 < (n - 3 * x4) / 2 + 1
        · rw [if_pos h2]
          exact sum_x0_x1_x3 n x4 x2 (by omega)
        · rw [if_neg h2]
          apply Finset.sum_eq_zero; intro x1 _
          apply Finset.sum_eq_zero; intro x3 _
          apply Finset.sum_eq_zero; intro x0 _
          rw [if_neg]; omega
      rw [Finset.sum_congr rfl hx2, ← Finset.sum_filter]
      congr 1
      ext x2; simp only [mem_filter, mem_range]; omega
    · rw [if_neg h4]
      apply Finset.sum_eq_zero; intro x2 _
      apply Finset.sum_eq_zero; intro x1 _
      apply Finset.sum_eq_zero; intro x3 _
      apply Finset.sum_eq_zero; intro x0 _
      rw [if_neg]; omega
  rw [Finset.sum_congr rfl hx4, ← Finset.sum_filter]
  congr 1
  ext x4; simp only [mem_filter, mem_range]; omega

lemma inner2_eq (n x4 : ℕ) (h : 3 * x4 ≤ n) :
    12 * (inner2 n x4 : ℤ) =
    2 * ∑ x2 ∈ range ((n - 3 * x4) / 2 + 1), gPoly (n : ℤ) (x4 : ℤ) (x2 : ℤ) := by
  unfold inner2
  rw [Nat.cast_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x2 hx2
  simp only [mem_range] at hx2
  rw [Nat.cast_sum]
  have ht := sum_t_poly (n + 1 - x2 - x4) (n - 3 * x4 - 2 * x2) (by omega)
  have h12 : 12 * (∑ t ∈ range (n - 3 * x4 - 2 * x2 + 1), ((t + 1) * (n + 1 - x2 - x4 - t) : ℕ) : ℤ) =
      2 * (6 * (∑ t ∈ range (n - 3 * x4 - 2 * x2 + 1), ((t + 1) * (n + 1 - x2 - x4 - t) : ℕ) : ℤ)) := by
    ring
  rw [h12, ht]
  have hA : ((n + 1 - x2 - x4 : ℕ) : ℤ) = (n : ℤ) + 1 - (x2 : ℤ) - (x4 : ℤ) := by omega
  have hL : ((n - 3 * x4 - 2 * x2 : ℕ) : ℤ) = (n : ℤ) - 3 * (x4 : ℤ) - 2 * (x2 : ℤ) := by omega
  rw [hA, hL]
  unfold gPoly
  ring

def fe12 (u p k : ℤ) : ℤ :=
  -378 * k ^ 4 + 108 * k ^ 3 * p + 216 * k ^ 3 * u + 270 * k ^ 3 + 9 * k ^ 2 * p ^ 2 +
    36 * k ^ 2 * p * u + 45 * k ^ 2 * p + 36 * k ^ 2 * u ^ 2 + 90 * k ^ 2 * u + 78 * k ^ 2 -
    6 * k * p ^ 3 - 30 * k * p ^ 2 * u - 39 * k * p ^ 2 - 60 * k * p * u ^ 2 -
    150 * k * p * u - 93 * k * p - 40 * k * u ^ 3 - 150 * k * u ^ 2 - 188 * k * u -
    78 * k + 2 * p ^ 3 * u + 2 * p ^ 3 + 9 * p ^ 2 * u ^ 2 + 21 * p ^ 2 * u + 12 * p ^ 2 +
    12 * p * u ^ 3 + 45 * p * u ^ 2 + 55 * p * u + 22 * p + 6 * u ^ 4 + 30 * u ^ 3 +
    54 * u ^ 2 + 42 * u + 12

def fo12 (u p k : ℤ) : ℤ :=
  -378 * k ^ 4 + 108 * k ^ 3 * p + 216 * k ^ 3 * u - 486 * k ^ 3 + 9 * k ^ 2 * p ^ 2 +
    36 * k ^ 2 * p * u + 207 * k ^ 2 * p + 36 * k ^ 2 * u ^ 2 + 414 * k ^ 2 * u - 84 * k ^ 2 -
    4 * k * p ^ 3 - 30 * k * p ^ 2 * u - 33 * k * p ^ 2 - 60 * k * p * u ^ 2 -
    114 * k * p * u + 37 * k * p - 40 * k * u ^ 3 - 114 * k * u ^ 2 + 64 * k * u +
    12 * k + p ^ 4 + 4 * p ^ 3 * u + 9 * p ^ 2 * u ^ 2 + 3 * p ^ 2 * u - 7 * p ^ 2 +
    12 * p * u ^ 3 + 15 * p * u ^ 2 - 7 * p * u + 6 * p + 6 * u ^ 4 + 10 * u ^ 3 -
    12 * u ^ 2 - 4 * u

lemma sum_fe12 (u p : ℤ) (m : ℕ) :
    10 * ∑ k ∈ range m, fe12 u p (k : ℤ) =
    -756 * (m : ℤ) ^ 5 + 270 * (m : ℤ) ^ 4 * p + 540 * (m : ℤ) ^ 4 * u + 2565 * (m : ℤ) ^ 4 +
      30 * (m : ℤ) ^ 3 * p ^ 2 + 120 * (m : ℤ) ^ 3 * p * u - 390 * (m : ℤ) ^ 3 * p +
      120 * (m : ℤ) ^ 3 * u ^ 2 - 780 * (m : ℤ) ^ 3 * u - 2350 * (m : ℤ) ^ 3 -
      30 * (m : ℤ) ^ 2 * p ^ 3 - 150 * (m : ℤ) ^ 2 * p ^ 2 * u - 240 * (m : ℤ) ^ 2 * p ^ 2 -
      300 * (m : ℤ) ^ 2 * p * u ^ 2 - 930 * (m : ℤ) ^ 2 * p * u - 420 * (m : ℤ) ^ 2 * p -
      200 * (m : ℤ) ^ 2 * u ^ 3 - 930 * (m : ℤ) ^ 2 * u ^ 2 - 850 * (m : ℤ) ^ 2 * u -
      105 * (m : ℤ) ^ 2 + 20 * (m : ℤ) * p ^ 3 * u + 50 * (m : ℤ) * p ^ 3 +
      90 * (m : ℤ) * p ^ 2 * u ^ 2 + 360 * (m : ℤ) * p ^ 2 * u + 330 * (m : ℤ) * p ^ 2 +
      120 * (m : ℤ) * p * u ^ 3 + 750 * (m : ℤ) * p * u ^ 2 + 1360 * (m : ℤ) * p * u +
      760 * (m : ℤ) * p + 60 * (m : ℤ) * u ^ 4 + 500 * (m : ℤ) * u ^ 3 +
      1350 * (m : ℤ) * u ^ 2 + 1510 * (m : ℤ) * u + 766 * (m : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    unfold fe12
    push_cast; ring

lemma sum_fo12 (u p : ℤ) (m : ℕ) :
    10 * ∑ k ∈ range m, fo12 u p (k : ℤ) =
    -756 * (m : ℤ) ^ 5 + 270 * (m : ℤ) ^ 4 * p + 540 * (m : ℤ) ^ 4 * u + 675 * (m : ℤ) ^ 4 +
      30 * (m : ℤ) ^ 3 * p ^ 2 + 120 * (m : ℤ) ^ 3 * p * u + 150 * (m : ℤ) ^ 3 * p +
      120 * (m : ℤ) ^ 3 * u ^ 2 + 300 * (m : ℤ) ^ 3 * u + 890 * (m : ℤ) ^ 3 -
      20 * (m : ℤ) ^ 2 * p ^ 3 - 150 * (m : ℤ) ^ 2 * p ^ 2 * u - 210 * (m : ℤ) ^ 2 * p ^ 2 -
      300 * (m : ℤ) ^ 2 * p * u ^ 2 - 750 * (m : ℤ) ^ 2 * p * u - 580 * (m : ℤ) ^ 2 * p -
      200 * (m : ℤ) ^ 2 * u ^ 3 - 750 * (m : ℤ) ^ 2 * u ^ 2 - 1210 * (m : ℤ) ^ 2 * u -
      735 * (m : ℤ) ^ 2 + 10 * (m : ℤ) * p ^ 4 + 40 * (m : ℤ) * p ^ 3 * u +
      20 * (m : ℤ) * p ^ 3 + 90 * (m : ℤ) * p ^ 2 * u ^ 2 + 180 * (m : ℤ) * p ^ 2 * u +
      110 * (m : ℤ) * p ^ 2 + 120 * (m : ℤ) * p * u ^ 3 + 450 * (m : ℤ) * p * u ^ 2 +
      560 * (m : ℤ) * p * u + 220 * (m : ℤ) * p + 60 * (m : ℤ) * u ^ 4 +
      300 * (m : ℤ) * u ^ 3 + 510 * (m : ℤ) * u ^ 2 + 330 * (m : ℤ) * u - 74 * (m : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    unfold fo12
    push_cast; ring

lemma inner2_even (u p k : ℕ) (hp : p ≤ 1) (hk : 6 * k ≤ 2 * u + p) :
    12 * (inner2 (2 * u + p) (2 * k) : ℤ) = fe12 (u : ℤ) (p : ℤ) (k : ℤ) := by
  rw [inner2_eq (2 * u + p) (2 * k) (by omega), sum_gPoly]
  have hm : ((2 * u + p - 3 * (2 * k)) / 2 + 1 : ℕ) = u + 1 - 3 * k := by omega
  rw [hm]
  have hmc : ((u + 1 - 3 * k : ℕ) : ℤ) = (u : ℤ) + 1 - 3 * (k : ℤ) := by omega
  push_cast
  rw [hmc]
  unfold fe12
  ring

lemma inner2_odd (u p k : ℕ) (hp : p ≤ 1) (hk : 6 * k + 3 ≤ 2 * u + p) :
    12 * (inner2 (2 * u + p) (2 * k + 1) : ℤ) = fo12 (u : ℤ) (p : ℤ) (k : ℤ) := by
  rw [inner2_eq (2 * u + p) (2 * k + 1) (by omega), sum_gPoly]
  have hm : ((2 * u + p - 3 * (2 * k + 1)) / 2 + 1 : ℕ) = u + p - 3 * k - 1 := by omega
  rw [hm]
  have hmc : ((u + p - 3 * k - 1 : ℕ) : ℤ) = (u : ℤ) + (p : ℤ) - 3 * (k : ℤ) - 1 := by omega
  push_cast
  rw [hmc]
  unfold fo12
  ring

lemma sum_split_even (f : ℕ → ℤ) (m : ℕ) :
    ∑ s ∈ range (2 * m + 1), f s =
    (∑ k ∈ range (m + 1), f (2 * k)) + (∑ k ∈ range m, f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ (fun k => f (2 * k)) (m + 1),
      Finset.sum_range_succ (fun k => f (2 * k + 1)) m]
    have h1 : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
    rw [h1]
    ring

lemma sum_split_odd (f : ℕ → ℤ) (m : ℕ) :
    ∑ s ∈ range (2 * m + 2), f s =
    (∑ k ∈ range (m + 1), f (2 * k)) + (∑ k ∈ range (m + 1), f (2 * k + 1)) := by
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, Finset.sum_range_succ, sum_split_even,
    Finset.sum_range_succ (fun k => f (2 * k + 1)) m]
  ring

def polyMod6 (q : ℤ) (r : ℕ) : ℤ :=
  match r with
  | 0 => 702 * q ^ 5 + 2070 * q ^ 4 + 2275 * q ^ 3 + 1170 * q ^ 2 + 293 * q + 30
  | 1 => 702 * q ^ 5 + 2655 * q ^ 4 + 3850 * q ^ 3 + 2685 * q ^ 2 + 908 * q + 120
  | 2 => 702 * q ^ 5 + 3240 * q ^ 4 + 5815 * q ^ 3 + 5085 * q ^ 2 + 2168 * q + 360
  | 3 => 702 * q ^ 5 + 3825 * q ^ 4 + 8170 * q ^ 3 + 8565 * q ^ 2 + 4418 * q + 900
  | 4 => 702 * q ^ 5 + 4410 * q ^ 4 + 10915 * q ^ 3 + 13320 * q ^ 2 + 8033 * q + 1920
  | _ => 702 * q ^ 5 + 4995 * q ^ 4 + 14050 * q ^ 3 + 19545 * q ^ 2 + 13448 * q + 3660

lemma a_mod6 (q r : ℕ) (hr : r < 6) :
    30 * (a (6 * q + r) : ℤ) = polyMod6 (q : ℤ) r := by
  rw [a_eq_sum_x4]
  suffices h120 :
      120 * (∑ x4 ∈ range ((6 * q + r) / 3 + 1), (inner2 (6 * q + r) x4 : ℤ)) =
      4 * polyMod6 (q : ℤ) r by
    rw [Nat.cast_sum]
    linarith
  interval_cases r
  · rw [show (6 * q + 0) / 3 + 1 = 2 * q + 1 by omega, sum_split_even]
    rw [show 6 * q + 0 = 2 * (3 * q) + 0 by omega]
    rw [show (120 : ℤ) * ((∑ k ∈ range (q + 1), (inner2 (2 * (3 * q) + 0) (2 * k) : ℤ)) +
          ∑ k ∈ range q, (inner2 (2 * (3 * q) + 0) (2 * k + 1) : ℤ)) =
        10 * (∑ k ∈ range (q + 1), 12 * (inner2 (2 * (3 * q) + 0) (2 * k) : ℤ)) +
        10 * (∑ k ∈ range q, 12 * (inner2 (2 * (3 * q) + 0) (2 * k + 1) : ℤ)) by
          simp only [← Finset.mul_sum]; ring]
    rw [Finset.sum_congr rfl (fun k hk => inner2_even (3 * q) 0 k (by omega) (by simp only [mem_range] at hk; omega))]
    rw [Finset.sum_congr rfl (fun k hk => inner2_odd (3 * q) 0 k (by omega) (by simp only [mem_range] at hk; omega))]
    rw [sum_fe12, sum_fo12]; unfold polyMod6; push_cast; ring
  · rw [show (6 * q + 1) / 3 + 1 = 2 * q + 1 by omega, sum_split_even]
    rw [show 6 * q + 1 = 2 * (3 * q) + 1 by omega]
    rw [show (120 : ℤ) * ((∑ k ∈ range (q + 1), (inner2 (2 * (3 * q) + 1) (2 * k) : ℤ)) +
          ∑ k ∈ range q, (inner2 (2 * (3 * q) + 1) (2 * k + 1) : ℤ)) =
        10 * (∑ k ∈ range (q + 1), 12 * (inner2 (2 * (3 * q) + 1) (2 * k) : ℤ)) +
        10 * (∑ k ∈ range q, 12 * (inner2 (2 * (3 * q) + 1) (2 * k + 1) : ℤ)) by
          simp only [← Finset.mul_sum]; ring]
    rw [Finset.sum_congr rfl (fun k hk => inner2_even (3 * q) 1 k (by omega) (by simp only [mem_range] at hk; omega))]
    rw [Finset.sum_congr rfl (fun k hk => inner2_odd (3 * q) 1 k (by omega) (by simp only [mem_range] at hk; omega))]
    rw [sum_fe12, sum_fo12]; unfold polyMod6; push_cast; ring
  · rw [show (6 * q + 2) / 3 + 1 = 2 * q + 1 by omega, sum_split_even]
    rw [show 6 * q + 2 = 2 * (3 * q + 1) + 0 by omega]
    rw [show (120 : ℤ) * ((∑ k ∈ range (q + 1), (inner2 (2 * (3 * q + 1) + 0) (2 * k) : ℤ)) +
          ∑ k ∈ range q, (inner2 (2 * (3 * q + 1) + 0) (2 * k + 1) : ℤ)) =
        10 * (∑ k ∈ range (q + 1), 12 * (inner2 (2 * (3 * q + 1) + 0) (2 * k) : ℤ)) +
        10 * (∑ k ∈ range q, 12 * (inner2 (2 * (3 * q + 1) + 0) (2 * k + 1) : ℤ)) by
          simp only [← Finset.mul_sum]; ring]
    rw [Finset.sum_congr rfl (fun k hk => inner2_even (3 * q + 1) 0 k (by omega) (by simp only [mem_range] at hk; omega))]
    rw [Finset.sum_congr rfl (fun k hk => inner2_odd (3 * q + 1) 0 k (by omega) (by simp only [mem_range] at hk; omega))]
    rw [sum_fe12, sum_fo12]; unfold polyMod6; push_cast; ring
  · rw [show (6 * q + 3) / 3 + 1 = 2 * q + 2 by omega, sum_split_odd]
    rw [show 6 * q + 3 = 2 * (3 * q + 1) + 1 by omega]
    rw [show (120 : ℤ) * ((∑ k ∈ range (q + 1), (inner2 (2 * (3 * q + 1) + 1) (2 * k) : ℤ)) +
          ∑ k ∈ range (q + 1), (inner2 (2 * (3 * q + 1) + 1) (2 * k + 1) : ℤ)) =
        10 * (∑ k ∈ range (q + 1), 12 * (inner2 (2 * (3 * q + 1) + 1) (2 * k) : ℤ)) +
        10 * (∑ k ∈ range (q + 1), 12 * (inner2 (2 * (3 * q + 1) + 1) (2 * k + 1) : ℤ)) by
          simp only [← Finset.mul_sum]; ring]
    rw [Finset.sum_congr rfl (fun k hk => inner2_even (3 * q + 1) 1 k (by omega) (by simp only [mem_range] at hk; omega))]
    rw [Finset.sum_congr rfl (fun k hk => inner2_odd (3 * q + 1) 1 k (by omega) (by simp only [mem_range] at hk; omega))]
    rw [sum_fe12, sum_fo12]; unfold polyMod6; push_cast; ring
  · rw [show (6 * q + 4) / 3 + 1 = 2 * q + 2 by omega, sum_split_odd]
    rw [show 6 * q + 4 = 2 * (3 * q + 2) + 0 by omega]
    rw [show (120 : ℤ) * ((∑ k ∈ range (q + 1), (inner2 (2 * (3 * q + 2) + 0) (2 * k) : ℤ)) +
          ∑ k ∈ range (q + 1), (inner2 (2 * (3 * q + 2) + 0) (2 * k + 1) : ℤ)) =
        10 * (∑ k ∈ range (q + 1), 12 * (inner2 (2 * (3 * q + 2) + 0) (2 * k) : ℤ)) +
        10 * (∑ k ∈ range (q + 1), 12 * (inner2 (2 * (3 * q + 2) + 0) (2 * k + 1) : ℤ)) by
          simp only [← Finset.mul_sum]; ring]
    rw [Finset.sum_congr rfl (fun k hk => inner2_even (3 * q + 2) 0 k (by omega) (by simp only [mem_range] at hk; omega))]
    rw [Finset.sum_congr rfl (fun k hk => inner2_odd (3 * q + 2) 0 k (by omega) (by simp only [mem_range] at hk; omega))]
    rw [sum_fe12, sum_fo12]; unfold polyMod6; push_cast; ring
  · rw [show (6 * q + 5) / 3 + 1 = 2 * q + 2 by omega, sum_split_odd]
    rw [show 6 * q + 5 = 2 * (3 * q + 2) + 1 by omega]
    rw [show (120 : ℤ) * ((∑ k ∈ range (q + 1), (inner2 (2 * (3 * q + 2) + 1) (2 * k) : ℤ)) +
          ∑ k ∈ range (q + 1), (inner2 (2 * (3 * q + 2) + 1) (2 * k + 1) : ℤ)) =
        10 * (∑ k ∈ range (q + 1), 12 * (inner2 (2 * (3 * q + 2) + 1) (2 * k) : ℤ)) +
        10 * (∑ k ∈ range (q + 1), 12 * (inner2 (2 * (3 * q + 2) + 1) (2 * k + 1) : ℤ)) by
          simp only [← Finset.mul_sum]; ring]
    rw [Finset.sum_congr rfl (fun k hk => inner2_even (3 * q + 2) 1 k (by omega) (by simp only [mem_range] at hk; omega))]
    rw [Finset.sum_congr rfl (fun k hk => inner2_odd (3 * q + 2) 1 k (by omega) (by simp only [mem_range] at hk; omega))]
    rw [sum_fe12, sum_fo12]; unfold polyMod6; push_cast; ring

lemma a_small :
    a 0 = 1 ∧ a 1 = 4 ∧ a 2 = 12 ∧ a 3 = 30 ∧ a 4 = 64 ∧ a 5 = 122 ∧ a 6 = 218 ∧
    a 7 = 364 ∧ a 8 = 579 ∧ a 9 = 886 ∧ a 10 = 1310 ∧ a 11 = 1880 := by
  have h0 := a_mod6 0 0 (by omega)
  have h1 := a_mod6 0 1 (by omega)
  have h2 := a_mod6 0 2 (by omega)
  have h3 := a_mod6 0 3 (by omega)
  have h4 := a_mod6 0 4 (by omega)
  have h5 := a_mod6 0 5 (by omega)
  have h6 := a_mod6 1 0 (by omega)
  have h7 := a_mod6 1 1 (by omega)
  have h8 := a_mod6 1 2 (by omega)
  have h9 := a_mod6 1 3 (by omega)
  have h10 := a_mod6 1 4 (by omega)
  have h11 := a_mod6 1 5 (by omega)
  norm_num [polyMod6] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega⟩

lemma hrec : ∀ n : ℕ, 11 < n →
    (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3) - 3 * a (n - 4) +
      6 * a (n - 6) - 3 * a (n - 8) - 2 * a (n - 9) + a (n - 10) +
      2 * a (n - 11) - a (n - 12) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  have hdiv : m = 6 * (m / 6) + m % 6 := (Nat.div_add_mod m 6).symm
  set q := m / 6
  set r := m % 6
  have hr : r < 6 := Nat.mod_lt m (by omega)
  rw [hdiv]
  suffices h30 :
      30 * (a (6 * q + r + 12) : ℤ) =
      2 * (30 * (a (6 * q + r + 12 - 1) : ℤ)) + (30 * (a (6 * q + r + 12 - 2) : ℤ)) -
      2 * (30 * (a (6 * q + r + 12 - 3) : ℤ)) - 3 * (30 * (a (6 * q + r + 12 - 4) : ℤ)) +
      6 * (30 * (a (6 * q + r + 12 - 6) : ℤ)) - 3 * (30 * (a (6 * q + r + 12 - 8) : ℤ)) -
      2 * (30 * (a (6 * q + r + 12 - 9) : ℤ)) + (30 * (a (6 * q + r + 12 - 10) : ℤ)) +
      2 * (30 * (a (6 * q + r + 12 - 11) : ℤ)) - (30 * (a (6 * q + r + 12 - 12) : ℤ)) by
    linarith
  have h00 := a_mod6 q 0 (by omega)
  have h01 := a_mod6 q 1 (by omega)
  have h02 := a_mod6 q 2 (by omega)
  have h03 := a_mod6 q 3 (by omega)
  have h04 := a_mod6 q 4 (by omega)
  have h05 := a_mod6 q 5 (by omega)
  have h10 := a_mod6 (q + 1) 0 (by omega)
  have h11 := a_mod6 (q + 1) 1 (by omega)
  have h12 := a_mod6 (q + 1) 2 (by omega)
  have h13 := a_mod6 (q + 1) 3 (by omega)
  have h14 := a_mod6 (q + 1) 4 (by omega)
  have h15 := a_mod6 (q + 1) 5 (by omega)
  have h20 := a_mod6 (q + 2) 0 (by omega)
  have h21 := a_mod6 (q + 2) 1 (by omega)
  have h22 := a_mod6 (q + 2) 2 (by omega)
  have h23 := a_mod6 (q + 2) 3 (by omega)
  have h24 := a_mod6 (q + 2) 4 (by omega)
  have h25 := a_mod6 (q + 2) 5 (by omega)
  interval_cases r
  · rw [show 6 * q + 0 + 12 = 6 * (q + 2) + 0 by omega,
        show 6 * (q + 2) + 0 - 1 = 6 * (q + 1) + 5 by omega,
        show 6 * (q + 2) + 0 - 2 = 6 * (q + 1) + 4 by omega,
        show 6 * (q + 2) + 0 - 3 = 6 * (q + 1) + 3 by omega,
        show 6 * (q + 2) + 0 - 4 = 6 * (q + 1) + 2 by omega,
        show 6 * (q + 2) + 0 - 6 = 6 * (q + 1) + 0 by omega,
        show 6 * (q + 2) + 0 - 8 = 6 * q + 4 by omega,
        show 6 * (q + 2) + 0 - 9 = 6 * q + 3 by omega,
        show 6 * (q + 2) + 0 - 10 = 6 * q + 2 by omega,
        show 6 * (q + 2) + 0 - 11 = 6 * q + 1 by omega,
        show 6 * (q + 2) + 0 - 12 = 6 * q + 0 by omega]
    rw [h20, h15, h14, h13, h12, h10, h04, h03, h02, h01, h00]
    simp only [polyMod6]; push_cast; ring
  · rw [show 6 * q + 1 + 12 = 6 * (q + 2) + 1 by omega,
        show 6 * (q + 2) + 1 - 1 = 6 * (q + 2) + 0 by omega,
        show 6 * (q + 2) + 1 - 2 = 6 * (q + 1) + 5 by omega,
        show 6 * (q + 2) + 1 - 3 = 6 * (q + 1) + 4 by omega,
        show 6 * (q + 2) + 1 - 4 = 6 * (q + 1) + 3 by omega,
        show 6 * (q + 2) + 1 - 6 = 6 * (q + 1) + 1 by omega,
        show 6 * (q + 2) + 1 - 8 = 6 * q + 5 by omega,
        show 6 * (q + 2) + 1 - 9 = 6 * q + 4 by omega,
        show 6 * (q + 2) + 1 - 10 = 6 * q + 3 by omega,
        show 6 * (q + 2) + 1 - 11 = 6 * q + 2 by omega,
        show 6 * (q + 2) + 1 - 12 = 6 * q + 1 by omega]
    rw [h21, h20, h15, h14, h13, h11, h05, h04, h03, h02, h01]
    simp only [polyMod6]; push_cast; ring
  · rw [show 6 * q + 2 + 12 = 6 * (q + 2) + 2 by omega,
        show 6 * (q + 2) + 2 - 1 = 6 * (q + 2) + 1 by omega,
        show 6 * (q + 2) + 2 - 2 = 6 * (q + 2) + 0 by omega,
        show 6 * (q + 2) + 2 - 3 = 6 * (q + 1) + 5 by omega,
        show 6 * (q + 2) + 2 - 4 = 6 * (q + 1) + 4 by omega,
        show 6 * (q + 2) + 2 - 6 = 6 * (q + 1) + 2 by omega,
        show 6 * (q + 2) + 2 - 8 = 6 * (q + 1) + 0 by omega,
        show 6 * (q + 2) + 2 - 9 = 6 * q + 5 by omega,
        show 6 * (q + 2) + 2 - 10 = 6 * q + 4 by omega,
        show 6 * (q + 2) + 2 - 11 = 6 * q + 3 by omega,
        show 6 * (q + 2) + 2 - 12 = 6 * q + 2 by omega]
    rw [h22, h21, h20, h15, h14, h12, h10, h05, h04, h03, h02]
    simp only [polyMod6]; push_cast; ring
  · rw [show 6 * q + 3 + 12 = 6 * (q + 2) + 3 by omega,
        show 6 * (q + 2) + 3 - 1 = 6 * (q + 2) + 2 by omega,
        show 6 * (q + 2) + 3 - 2 = 6 * (q + 2) + 1 by omega,
        show 6 * (q + 2) + 3 - 3 = 6 * (q + 2) + 0 by omega,
        show 6 * (q + 2) + 3 - 4 = 6 * (q + 1) + 5 by omega,
        show 6 * (q + 2) + 3 - 6 = 6 * (q + 1) + 3 by omega,
        show 6 * (q + 2) + 3 - 8 = 6 * (q + 1) + 1 by omega,
        show 6 * (q + 2) + 3 - 9 = 6 * (q + 1) + 0 by omega,
        show 6 * (q + 2) + 3 - 10 = 6 * q + 5 by omega,
        show 6 * (q + 2) + 3 - 11 = 6 * q + 4 by omega,
        show 6 * (q + 2) + 3 - 12 = 6 * q + 3 by omega]
    rw [h23, h22, h21, h20, h15, h13, h11, h10, h05, h04, h03]
    simp only [polyMod6]; push_cast; ring
  · rw [show 6 * q + 4 + 12 = 6 * (q + 2) + 4 by omega,
        show 6 * (q + 2) + 4 - 1 = 6 * (q + 2) + 3 by omega,
        show 6 * (q + 2) + 4 - 2 = 6 * (q + 2) + 2 by omega,
        show 6 * (q + 2) + 4 - 3 = 6 * (q + 2) + 1 by omega,
        show 6 * (q + 2) + 4 - 4 = 6 * (q + 2) + 0 by omega,
        show 6 * (q + 2) + 4 - 6 = 6 * (q + 1) + 4 by omega,
        show 6 * (q + 2) + 4 - 8 = 6 * (q + 1) + 2 by omega,
        show 6 * (q + 2) + 4 - 9 = 6 * (q + 1) + 1 by omega,
        show 6 * (q + 2) + 4 - 10 = 6 * (q + 1) + 0 by omega,
        show 6 * (q + 2) + 4 - 11 = 6 * q + 5 by omega,
        show 6 * (q + 2) + 4 - 12 = 6 * q + 4 by omega]
    rw [h24, h23, h22, h21, h20, h14, h12, h11, h10, h05, h04]
    simp only [polyMod6]; push_cast; ring
  · rw [show 6 * q + 5 + 12 = 6 * (q + 2) + 5 by omega,
        show 6 * (q + 2) + 5 - 1 = 6 * (q + 2) + 4 by omega,
        show 6 * (q + 2) + 5 - 2 = 6 * (q + 2) + 3 by omega,
        show 6 * (q + 2) + 5 - 3 = 6 * (q + 2) + 2 by omega,
        show 6 * (q + 2) + 5 - 4 = 6 * (q + 2) + 1 by omega,
        show 6 * (q + 2) + 5 - 6 = 6 * (q + 1) + 5 by omega,
        show 6 * (q + 2) + 5 - 8 = 6 * (q + 1) + 3 by omega,
        show 6 * (q + 2) + 5 - 9 = 6 * (q + 1) + 2 by omega,
        show 6 * (q + 2) + 5 - 10 = 6 * (q + 1) + 1 by omega,
        show 6 * (q + 2) + 5 - 11 = 6 * (q + 1) + 0 by omega,
        show 6 * (q + 2) + 5 - 12 = 6 * q + 5 by omega]
    rw [h25, h24, h23, h22, h21, h15, h13, h12, h11, h10, h05]
    simp only [polyMod6]; push_cast; ring

lemma hgf :
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - X) ^ 6 * (1 + X) ^ 2 * (1 + X + X ^ 2) ^ 2) =
    1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11⟩ := a_small
  set S := PowerSeries.mk (fun n => (a n : ℚ)) with hS
  have hl : S * ((1 - X) ^ 6 * (1 + X) ^ 2 * (1 + X + X ^ 2) ^ 2) =
      S + C (-2 : ℚ) * (S * X ^ 1) + C (-1 : ℚ) * (S * X ^ 2) +
      C (2 : ℚ) * (S * X ^ 3) + C (3 : ℚ) * (S * X ^ 4) +
      C (-6 : ℚ) * (S * X ^ 6) + C (3 : ℚ) * (S * X ^ 8) +
      C (2 : ℚ) * (S * X ^ 9) + C (-1 : ℚ) * (S * X ^ 10) +
      C (-2 : ℚ) * (S * X ^ 11) + C (1 : ℚ) * (S * X ^ 12) := by
    simp only [map_neg, map_ofNat, map_one]; ring
  have hr : (1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 : PowerSeries ℚ) =
      C (1 : ℚ) + C (2 : ℚ) * X ^ 1 + C (3 : ℚ) * X ^ 2 +
      C (4 : ℚ) * X ^ 3 + C (3 : ℚ) * X ^ 4 := by
    simp only [map_ofNat, map_one]; ring
  rw [hl, hr]
  ext n
  simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hS, coeff_mk]
  rcases Nat.lt_or_ge n 12 with hn | hn
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] <;> norm_num
  · have hq : (a n : ℚ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3) - 3 * a (n - 4) +
        6 * a (n - 6) - 3 * a (n - 8) - 2 * a (n - 9) + a (n - 10) +
        2 * a (n - 11) - a (n - 12) := by
      exact_mod_cast hrec n (by omega)
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have c4 : 4 ≤ n := by omega
    have c6 : 6 ≤ n := by omega
    have c8 : 8 ≤ n := by omega
    have c9 : 9 ≤ n := by omega
    have c10 : 10 ≤ n := by omega
    have c11 : 11 ≤ n := by omega
    have c12 : 12 ≤ n := by omega
    have d0 : n ≠ 0 := by omega
    have e1 : n - 1 ≠ 0 := by omega
    have e2 : n - 2 ≠ 0 := by omega
    have e3 : n - 3 ≠ 0 := by omega
    have e4 : n - 4 ≠ 0 := by omega
    simp only [c1, c2, c3, c4, c6, c8, c9, c10, c11, c12,
      d0, e1, e2, e3, e4, if_true, if_false]
    linear_combination hq

theorem main_proof :
    (PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - X) ^ 6 * (1 + X) ^ 2 * (1 + X + X ^ 2) ^ 2) =
      1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4) ∧
    (∀ n : ℕ, 11 < n →
      (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3) - 3 * a (n - 4) +
        6 * a (n - 6) - 3 * a (n - 8) - 2 * a (n - 9) + a (n - 10) +
        2 * a (n - 11) - a (n - 12)) :=
  ⟨hgf, hrec⟩

end OMA.P166213

theorem OMA.solution : type_of% @OMA.S_oeis_a166213.main := OMA.P166213.main_proof
