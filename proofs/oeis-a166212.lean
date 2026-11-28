import OMAStatements.S_oeis_a166212

-- Credit: @Dariusthedoggie
-- Proof: reduce by 120-degree rotational symmetry to 4 orbit variables, evaluate the nested lattice sum explicitly mod 6, and verify the recurrence and g.f.

namespace OMA.P166212

open OMA.S_oeis_a166212 PowerSeries Finset

/-- Orbit index of each cell under 120-degree rotation. -/
def orb (p : Cell) : Fin 4 :=
  if p.1.1 = 3 ∨ p.1.2.1 = 3 ∨ p.1.2.2 = 3 then 0
  else if (p.1.1 = 2 ∧ p.1.2.1 = 1) ∨ (p.1.2.1 = 2 ∧ p.1.2.2 = 1) ∨ (p.1.2.2 = 2 ∧ p.1.1 = 1) then 1
  else if (p.1.1 = 1 ∧ p.1.2.1 = 2) ∨ (p.1.2.1 = 1 ∧ p.1.2.2 = 2) ∨ (p.1.2.2 = 1 ∧ p.1.1 = 2) then 2
  else 3

/-- Canonical representative of each rotation orbit. -/
def rep : Fin 4 → Cell
  | 0 => ⟨(3, 0, 0), by decide⟩
  | 1 => ⟨(2, 1, 0), by decide⟩
  | 2 => ⟨(1, 2, 0), by decide⟩
  | 3 => ⟨(1, 1, 1), by decide⟩

lemma orb_rep : ∀ i : Fin 4, orb (rep i) = i := by decide
lemma orb_rot : ∀ p : Cell, orb (rot p) = orb p := by decide
lemma rot_orbit : ∀ p : Cell,
    p = rep (orb p) ∨ p = rot (rep (orb p)) ∨ p = rot (rot (rep (orb p))) := by decide

/-- Number of cells in orbit `i` equal to or adjacent to `p`. -/
def coeff (p : Cell) (i : Fin 4) : ℕ :=
  (Finset.univ.filter (fun q : Cell => (q = p ∨ adj p q) ∧ orb q = i)).card

lemma coeff_orb0 : ∀ p : Cell, orb p = 0 →
    coeff p 0 = 1 ∧ coeff p 1 = 1 ∧ coeff p 2 = 1 ∧ coeff p 3 = 0 := by decide

lemma coeff_orb1 : ∀ p : Cell, orb p = 1 →
    coeff p 0 = 1 ∧ coeff p 1 = 1 ∧ coeff p 2 = 2 ∧ coeff p 3 = 1 := by decide

lemma coeff_orb2 : ∀ p : Cell, orb p = 2 →
    coeff p 0 = 1 ∧ coeff p 1 = 2 ∧ coeff p 2 = 1 ∧ coeff p 3 = 1 := by decide

lemma coeff_orb3 : ∀ p : Cell, orb p = 3 →
    coeff p 0 = 0 ∧ coeff p 1 = 3 ∧ coeff p 2 = 3 ∧ coeff p 3 = 1 := by decide

lemma nbrSum_comp {n : ℕ} (v : Fin 4 → Fin (n + 1)) (p : Cell) :
    nbrSum (fun q => v (orb q)) p = ∑ i : Fin 4, coeff p i * (v i : ℕ) := by
  unfold nbrSum coeff
  have h1 : ∀ q : Cell,
      (if q = p ∨ adj p q then (v (orb q) : ℕ) else 0) =
      ∑ i : Fin 4, if (q = p ∨ adj p q) ∧ orb q = i then (v i : ℕ) else 0 := by
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
def valid4 (n : ℕ) (v : Fin 4 → Fin (n + 1)) : Prop :=
  (v 0 : ℕ) + (v 1 : ℕ) + 2 * (v 2 : ℕ) + (v 3 : ℕ) ≤ n ∧
  (v 0 : ℕ) + 2 * (v 1 : ℕ) + (v 2 : ℕ) + (v 3 : ℕ) ≤ n ∧
  3 * (v 1 : ℕ) + 3 * (v 2 : ℕ) + (v 3 : ℕ) ≤ n

instance (n : ℕ) (v : Fin 4 → Fin (n + 1)) : Decidable (valid4 n v) := by
  unfold valid4
  infer_instance

lemma valid_iff_valid4 {n : ℕ} (v : Fin 4 → Fin (n + 1)) :
    valid n (fun q => v (orb q)) ↔ valid4 n v := by
  constructor
  · rintro ⟨_, hsum⟩
    refine ⟨?_, ?_, ?_⟩
    · have h := hsum (rep 1)
      rw [nbrSum_comp, Fin.sum_univ_four] at h
      have hc := coeff_orb1 (rep 1) (orb_rep 1)
      rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] at h
      omega
    · have h := hsum (rep 2)
      rw [nbrSum_comp, Fin.sum_univ_four] at h
      have hc := coeff_orb2 (rep 2) (orb_rep 2)
      rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] at h
      omega
    · have h := hsum (rep 3)
      rw [nbrSum_comp, Fin.sum_univ_four] at h
      have hc := coeff_orb3 (rep 3) (orb_rep 3)
      rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] at h
      omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun p => by dsimp; rw [orb_rot], fun p => ?_⟩
    rw [nbrSum_comp, Fin.sum_univ_four]
    have hp : orb p = 0 ∨ orb p = 1 ∨ orb p = 2 ∨ orb p = 3 := by
      generalize orb p = i; fin_cases i <;> simp
    rcases hp with h | h | h | h
    · have hc := coeff_orb0 p h; rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]; omega
    · have hc := coeff_orb1 p h; rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]; omega
    · have hc := coeff_orb2 p h; rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]; omega
    · have hc := coeff_orb3 p h; rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]; omega

lemma a_eq_card4 (n : ℕ) :
    a n = (Finset.univ.filter (valid4 n)).card := by
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
    rw [← valid_iff_valid4, hfun]
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
      exact ⟨Finset.mem_univ _, (valid_iff_valid4 v).mpr hv.2⟩
    · funext i
      dsimp
      rw [orb_rep]

lemma a_eq_sum4 (n : ℕ) :
    a n = ∑ x1 ∈ range (n + 1), ∑ x2 ∈ range (n + 1), ∑ x3 ∈ range (n + 1),
      ∑ x0 ∈ range (n + 1),
        if x0 + x1 + 2 * x2 + x3 ≤ n ∧ x0 + 2 * x1 + x2 + x3 ≤ n ∧
          3 * x1 + 3 * x2 + x3 ≤ n then 1 else 0 := by
  rw [a_eq_card4, Finset.card_filter]
  let e : (Fin 4 → Fin (n + 1)) ≃ Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) :=
    { toFun := fun v => (v 1, v 2, v 3, v 0)
      invFun := fun t i => match i with
        | 0 => t.2.2.2
        | 1 => t.1
        | 2 => t.2.1
        | 3 => t.2.2.1
      left_inv := fun v => by funext i; fin_cases i <;> rfl
      right_inv := fun ⟨_, _, _, _⟩ => rfl }
  rw [← e.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  have hconv :
      (∑ x1 : Fin (n + 1), ∑ x2 : Fin (n + 1), ∑ x3 : Fin (n + 1), ∑ x0 : Fin (n + 1),
        if valid4 n (e.symm (x1, x2, x3, x0)) then 1 else 0) =
      ∑ x1 : Fin (n + 1), ∑ x2 : Fin (n + 1), ∑ x3 : Fin (n + 1), ∑ x0 : Fin (n + 1),
        if (x0 : ℕ) + (x1 : ℕ) + 2 * (x2 : ℕ) + (x3 : ℕ) ≤ n ∧
           (x0 : ℕ) + 2 * (x1 : ℕ) + (x2 : ℕ) + (x3 : ℕ) ≤ n ∧
           3 * (x1 : ℕ) + 3 * (x2 : ℕ) + (x3 : ℕ) ≤ n then 1 else 0 := by
    apply Finset.sum_congr rfl; intro x1 _
    apply Finset.sum_congr rfl; intro x2 _
    apply Finset.sum_congr rfl; intro x3 _
    apply Finset.sum_congr rfl; intro x0 _
    have hiff : valid4 n (e.symm (x1, x2, x3, x0)) ↔
        (x0 : ℕ) + (x1 : ℕ) + 2 * (x2 : ℕ) + (x3 : ℕ) ≤ n ∧
        (x0 : ℕ) + 2 * (x1 : ℕ) + (x2 : ℕ) + (x3 : ℕ) ≤ n ∧
        3 * (x1 : ℕ) + 3 * (x2 : ℕ) + (x3 : ℕ) ≤ n := Iff.rfl
    by_cases h : (x0 : ℕ) + (x1 : ℕ) + 2 * (x2 : ℕ) + (x3 : ℕ) ≤ n ∧
        (x0 : ℕ) + 2 * (x1 : ℕ) + (x2 : ℕ) + (x3 : ℕ) ≤ n ∧
        3 * (x1 : ℕ) + 3 * (x2 : ℕ) + (x3 : ℕ) ≤ n
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun hv => h (hiff.mp hv)), if_neg h]
  rw [hconv]
  rw [Fin.sum_univ_eq_sum_range (fun x1 => ∑ x2 : Fin (n + 1), ∑ x3 : Fin (n + 1), ∑ x0 : Fin (n + 1),
    if (x0 : ℕ) + x1 + 2 * (x2 : ℕ) + (x3 : ℕ) ≤ n ∧
       (x0 : ℕ) + 2 * x1 + (x2 : ℕ) + (x3 : ℕ) ≤ n ∧
       3 * x1 + 3 * (x2 : ℕ) + (x3 : ℕ) ≤ n then 1 else 0)]
  apply Finset.sum_congr rfl; intro x1 _
  rw [Fin.sum_univ_eq_sum_range (fun x2 => ∑ x3 : Fin (n + 1), ∑ x0 : Fin (n + 1),
    if (x0 : ℕ) + x1 + 2 * x2 + (x3 : ℕ) ≤ n ∧
       (x0 : ℕ) + 2 * x1 + x2 + (x3 : ℕ) ≤ n ∧
       3 * x1 + 3 * x2 + (x3 : ℕ) ≤ n then 1 else 0)]
  apply Finset.sum_congr rfl; intro x2 _
  rw [Fin.sum_univ_eq_sum_range (fun x3 => ∑ x0 : Fin (n + 1),
    if (x0 : ℕ) + x1 + 2 * x2 + x3 ≤ n ∧
       (x0 : ℕ) + 2 * x1 + x2 + x3 ≤ n ∧
       3 * x1 + 3 * x2 + x3 ≤ n then 1 else 0)]
  apply Finset.sum_congr rfl; intro x3 _
  rw [Fin.sum_univ_eq_sum_range (fun x0 =>
    if x0 + x1 + 2 * x2 + x3 ≤ n ∧
       x0 + 2 * x1 + x2 + x3 ≤ n ∧
       3 * x1 + 3 * x2 + x3 ≤ n then 1 else 0)]

lemma sum_x0 (n x1 x2 x3 : ℕ) (h3 : 3 * x1 + 3 * x2 + x3 ≤ n) :
    (∑ x0 ∈ range (n + 1),
      if x0 + x1 + 2 * x2 + x3 ≤ n ∧ x0 + 2 * x1 + x2 + x3 ≤ n ∧
        3 * x1 + 3 * x2 + x3 ≤ n then 1 else 0) =
    n + 1 - x1 - x2 - max x1 x2 - x3 := by
  have hfilt : (∑ x0 ∈ range (n + 1),
      if x0 + x1 + 2 * x2 + x3 ≤ n ∧ x0 + 2 * x1 + x2 + x3 ≤ n ∧
        3 * x1 + 3 * x2 + x3 ≤ n then 1 else 0) =
      ((range (n + 1)).filter (fun x0 => x0 < n + 1 - x1 - x2 - max x1 x2 - x3)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro x0 _
    have hiff : (x0 + x1 + 2 * x2 + x3 ≤ n ∧ x0 + 2 * x1 + x2 + x3 ≤ n ∧
        3 * x1 + 3 * x2 + x3 ≤ n) ↔ x0 < n + 1 - x1 - x2 - max x1 x2 - x3 := by omega
    simp only [hiff]
  rw [hfilt]
  have hsub : (range (n + 1)).filter (fun x0 => x0 < n + 1 - x1 - x2 - max x1 x2 - x3) =
      range (n + 1 - x1 - x2 - max x1 x2 - x3) := by
    ext x0
    simp only [mem_filter, mem_range]
    omega
  rw [hsub, card_range]

lemma a_eq_sum3 (n : ℕ) :
    a n = ∑ x1 ∈ range (n + 1), ∑ x2 ∈ range (n + 1),
      if 3 * (x1 + x2) ≤ n then
        ∑ x3 ∈ range (n - 3 * (x1 + x2) + 1), (n + 1 - x1 - x2 - max x1 x2 - x3)
      else 0 := by
  rw [a_eq_sum4]
  apply Finset.sum_congr rfl; intro x1 _
  apply Finset.sum_congr rfl; intro x2 _
  by_cases h12 : 3 * (x1 + x2) ≤ n
  · rw [if_pos h12]
    have hcongr : ∑ x3 ∈ range (n + 1),
        (∑ x0 ∈ range (n + 1),
          if x0 + x1 + 2 * x2 + x3 ≤ n ∧ x0 + 2 * x1 + x2 + x3 ≤ n ∧
            3 * x1 + 3 * x2 + x3 ≤ n then 1 else 0) =
        ∑ x3 ∈ range (n + 1),
          if x3 < n - 3 * (x1 + x2) + 1 then n + 1 - x1 - x2 - max x1 x2 - x3 else 0 := by
      apply Finset.sum_congr rfl
      intro x3 _
      by_cases hx3 : x3 < n - 3 * (x1 + x2) + 1
      · rw [if_pos hx3]
        exact sum_x0 n x1 x2 x3 (by omega)
      · rw [if_neg hx3]
        apply Finset.sum_eq_zero
        intro x0 _
        rw [if_neg]; omega
    rw [hcongr, ← Finset.sum_filter]
    congr 1
    ext x3; simp only [mem_filter, mem_range]; omega
  · rw [if_neg h12]
    apply Finset.sum_eq_zero; intro x3 _
    apply Finset.sum_eq_zero; intro x0 _
    rw [if_neg]; omega

lemma reindex_pair (n : ℕ) (F : ℕ → ℕ → ℕ) :
    (∑ x1 ∈ range (n + 1), ∑ x2 ∈ range (n + 1), if 3 * (x1 + x2) ≤ n then F x1 x2 else 0) =
    ∑ s ∈ range (n / 3 + 1), ∑ x1 ∈ range (s + 1), F x1 (s - x1) := by
  have h1 : ∀ x1 x2 : ℕ,
      (if 3 * (x1 + x2) ≤ n then F x1 x2 else 0) =
      ∑ s ∈ range (n / 3 + 1), if x1 + x2 = s then F x1 x2 else 0 := by
    intro x1 x2
    by_cases h : 3 * (x1 + x2) ≤ n
    · rw [if_pos h, Finset.sum_eq_single (x1 + x2)]
      · simp
      · intro s _ hs; simp [Ne.symm hs]
      · intro hs; simp only [mem_range] at hs; omega
    · rw [if_neg h]
      symm
      apply Finset.sum_eq_zero
      intro s hs
      simp only [mem_range] at hs
      rw [if_neg]; omega
  simp_rw [h1]
  conv_lhs =>
    arg 2; ext x1
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [mem_range] at hs
  have h2 : ∀ x1 ∈ range (n + 1),
      (∑ x2 ∈ range (n + 1), if x1 + x2 = s then F x1 x2 else 0) =
      if x1 < s + 1 then F x1 (s - x1) else 0 := by
    intro x1 _
    by_cases hx1 : x1 < s + 1
    · rw [if_pos hx1, Finset.sum_eq_single (s - x1)]
      · rw [if_pos (by omega)]
      · intro x2 _ hx2; rw [if_neg]; omega
      · intro hmem; simp only [mem_range] at hmem; omega
    · rw [if_neg hx1]
      apply Finset.sum_eq_zero
      intro x2 _
      rw [if_neg]; omega
  rw [Finset.sum_congr rfl h2, ← Finset.sum_filter]
  congr 1
  ext x1; simp only [mem_filter, mem_range]; omega

lemma sum_range_sub_cast (A L : ℕ) (h : L ≤ A) :
    2 * (∑ x ∈ range (L + 1), (A - x : ℕ) : ℤ) =
    ((L : ℤ) + 1) * (2 * (A : ℤ) - (L : ℤ)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, Nat.cast_add, mul_add, ih (by omega)]
    have hsub : ((A - (L + 1) : ℕ) : ℤ) = (A : ℤ) - ((L : ℤ) + 1) := by omega
    rw [hsub]
    push_cast
    ring

lemma sum_max_even (k : ℕ) :
    (∑ x ∈ range (2 * k + 1), (max x (2 * k - x) : ℕ) : ℤ) = 3 * (k : ℤ) ^ 2 + 2 * (k : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : ∑ x ∈ range (2 * (k + 1) + 1), max x (2 * (k + 1) - x) =
        (∑ x ∈ range (2 * k + 1), max x (2 * k - x)) + (2 * k + 1) + (2 * k + 2) + (2 * k + 2) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega, Finset.sum_range_succ]
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
      rw [Finset.sum_range_succ']
      have hcongr : ∑ x ∈ range (2 * k + 1), max (x + 1) (2 * k + 1 + 1 - (x + 1)) =
          ∑ x ∈ range (2 * k + 1), (max x (2 * k - x) + 1) := by
        apply Finset.sum_congr rfl
        intro x hx; simp only [mem_range] at hx; omega
      rw [hcongr, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
      have h0 : max 0 (2 * k + 1 + 1 - 0) = 2 * k + 2 := by omega
      have hlast : max (2 * k + 2) (2 * k + 1 + 1 - (2 * k + 2)) = 2 * k + 2 := by omega
      rw [h0, hlast]
    have hc : (∑ x ∈ range (2 * (k + 1) + 1), (max x (2 * (k + 1) - x) : ℕ) : ℤ) =
        (∑ x ∈ range (2 * k + 1), (max x (2 * k - x) : ℕ) : ℤ) +
          (2 * (k : ℤ) + 1) + (2 * (k : ℤ) + 2) + (2 * (k : ℤ) + 2) := by
      exact_mod_cast hstep
    rw [hc, ih]
    push_cast
    ring

lemma sum_max_odd (k : ℕ) :
    (∑ x ∈ range (2 * k + 2), (max x (2 * k + 1 - x) : ℕ) : ℤ) =
    3 * (k : ℤ) ^ 2 + 5 * (k : ℤ) + 2 := by
  induction k with
  | zero => simp [Finset.sum_range_succ]
  | succ k ih =>
    have hstep : ∑ x ∈ range (2 * (k + 1) + 2), max x (2 * (k + 1) + 1 - x) =
        (∑ x ∈ range (2 * k + 2), max x (2 * k + 1 - x)) + (2 * k + 2) + (2 * k + 3) + (2 * k + 3) := by
      rw [show 2 * (k + 1) + 2 = (2 * k + 3) + 1 by omega, Finset.sum_range_succ]
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega]
      rw [Finset.sum_range_succ']
      have hcongr : ∑ x ∈ range (2 * k + 2), max (x + 1) (2 * k + 2 + 1 - (x + 1)) =
          ∑ x ∈ range (2 * k + 2), (max x (2 * k + 1 - x) + 1) := by
        apply Finset.sum_congr rfl
        intro x hx; simp only [mem_range] at hx; omega
      rw [hcongr, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
      have h0 : max 0 (2 * k + 2 + 1 - 0) = 2 * k + 3 := by omega
      have hlast : max (2 * k + 3) (2 * k + 2 + 1 - (2 * k + 3)) = 2 * k + 3 := by omega
      rw [h0, hlast]
    have hc : (∑ x ∈ range (2 * (k + 1) + 2), (max x (2 * (k + 1) + 1 - x) : ℕ) : ℤ) =
        (∑ x ∈ range (2 * k + 2), (max x (2 * k + 1 - x) : ℕ) : ℤ) +
          (2 * (k : ℤ) + 2) + (2 * (k : ℤ) + 3) + (2 * (k : ℤ) + 3) := by
      exact_mod_cast hstep
    rw [hc, ih]
    push_cast
    ring

def innerTerm (n s : ℕ) : ℕ :=
  ∑ x1 ∈ range (s + 1),
    ∑ x3 ∈ range (n - 3 * s + 1), (n + 1 - x1 - (s - x1) - max x1 (s - x1) - x3)

lemma a_eq_sum_s (n : ℕ) : a n = ∑ s ∈ range (n / 3 + 1), innerTerm n s := by
  rw [a_eq_sum3]
  have h := reindex_pair n (fun x1 x2 =>
    ∑ x3 ∈ range (n - 3 * (x1 + x2) + 1), (n + 1 - x1 - x2 - max x1 x2 - x3))
  rw [h]
  apply Finset.sum_congr rfl
  intro s _
  unfold innerTerm
  apply Finset.sum_congr rfl
  intro x1 hx1
  simp only [mem_range] at hx1
  have hadd : x1 + (s - x1) = s := by omega
  rw [hadd]

lemma innerTerm_even (n k : ℕ) (h : 6 * k ≤ n) :
    2 * (innerTerm n (2 * k) : ℤ) =
    12 * (k : ℤ) ^ 3 - 14 * (k : ℤ) ^ 2 * (n : ℤ) - 14 * (k : ℤ) ^ 2 +
      2 * (k : ℤ) * (n : ℤ) ^ 2 - 2 * (k : ℤ) * (n : ℤ) - 10 * (k : ℤ) +
      (n : ℤ) ^ 2 + 3 * (n : ℤ) + 2 := by
  unfold innerTerm
  rw [Nat.cast_sum, Finset.mul_sum]
  simp_rw [Nat.cast_sum]
  have h1 : ∀ x1 ∈ range (2 * k + 1),
      2 * (∑ x3 ∈ range (n - 3 * (2 * k) + 1),
        (n + 1 - x1 - (2 * k - x1) - max x1 (2 * k - x1) - x3 : ℕ) : ℤ) =
      (((n : ℤ) - 6 * (k : ℤ)) + 1) *
        ((n : ℤ) + 2 + 2 * (k : ℤ) - 2 * (max x1 (2 * k - x1) : ℤ)) := by
    intro x1 hx1
    simp only [mem_range] at hx1
    have hsub := sum_range_sub_cast (n + 1 - x1 - (2 * k - x1) - max x1 (2 * k - x1))
      (n - 3 * (2 * k)) (by omega)
    rw [hsub]
    have hL : ((n - 3 * (2 * k) : ℕ) : ℤ) = (n : ℤ) - 6 * (k : ℤ) := by omega
    have hA : ((n + 1 - x1 - (2 * k - x1) - max x1 (2 * k - x1) : ℕ) : ℤ) =
        (n : ℤ) + 1 - 2 * (k : ℤ) - (max x1 (2 * k - x1) : ℤ) := by omega
    rw [hL, hA]; ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  have hm : ∑ i ∈ range (2 * k + 1), max (i : ℤ) (2 * (k : ℤ) - (i : ℤ)) =
      3 * (k : ℤ) ^ 2 + 2 * (k : ℤ) := by
    rw [← sum_max_even k]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [mem_range] at hi
    rw [Nat.cast_max]; congr 1; omega
  push_cast
  rw [hm]; ring

lemma innerTerm_odd (n k : ℕ) (h : 6 * k + 3 ≤ n) :
    2 * (innerTerm n (2 * k + 1) : ℤ) =
    12 * (k : ℤ) ^ 3 - 14 * (k : ℤ) ^ 2 * (n : ℤ) + 4 * (k : ℤ) ^ 2 +
      2 * (k : ℤ) * (n : ℤ) ^ 2 - 16 * (k : ℤ) * (n : ℤ) - 12 * (k : ℤ) +
      2 * (n : ℤ) ^ 2 - 2 * (n : ℤ) - 4 := by
  unfold innerTerm
  rw [Nat.cast_sum, Finset.mul_sum]
  simp_rw [Nat.cast_sum]
  have h1 : ∀ x1 ∈ range (2 * k + 1 + 1),
      2 * (∑ x3 ∈ range (n - 3 * (2 * k + 1) + 1),
        (n + 1 - x1 - (2 * k + 1 - x1) - max x1 (2 * k + 1 - x1) - x3 : ℕ) : ℤ) =
      (((n : ℤ) - 6 * (k : ℤ) - 3) + 1) *
        ((n : ℤ) + 3 + 2 * (k : ℤ) - 2 * (max x1 (2 * k + 1 - x1) : ℤ)) := by
    intro x1 hx1
    simp only [mem_range] at hx1
    have hsub := sum_range_sub_cast (n + 1 - x1 - (2 * k + 1 - x1) - max x1 (2 * k + 1 - x1))
      (n - 3 * (2 * k + 1)) (by omega)
    rw [hsub]
    have hL : ((n - 3 * (2 * k + 1) : ℕ) : ℤ) = (n : ℤ) - 6 * (k : ℤ) - 3 := by omega
    have hA : ((n + 1 - x1 - (2 * k + 1 - x1) - max x1 (2 * k + 1 - x1) : ℕ) : ℤ) =
        (n : ℤ) + 1 - (2 * (k : ℤ) + 1) - (max x1 (2 * k + 1 - x1) : ℤ) := by omega
    rw [hL, hA]; ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  have hm : ∑ i ∈ range (2 * k + 1 + 1), max (i : ℤ) (2 * (k : ℤ) + 1 - (i : ℤ)) =
      3 * (k : ℤ) ^ 2 + 5 * (k : ℤ) + 2 := by
    rw [← sum_max_odd k]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [mem_range] at hi
    rw [Nat.cast_max]; congr 1; omega
  push_cast
  rw [hm]; ring

lemma sum_poly_even (N : ℤ) (m : ℕ) :
    6 * ∑ k ∈ range m,
      (12 * (k : ℤ) ^ 3 - 14 * (k : ℤ) ^ 2 * N - 14 * (k : ℤ) ^ 2 +
        2 * (k : ℤ) * N ^ 2 - 2 * (k : ℤ) * N - 10 * (k : ℤ) +
        N ^ 2 + 3 * N + 2) =
    18 * (m : ℤ) ^ 4 - 28 * (m : ℤ) ^ 3 * N - 64 * (m : ℤ) ^ 3 +
      6 * (m : ℤ) ^ 2 * N ^ 2 + 36 * (m : ℤ) ^ 2 * N + 30 * (m : ℤ) ^ 2 +
      10 * (m : ℤ) * N + 28 * (m : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast; ring

lemma sum_poly_odd (N : ℤ) (m : ℕ) :
    6 * ∑ k ∈ range m,
      (12 * (k : ℤ) ^ 3 - 14 * (k : ℤ) ^ 2 * N + 4 * (k : ℤ) ^ 2 +
        2 * (k : ℤ) * N ^ 2 - 16 * (k : ℤ) * N - 12 * (k : ℤ) +
        2 * N ^ 2 - 2 * N - 4) =
    18 * (m : ℤ) ^ 4 - 28 * (m : ℤ) ^ 3 * N - 28 * (m : ℤ) ^ 3 +
      6 * (m : ℤ) ^ 2 * N ^ 2 - 6 * (m : ℤ) ^ 2 * N - 30 * (m : ℤ) ^ 2 +
      6 * (m : ℤ) * N ^ 2 + 22 * (m : ℤ) * N + 16 * (m : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast; ring

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
  | 0 => 66 * q ^ 4 + 152 * q ^ 3 + 126 * q ^ 2 + 46 * q + 6
  | 1 => 66 * q ^ 4 + 196 * q ^ 3 + 213 * q ^ 2 + 101 * q + 18
  | 2 => 66 * q ^ 4 + 240 * q ^ 3 + 312 * q ^ 2 + 174 * q + 36
  | 3 => 66 * q ^ 4 + 284 * q ^ 3 + 453 * q ^ 2 + 319 * q + 84
  | 4 => 66 * q ^ 4 + 328 * q ^ 3 + 606 * q ^ 2 + 494 * q + 150
  | _ => 66 * q ^ 4 + 372 * q ^ 3 + 771 * q ^ 2 + 699 * q + 234

lemma a_mod6 (q r : ℕ) (hr : r < 6) :
    6 * (a (6 * q + r) : ℤ) = polyMod6 (q : ℤ) r := by
  rw [a_eq_sum_s]
  suffices hkey : 12 * (∑ s ∈ range ((6 * q + r) / 3 + 1), (innerTerm (6 * q + r) s : ℤ)) =
      2 * polyMod6 (q : ℤ) r by
    rw [Nat.cast_sum]
    linarith
  interval_cases r
  · rw [show (6 * q + 0) / 3 + 1 = 2 * q + 1 by omega, sum_split_even]
    rw [show (12 : ℤ) * ((∑ k ∈ range (q + 1), (innerTerm (6 * q + 0) (2 * k) : ℤ)) +
          ∑ k ∈ range q, (innerTerm (6 * q + 0) (2 * k + 1) : ℤ)) =
        6 * (∑ k ∈ range (q + 1), 2 * (innerTerm (6 * q + 0) (2 * k) : ℤ)) +
        6 * (∑ k ∈ range q, 2 * (innerTerm (6 * q + 0) (2 * k + 1) : ℤ)) by
          simp only [← Finset.mul_sum]; ring]
    rw [Finset.sum_congr rfl (fun k hk => innerTerm_even (6 * q + 0) k (by simp only [mem_range] at hk; omega))]
    rw [Finset.sum_congr rfl (fun k hk => innerTerm_odd (6 * q + 0) k (by simp only [mem_range] at hk; omega))]
    rw [sum_poly_even, sum_poly_odd]; unfold polyMod6; push_cast; ring
  · rw [show (6 * q + 1) / 3 + 1 = 2 * q + 1 by omega, sum_split_even]
    rw [show (12 : ℤ) * ((∑ k ∈ range (q + 1), (innerTerm (6 * q + 1) (2 * k) : ℤ)) +
          ∑ k ∈ range q, (innerTerm (6 * q + 1) (2 * k + 1) : ℤ)) =
        6 * (∑ k ∈ range (q + 1), 2 * (innerTerm (6 * q + 1) (2 * k) : ℤ)) +
        6 * (∑ k ∈ range q, 2 * (innerTerm (6 * q + 1) (2 * k + 1) : ℤ)) by
          simp only [← Finset.mul_sum]; ring]
    rw [Finset.sum_congr rfl (fun k hk => innerTerm_even (6 * q + 1) k (by simp only [mem_range] at hk; omega))]
    rw [Finset.sum_congr rfl (fun k hk => innerTerm_odd (6 * q + 1) k (by simp only [mem_range] at hk; omega))]
    rw [sum_poly_even, sum_poly_odd]; unfold polyMod6; push_cast; ring
  · rw [show (6 * q + 2) / 3 + 1 = 2 * q + 1 by omega, sum_split_even]
    rw [show (12 : ℤ) * ((∑ k ∈ range (q + 1), (innerTerm (6 * q + 2) (2 * k) : ℤ)) +
          ∑ k ∈ range q, (innerTerm (6 * q + 2) (2 * k + 1) : ℤ)) =
        6 * (∑ k ∈ range (q + 1), 2 * (innerTerm (6 * q + 2) (2 * k) : ℤ)) +
        6 * (∑ k ∈ range q, 2 * (innerTerm (6 * q + 2) (2 * k + 1) : ℤ)) by
          simp only [← Finset.mul_sum]; ring]
    rw [Finset.sum_congr rfl (fun k hk => innerTerm_even (6 * q + 2) k (by simp only [mem_range] at hk; omega))]
    rw [Finset.sum_congr rfl (fun k hk => innerTerm_odd (6 * q + 2) k (by simp only [mem_range] at hk; omega))]
    rw [sum_poly_even, sum_poly_odd]; unfold polyMod6; push_cast; ring
  · rw [show (6 * q + 3) / 3 + 1 = 2 * q + 2 by omega, sum_split_odd]
    rw [show (12 : ℤ) * ((∑ k ∈ range (q + 1), (innerTerm (6 * q + 3) (2 * k) : ℤ)) +
          ∑ k ∈ range (q + 1), (innerTerm (6 * q + 3) (2 * k + 1) : ℤ)) =
        6 * (∑ k ∈ range (q + 1), 2 * (innerTerm (6 * q + 3) (2 * k) : ℤ)) +
        6 * (∑ k ∈ range (q + 1), 2 * (innerTerm (6 * q + 3) (2 * k + 1) : ℤ)) by
          simp only [← Finset.mul_sum]; ring]
    rw [Finset.sum_congr rfl (fun k hk => innerTerm_even (6 * q + 3) k (by simp only [mem_range] at hk; omega))]
    rw [Finset.sum_congr rfl (fun k hk => innerTerm_odd (6 * q + 3) k (by simp only [mem_range] at hk; omega))]
    rw [sum_poly_even, sum_poly_odd]; unfold polyMod6; push_cast; ring
  · rw [show (6 * q + 4) / 3 + 1 = 2 * q + 2 by omega, sum_split_odd]
    rw [show (12 : ℤ) * ((∑ k ∈ range (q + 1), (innerTerm (6 * q + 4) (2 * k) : ℤ)) +
          ∑ k ∈ range (q + 1), (innerTerm (6 * q + 4) (2 * k + 1) : ℤ)) =
        6 * (∑ k ∈ range (q + 1), 2 * (innerTerm (6 * q + 4) (2 * k) : ℤ)) +
        6 * (∑ k ∈ range (q + 1), 2 * (innerTerm (6 * q + 4) (2 * k + 1) : ℤ)) by
          simp only [← Finset.mul_sum]; ring]
    rw [Finset.sum_congr rfl (fun k hk => innerTerm_even (6 * q + 4) k (by simp only [mem_range] at hk; omega))]
    rw [Finset.sum_congr rfl (fun k hk => innerTerm_odd (6 * q + 4) k (by simp only [mem_range] at hk; omega))]
    rw [sum_poly_even, sum_poly_odd]; unfold polyMod6; push_cast; ring
  · rw [show (6 * q + 5) / 3 + 1 = 2 * q + 2 by omega, sum_split_odd]
    rw [show (12 : ℤ) * ((∑ k ∈ range (q + 1), (innerTerm (6 * q + 5) (2 * k) : ℤ)) +
          ∑ k ∈ range (q + 1), (innerTerm (6 * q + 5) (2 * k + 1) : ℤ)) =
        6 * (∑ k ∈ range (q + 1), 2 * (innerTerm (6 * q + 5) (2 * k) : ℤ)) +
        6 * (∑ k ∈ range (q + 1), 2 * (innerTerm (6 * q + 5) (2 * k + 1) : ℤ)) by
          simp only [← Finset.mul_sum]; ring]
    rw [Finset.sum_congr rfl (fun k hk => innerTerm_even (6 * q + 5) k (by simp only [mem_range] at hk; omega))]
    rw [Finset.sum_congr rfl (fun k hk => innerTerm_odd (6 * q + 5) k (by simp only [mem_range] at hk; omega))]
    rw [sum_poly_even, sum_poly_odd]; unfold polyMod6; push_cast; ring

lemma a_small :
    a 0 = 1 ∧ a 1 = 3 ∧ a 2 = 6 ∧ a 3 = 14 ∧ a 4 = 25 ∧ a 5 = 39 ∧ a 6 = 66 ∧
    a 7 = 99 ∧ a 8 = 138 ∧ a 9 = 201 ∧ a 10 = 274 ∧ a 11 = 357 ∧ a 12 = 479 ∧ a 13 = 616 := by
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
  have h12 := a_mod6 2 0 (by omega)
  have h13 := a_mod6 2 1 (by omega)
  norm_num [polyMod6] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

lemma hrec : ∀ n : ℕ, 13 < n →
    (a n : ℤ) = 2 * a (n - 1) - a (n - 2) + 2 * a (n - 3) - 4 * a (n - 4) +
      2 * a (n - 5) - 2 * a (n - 9) + 4 * a (n - 10) - 2 * a (n - 11) +
      a (n - 12) - 2 * a (n - 13) + a (n - 14) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 14 := ⟨n - 14, by omega⟩
  have hdiv : m = 6 * (m / 6) + m % 6 := (Nat.div_add_mod m 6).symm
  set q := m / 6
  set r := m % 6
  have hr : r < 6 := Nat.mod_lt m (by omega)
  rw [hdiv]
  suffices h6 :
      6 * (a (6 * q + r + 14) : ℤ) =
      2 * (6 * (a (6 * q + r + 14 - 1) : ℤ)) - (6 * (a (6 * q + r + 14 - 2) : ℤ)) +
      2 * (6 * (a (6 * q + r + 14 - 3) : ℤ)) - 4 * (6 * (a (6 * q + r + 14 - 4) : ℤ)) +
      2 * (6 * (a (6 * q + r + 14 - 5) : ℤ)) - 2 * (6 * (a (6 * q + r + 14 - 9) : ℤ)) +
      4 * (6 * (a (6 * q + r + 14 - 10) : ℤ)) - 2 * (6 * (a (6 * q + r + 14 - 11) : ℤ)) +
      (6 * (a (6 * q + r + 14 - 12) : ℤ)) - 2 * (6 * (a (6 * q + r + 14 - 13) : ℤ)) +
      (6 * (a (6 * q + r + 14 - 14) : ℤ)) by
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
  have h30 := a_mod6 (q + 3) 0 (by omega)
  have h31 := a_mod6 (q + 3) 1 (by omega)
  interval_cases r
  · rw [show 6 * q + 0 + 14 = 6 * (q + 2) + 2 by omega,
        show 6 * (q + 2) + 2 - 1 = 6 * (q + 2) + 1 by omega,
        show 6 * (q + 2) + 2 - 2 = 6 * (q + 2) + 0 by omega,
        show 6 * (q + 2) + 2 - 3 = 6 * (q + 1) + 5 by omega,
        show 6 * (q + 2) + 2 - 4 = 6 * (q + 1) + 4 by omega,
        show 6 * (q + 2) + 2 - 5 = 6 * (q + 1) + 3 by omega,
        show 6 * (q + 2) + 2 - 9 = 6 * q + 5 by omega,
        show 6 * (q + 2) + 2 - 10 = 6 * q + 4 by omega,
        show 6 * (q + 2) + 2 - 11 = 6 * q + 3 by omega,
        show 6 * (q + 2) + 2 - 12 = 6 * q + 2 by omega,
        show 6 * (q + 2) + 2 - 13 = 6 * q + 1 by omega,
        show 6 * (q + 2) + 2 - 14 = 6 * q + 0 by omega]
    rw [h22, h21, h20, h15, h14, h13, h05, h04, h03, h02, h01, h00]
    simp only [polyMod6]; push_cast; ring
  · rw [show 6 * q + 1 + 14 = 6 * (q + 2) + 3 by omega,
        show 6 * (q + 2) + 3 - 1 = 6 * (q + 2) + 2 by omega,
        show 6 * (q + 2) + 3 - 2 = 6 * (q + 2) + 1 by omega,
        show 6 * (q + 2) + 3 - 3 = 6 * (q + 2) + 0 by omega,
        show 6 * (q + 2) + 3 - 4 = 6 * (q + 1) + 5 by omega,
        show 6 * (q + 2) + 3 - 5 = 6 * (q + 1) + 4 by omega,
        show 6 * (q + 2) + 3 - 9 = 6 * (q + 1) + 0 by omega,
        show 6 * (q + 2) + 3 - 10 = 6 * q + 5 by omega,
        show 6 * (q + 2) + 3 - 11 = 6 * q + 4 by omega,
        show 6 * (q + 2) + 3 - 12 = 6 * q + 3 by omega,
        show 6 * (q + 2) + 3 - 13 = 6 * q + 2 by omega,
        show 6 * (q + 2) + 3 - 14 = 6 * q + 1 by omega]
    rw [h23, h22, h21, h20, h15, h14, h10, h05, h04, h03, h02, h01]
    simp only [polyMod6]; push_cast; ring
  · rw [show 6 * q + 2 + 14 = 6 * (q + 2) + 4 by omega,
        show 6 * (q + 2) + 4 - 1 = 6 * (q + 2) + 3 by omega,
        show 6 * (q + 2) + 4 - 2 = 6 * (q + 2) + 2 by omega,
        show 6 * (q + 2) + 4 - 3 = 6 * (q + 2) + 1 by omega,
        show 6 * (q + 2) + 4 - 4 = 6 * (q + 2) + 0 by omega,
        show 6 * (q + 2) + 4 - 5 = 6 * (q + 1) + 5 by omega,
        show 6 * (q + 2) + 4 - 9 = 6 * (q + 1) + 1 by omega,
        show 6 * (q + 2) + 4 - 10 = 6 * (q + 1) + 0 by omega,
        show 6 * (q + 2) + 4 - 11 = 6 * q + 5 by omega,
        show 6 * (q + 2) + 4 - 12 = 6 * q + 4 by omega,
        show 6 * (q + 2) + 4 - 13 = 6 * q + 3 by omega,
        show 6 * (q + 2) + 4 - 14 = 6 * q + 2 by omega]
    rw [h24, h23, h22, h21, h20, h15, h11, h10, h05, h04, h03, h02]
    simp only [polyMod6]; push_cast; ring
  · rw [show 6 * q + 3 + 14 = 6 * (q + 2) + 5 by omega,
        show 6 * (q + 2) + 5 - 1 = 6 * (q + 2) + 4 by omega,
        show 6 * (q + 2) + 5 - 2 = 6 * (q + 2) + 3 by omega,
        show 6 * (q + 2) + 5 - 3 = 6 * (q + 2) + 2 by omega,
        show 6 * (q + 2) + 5 - 4 = 6 * (q + 2) + 1 by omega,
        show 6 * (q + 2) + 5 - 5 = 6 * (q + 2) + 0 by omega,
        show 6 * (q + 2) + 5 - 9 = 6 * (q + 1) + 2 by omega,
        show 6 * (q + 2) + 5 - 10 = 6 * (q + 1) + 1 by omega,
        show 6 * (q + 2) + 5 - 11 = 6 * (q + 1) + 0 by omega,
        show 6 * (q + 2) + 5 - 12 = 6 * q + 5 by omega,
        show 6 * (q + 2) + 5 - 13 = 6 * q + 4 by omega,
        show 6 * (q + 2) + 5 - 14 = 6 * q + 3 by omega]
    rw [h25, h24, h23, h22, h21, h20, h12, h11, h10, h05, h04, h03]
    simp only [polyMod6]; push_cast; ring
  · rw [show 6 * q + 4 + 14 = 6 * (q + 3) + 0 by omega,
        show 6 * (q + 3) + 0 - 1 = 6 * (q + 2) + 5 by omega,
        show 6 * (q + 3) + 0 - 2 = 6 * (q + 2) + 4 by omega,
        show 6 * (q + 3) + 0 - 3 = 6 * (q + 2) + 3 by omega,
        show 6 * (q + 3) + 0 - 4 = 6 * (q + 2) + 2 by omega,
        show 6 * (q + 3) + 0 - 5 = 6 * (q + 2) + 1 by omega,
        show 6 * (q + 3) + 0 - 9 = 6 * (q + 1) + 3 by omega,
        show 6 * (q + 3) + 0 - 10 = 6 * (q + 1) + 2 by omega,
        show 6 * (q + 3) + 0 - 11 = 6 * (q + 1) + 1 by omega,
        show 6 * (q + 3) + 0 - 12 = 6 * (q + 1) + 0 by omega,
        show 6 * (q + 3) + 0 - 13 = 6 * q + 5 by omega,
        show 6 * (q + 3) + 0 - 14 = 6 * q + 4 by omega]
    rw [h30, h25, h24, h23, h22, h21, h13, h12, h11, h10, h05, h04]
    simp only [polyMod6]; push_cast; ring
  · rw [show 6 * q + 5 + 14 = 6 * (q + 3) + 1 by omega,
        show 6 * (q + 3) + 1 - 1 = 6 * (q + 3) + 0 by omega,
        show 6 * (q + 3) + 1 - 2 = 6 * (q + 2) + 5 by omega,
        show 6 * (q + 3) + 1 - 3 = 6 * (q + 2) + 4 by omega,
        show 6 * (q + 3) + 1 - 4 = 6 * (q + 2) + 3 by omega,
        show 6 * (q + 3) + 1 - 5 = 6 * (q + 2) + 2 by omega,
        show 6 * (q + 3) + 1 - 9 = 6 * (q + 1) + 4 by omega,
        show 6 * (q + 3) + 1 - 10 = 6 * (q + 1) + 3 by omega,
        show 6 * (q + 3) + 1 - 11 = 6 * (q + 1) + 2 by omega,
        show 6 * (q + 3) + 1 - 12 = 6 * (q + 1) + 1 by omega,
        show 6 * (q + 3) + 1 - 13 = 6 * (q + 1) + 0 by omega,
        show 6 * (q + 3) + 1 - 14 = 6 * q + 5 by omega]
    rw [h31, h30, h25, h24, h23, h22, h14, h13, h12, h11, h10, h05]
    simp only [polyMod6]; push_cast; ring

lemma hgf :
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - X) ^ 5 * (1 + X) * (1 - X + X ^ 2) * (1 + X + X ^ 2) ^ 3) =
    1 + X + X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + 3 * X ^ 6 := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13⟩ := a_small
  set S := PowerSeries.mk (fun n => (a n : ℚ)) with hS
  have hl : S * ((1 - X) ^ 5 * (1 + X) * (1 - X + X ^ 2) * (1 + X + X ^ 2) ^ 3) =
      S + C (-2 : ℚ) * (S * X ^ 1) + C (1 : ℚ) * (S * X ^ 2) +
      C (-2 : ℚ) * (S * X ^ 3) + C (4 : ℚ) * (S * X ^ 4) +
      C (-2 : ℚ) * (S * X ^ 5) + C (2 : ℚ) * (S * X ^ 9) +
      C (-4 : ℚ) * (S * X ^ 10) + C (2 : ℚ) * (S * X ^ 11) +
      C (-1 : ℚ) * (S * X ^ 12) + C (2 : ℚ) * (S * X ^ 13) +
      C (-1 : ℚ) * (S * X ^ 14) := by
    simp only [map_neg, map_ofNat, map_one]; ring
  have hr : (1 + X + X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + 3 * X ^ 6 : PowerSeries ℚ) =
      C (1 : ℚ) + C (1 : ℚ) * X ^ 1 + C (1 : ℚ) * X ^ 2 + C (3 : ℚ) * X ^ 3 +
      C (1 : ℚ) * X ^ 4 + C (1 : ℚ) * X ^ 5 + C (3 : ℚ) * X ^ 6 := by
    simp only [map_ofNat, map_one]; ring
  rw [hl, hr]
  ext n
  simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hS, coeff_mk]
  rcases Nat.lt_or_ge n 14 with hn | hn
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] <;> norm_num
  · have hq : (a n : ℚ) = 2 * a (n - 1) - a (n - 2) + 2 * a (n - 3) - 4 * a (n - 4) +
        2 * a (n - 5) - 2 * a (n - 9) + 4 * a (n - 10) - 2 * a (n - 11) +
        a (n - 12) - 2 * a (n - 13) + a (n - 14) := by
      exact_mod_cast hrec n (by omega)
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have c4 : 4 ≤ n := by omega
    have c5 : 5 ≤ n := by omega
    have c6 : 6 ≤ n := by omega
    have c9 : 9 ≤ n := by omega
    have c10 : 10 ≤ n := by omega
    have c11 : 11 ≤ n := by omega
    have c12 : 12 ≤ n := by omega
    have c13 : 13 ≤ n := by omega
    have c14 : 14 ≤ n := by omega
    have d0 : n ≠ 0 := by omega
    have e1 : n - 1 ≠ 0 := by omega
    have e2 : n - 2 ≠ 0 := by omega
    have e3 : n - 3 ≠ 0 := by omega
    have e4 : n - 4 ≠ 0 := by omega
    have e5 : n - 5 ≠ 0 := by omega
    have e6 : n - 6 ≠ 0 := by omega
    simp only [c1, c2, c3, c4, c5, c6, c9, c10, c11, c12, c13, c14,
      d0, e1, e2, e3, e4, e5, e6, if_true, if_false]
    linear_combination hq

theorem main_proof :
    (PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - X) ^ 5 * (1 + X) * (1 - X + X ^ 2) * (1 + X + X ^ 2) ^ 3) =
      1 + X + X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + 3 * X ^ 6) ∧
    (∀ n : ℕ, 13 < n →
      (a n : ℤ) = 2 * a (n - 1) - a (n - 2) + 2 * a (n - 3) - 4 * a (n - 4) +
        2 * a (n - 5) - 2 * a (n - 9) + 4 * a (n - 10) - 2 * a (n - 11) +
        a (n - 12) - 2 * a (n - 13) + a (n - 14)) :=
  ⟨hgf, hrec⟩

end OMA.P166212

theorem OMA.solution : type_of% @OMA.S_oeis_a166212.main := OMA.P166212.main_proof
