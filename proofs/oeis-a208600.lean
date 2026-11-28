import OMAStatements.S_oeis_a208600
import Mathlib

namespace OMA.Helpers_a208600

open PowerSeries Finset OMA.S_oeis_a208600

lemma geomPS (m : ℕ) : (∑ t ∈ range m, (X : PowerSeries ℤ) ^ t) = (1 - X ^ m) * PowerSeries.mk 1 := by
  have h1 : (∑ t ∈ range m, (X : PowerSeries ℤ) ^ t) * (1 - X) = 1 - X ^ m := by
    have := geom_sum_mul (X : PowerSeries ℤ) m
    linear_combination -this
  calc (∑ t ∈ range m, (X : PowerSeries ℤ) ^ t)
      = (∑ t ∈ range m, (X : PowerSeries ℤ) ^ t) * ((1 - X) * PowerSeries.mk 1) := by
        rw [mul_comm (1 - X), mk_one_mul_one_sub_eq_one, mul_one]
    _ = (1 - X ^ m) * PowerSeries.mk 1 := by rw [← mul_assoc, h1]

lemma card_eq_coeff (k m N : ℕ) :
    ((#{f ∈ Fintype.piFinset (fun _ : Fin k => range m) | ∑ i, f i = N} : ℕ) : ℤ) =
      coeff N ((∑ t ∈ range m, (X : PowerSeries ℤ) ^ t) ^ k) := by
  have : (∑ t ∈ range m, (X : PowerSeries ℤ) ^ t) ^ k =
      ∏ _i : Fin k, ∑ t ∈ range m, (X : PowerSeries ℤ) ^ t := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [this, Finset.prod_univ_sum]
  simp_rw [Finset.prod_pow_eq_pow_sum, map_sum, coeff_X_pow]
  rw [Finset.sum_boole]
  congr 2
  ext f; simp [eq_comm]

lemma coeff_geom_pow (k m N : ℕ) :
    coeff N ((∑ t ∈ range m, (X : PowerSeries ℤ) ^ t) ^ (k + 1)) =
      ∑ j ∈ range (k + 2), (-1 : ℤ) ^ j * ((k + 1).choose j : ℤ) *
        (if m * j ≤ N then ((N - m * j + k).choose k : ℤ) else 0) := by
  rw [geomPS, mul_pow, mk_one_pow_eq_mk_choose_add, sub_eq_add_neg, add_comm, add_pow,
    Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [one_pow, mul_one, neg_pow, ← pow_mul]
  have : ((-1 : PowerSeries ℤ) ^ j * X ^ (m * j) * ((k + 1).choose j : PowerSeries ℤ) *
      PowerSeries.mk fun n => ((k + n).choose k : ℤ)) =
      X ^ (m * j) * (C ((-1 : ℤ) ^ j * ((k + 1).choose j : ℤ)) *
        PowerSeries.mk fun n => ((k + n).choose k : ℤ)) := by
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [this, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_C_mul, PowerSeries.coeff_mk, Nat.add_comm k (N - m * j)]
  · simp

lemma choose_five (b : ℕ) :
    ((b.choose 5 : ℕ) : ℚ) = b * (b - 1) * (b - 2) * (b - 3) * (b - 4) / 120 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose b 5
  have h2 := descPochhammer_eval_eq_descFactorial ℚ b 5
  rw [h, Nat.cast_mul] at h2
  simp [descPochhammer_succ_right, Nat.factorial] at h2
  linear_combination -h2 / 120

/-- shift labels from -n..n to 0..2n -/
lemma shift_card (k n : ℕ) :
    #{f ∈ Fintype.piFinset (fun _ : Fin k => Icc (-(n : ℤ)) n) | ∑ i, f i = 0} =
      #{f ∈ Fintype.piFinset (fun _ : Fin k => range (2 * n + 1)) | ∑ i, f i = k * n} := by
  refine Finset.card_nbij' (fun f i => (f i + n).toNat) (fun g i => (g i : ℤ) - n) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [coe_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq] at hf
    simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq]
    refine ⟨fun i => by have := hf.1 i; omega, ?_⟩
    have h2 : ((∑ i, (f i + n).toNat : ℕ) : ℤ) = k * n := by
      push_cast
      rw [Finset.sum_congr rfl (fun i _ => Int.toNat_of_nonneg (by have := hf.1 i; omega))]
      rw [Finset.sum_add_distrib, hf.2]; simp
    exact_mod_cast h2
  · intro g hg
    simp only [coe_filter, Fintype.mem_piFinset, mem_range, Set.mem_ofPred_eq] at hg
    simp only [coe_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq]
    refine ⟨fun i => by have := hg.1 i; omega, ?_⟩
    rw [Finset.sum_sub_distrib]
    have : ((∑ i, g i : ℕ) : ℤ) = k * n := by exact_mod_cast hg.2
    push_cast at this
    rw [this]; simp
  · intro f hf
    simp only [coe_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq] at hf
    funext i; have := hf.1 i; simp only; omega
  · intro g hg
    funext i; simp

lemma card_sub (n : ℕ) (P : (Fin 6 → ℤ) → Prop) [DecidablePred P] :
    Nat.card {f : L n // P f.1} =
      #{f ∈ Fintype.piFinset (fun _ : Fin 6 => Icc (-(n : ℤ)) n) | ∑ i, f i = 0 ∧ P f} := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
    (Equiv.subtypeEquivRight fun f => ?_))
  simp [Fintype.mem_piFinset, and_assoc]


lemma T6 (n : ℕ) (hn : 1 ≤ n) :
    ((#{f ∈ Fintype.piFinset (fun _ : Fin 6 => Icc (-(n : ℤ)) n) | ∑ i, f i = 0} : ℕ) : ℚ) =
      ((6 * n + 5).choose 5 : ℚ) - 6 * ((4 * n + 4).choose 5 : ℚ) +
        15 * ((2 * n + 3).choose 5 : ℚ) := by
  have h := card_eq_coeff 6 (2 * n + 1) (6 * n)
  rw [coeff_geom_pow 5] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h
  rw [show 6 * n - (2 * n + 1) * 0 + 5 = 6 * n + 5 by omega,
    show 6 * n - (2 * n + 1) * 1 + 5 = 4 * n + 4 by omega,
    show 6 * n - (2 * n + 1) * 2 + 5 = 2 * n + 3 by omega] at h
  rw [shift_card]
  have h' : ((#{f ∈ Fintype.piFinset (fun _ : Fin 6 => range (2 * n + 1)) | ∑ i, f i = 6 * n} : ℕ) : ℚ)
      = (((#{f ∈ Fintype.piFinset (fun _ : Fin 6 => range (2 * n + 1)) | ∑ i, f i = 6 * n} : ℕ) : ℤ) : ℚ) := by
    push_cast; rfl
  rw [h', h]
  simp only [show (5+1).choose 0 = 1 from rfl, show (5+1).choose 1 = 6 from rfl,
    show (5+1).choose 2 = 15 from rfl]
  push_cast
  ring

lemma T3 (n : ℕ) (hn : 1 ≤ n) :
    ((#{f ∈ Fintype.piFinset (fun _ : Fin 3 => Icc (-(n : ℤ)) n) | ∑ i, f i = 0} : ℕ) : ℚ) =
      3 * n ^ 2 + 3 * n + 1 := by
  have h := card_eq_coeff 3 (2 * n + 1) (3 * n)
  rw [coeff_geom_pow 2] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega)] at h
  rw [show 3 * n - (2 * n + 1) * 0 + 2 = 3 * n + 2 by omega,
    show 3 * n - (2 * n + 1) * 1 + 2 = n + 1 by omega] at h
  rw [shift_card]
  have h' : ((#{f ∈ Fintype.piFinset (fun _ : Fin 3 => range (2 * n + 1)) | ∑ i, f i = 3 * n} : ℕ) : ℚ)
      = (((#{f ∈ Fintype.piFinset (fun _ : Fin 3 => range (2 * n + 1)) | ∑ i, f i = 3 * n} : ℕ) : ℤ) : ℚ) := by
    push_cast; rfl
  rw [h', h]
  simp only [show (2+1).choose 0 = 1 from rfl, show (2+1).choose 1 = 3 from rfl]
  push_cast
  rw [Nat.cast_choose_two, Nat.cast_choose_two]
  push_cast
  ring


noncomputable abbrev S6 (n : ℕ) : Finset (Fin 6 → ℤ) := Fintype.piFinset (fun _ : Fin 6 => Icc (-(n : ℤ)) n)

lemma Lext {n : ℕ} (f g : L n) : f = g ↔ ∀ i, f.1 i = g.1 i :=
  ⟨fun h i => h ▸ rfl, fun h => Subtype.ext (funext h)⟩

noncomputable def act (n : ℕ) (r : Fin 6) (f : L n) : L n :=
  ⟨fun i => f.1 (i + r), fun i => f.2.1 (i + r), by
    have := Equiv.sum_comp (Equiv.addRight r) f.1
    simp only [Equiv.coe_addRight] at this
    rw [this]; exact f.2.2⟩

noncomputable instance instAct (n : ℕ) : AddAction (Fin 6) (L n) where
  vadd := act n
  zero_vadd f := (Lext _ _).2 fun i => by
    show f.1 (i + 0) = f.1 i
    rw [add_zero]
  add_vadd r s f := (Lext _ _).2 fun i => by
    show f.1 (i + (r + s)) = f.1 (i + r + s)
    rw [add_assoc]

lemma vadd_val (n : ℕ) (r : Fin 6) (f : L n) (i : Fin 6) : (r +ᵥ f).1 i = f.1 (i + r) := rfl

lemma a_eq (n : ℕ) : a n = Nat.card (AddAction.orbitRel.Quotient (Fin 6) (L n)) := by
  unfold a
  refine Nat.card_congr (Quot.congrRight fun f g => ?_)
  show SameNecklace n f g ↔ f ∈ AddAction.orbit (Fin 6) g
  rw [AddAction.mem_orbit_iff]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨-r, (Lext _ _).2 fun i => by rw [vadd_val, hr]; simp⟩
  · rintro ⟨r, hr⟩
    refine ⟨-r, fun i => ?_⟩
    rw [← hr, vadd_val]; simp

noncomputable instance instFin (n : ℕ) : Fintype (L n) := by
  unfold L
  exact Fintype.subtype ((S6 n).filter fun f => ∑ i, f i = 0)
    (by intro f; simp [Fintype.mem_piFinset])

lemma fix_card (n : ℕ) (g : Fin 6) :
    Nat.card (AddAction.fixedBy (L n) g) = #{f ∈ S6 n | ∑ i, f i = 0 ∧ ∀ i, f (i + g) = f i} := by
  rw [← card_sub]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
  rw [AddAction.mem_fixedBy, Lext]
  rfl

lemma burnside (n : ℕ) :
    ∑ g : Fin 6, Nat.card (AddAction.fixedBy (L n) g) = a n * 6 := by
  classical
  have := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup (Fin 6) (L n)
  simp only [← Nat.card_eq_fintype_card] at this
  rw [this, a_eq, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin]

lemma fix0 (n : ℕ) : #{f ∈ S6 n | ∑ i, f i = 0 ∧ ∀ i, f (i + 0) = f i} =
    #{f ∈ Fintype.piFinset (fun _ : Fin 6 => Icc (-(n : ℤ)) n) | ∑ i, f i = 0} := by
  congr 1; ext f; simp

lemma fix1 (n : ℕ) : #{f ∈ S6 n | ∑ i, f i = 0 ∧ ∀ i, f (i + 1) = f i} = 1 := by
  rw [Finset.card_eq_one]; refine ⟨0, ?_⟩
  ext f
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨-, hs, h⟩
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
    simp [Fin.sum_univ_six] at hs h0 h1 h2 h3 h4
    funext i; fin_cases i <;> simp <;> omega
  · rintro rfl; simp [Fintype.mem_piFinset]

lemma fix5 (n : ℕ) : #{f ∈ S6 n | ∑ i, f i = 0 ∧ ∀ i, f (i + 5) = f i} = 1 := by
  rw [Finset.card_eq_one]; refine ⟨0, ?_⟩
  ext f
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨-, hs, h⟩
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
    simp [Fin.sum_univ_six] at hs h0 h1 h2 h3 h4
    funext i; fin_cases i <;> simp <;> omega
  · rintro rfl; simp [Fintype.mem_piFinset]


lemma fix2 (n : ℕ) : #{f ∈ S6 n | ∑ i, f i = 0 ∧ ∀ i, f (i + 2) = f i} = 2 * n + 1 := by
  have : #(Icc (-(n : ℤ)) n) = 2 * n + 1 := by rw [Int.card_Icc]; omega
  rw [← this]
  refine Finset.card_nbij' (fun f => f 0) (fun a => ![a, -a, a, -a, a, -a]) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [coe_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq] at hf
    simpa using hf.1 0
  · intro x hx
    simp only [coe_Icc, Set.mem_Icc] at hx
    simp only [coe_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq]
    refine ⟨fun i => ?_, ?_, fun i => ?_⟩
    · fin_cases i <;> simp <;> omega
    · simp [Fin.sum_univ_six]
    · fin_cases i <;> simp
  · intro f hf
    simp only [coe_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq] at hf
    obtain ⟨-, hs, h⟩ := hf
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
    simp [Fin.sum_univ_six] at hs h0 h1 h2 h3 h4
    funext i; fin_cases i <;> simp <;> omega
  · intro x hx; simp

lemma fix4 (n : ℕ) : #{f ∈ S6 n | ∑ i, f i = 0 ∧ ∀ i, f (i + 4) = f i} = 2 * n + 1 := by
  have : #(Icc (-(n : ℤ)) n) = 2 * n + 1 := by rw [Int.card_Icc]; omega
  rw [← this]
  refine Finset.card_nbij' (fun f => f 0) (fun a => ![a, -a, a, -a, a, -a]) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [coe_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq] at hf
    simpa using hf.1 0
  · intro x hx
    simp only [coe_Icc, Set.mem_Icc] at hx
    simp only [coe_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq]
    refine ⟨fun i => ?_, ?_, fun i => ?_⟩
    · fin_cases i <;> simp <;> omega
    · simp [Fin.sum_univ_six]
    · fin_cases i <;> simp
  · intro f hf
    simp only [coe_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq] at hf
    obtain ⟨-, hs, h⟩ := hf
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
    have h5 := h 5
    simp [Fin.sum_univ_six] at hs h0 h1 h2 h3 h4 h5
    funext i; fin_cases i <;> simp <;> omega
  · intro x hx; simp

lemma fix3 (n : ℕ) : #{f ∈ S6 n | ∑ i, f i = 0 ∧ ∀ i, f (i + 3) = f i} =
    #{f ∈ Fintype.piFinset (fun _ : Fin 3 => Icc (-(n : ℤ)) n) | ∑ i, f i = 0} := by
  refine Finset.card_nbij' (fun f => ![f 0, f 1, f 2]) (fun x => ![x 0, x 1, x 2, x 0, x 1, x 2])
    ?_ ?_ ?_ ?_
  · intro f hf
    simp only [coe_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq] at hf ⊢
    obtain ⟨hb, hs, h⟩ := hf
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    simp [Fin.sum_univ_six] at hs h0 h1 h2
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [hb]
    · simp [Fin.sum_univ_three]; omega
  · intro x hx
    simp only [coe_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨hb, hs⟩ := hx
    simp [Fin.sum_univ_three] at hs
    refine ⟨fun i => ?_, ?_, fun i => ?_⟩
    · fin_cases i <;> simp [hb]
    · simp [Fin.sum_univ_six]; omega
    · fin_cases i <;> simp
  · intro f hf
    simp only [coe_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq] at hf
    obtain ⟨-, hs, h⟩ := hf
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    simp at h0 h1 h2
    funext i; fin_cases i <;> simp <;> omega
  · intro x hx
    funext i; fin_cases i <;> simp

lemma a_formula (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (((6 * n + 5).choose 5 : ℚ) - 6 * ((4 * n + 4).choose 5 : ℚ) +
        15 * ((2 * n + 3).choose 5 : ℚ) + (3 * n ^ 2 + 3 * n + 1) + 4 * n + 4) / 6 := by
  have hb := burnside n
  rw [Fin.sum_univ_six] at hb
  simp only [fix_card] at hb
  rw [fix0, fix1, fix2, fix3, fix4, fix5] at hb
  have hq : ((a n * 6 : ℕ) : ℚ) = _ := congrArg (fun x : ℕ => (x : ℚ)) hb.symm
  push_cast at hq
  rw [T6 n hn, T3 n hn] at hq
  linear_combination hq / 6


noncomputable def P (x : ℚ) : ℚ :=
  ((6 * x + 5) * (6 * x + 4) * (6 * x + 3) * (6 * x + 2) * (6 * x + 1) / 120 -
    6 * ((4 * x + 4) * (4 * x + 3) * (4 * x + 2) * (4 * x + 1) * (4 * x) / 120) +
    15 * ((2 * x + 3) * (2 * x + 2) * (2 * x + 1) * (2 * x) * (2 * x - 1) / 120) +
    (3 * x ^ 2 + 3 * x + 1) + 4 * x + 4) / 6

lemma aP (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = P n := by
  rw [a_formula n hn, choose_five, choose_five, choose_five, P]
  push_cast
  ring

lemma coeff_mk_mul_X_pow (f : ℕ → ℚ) (j k : ℕ) :
    coeff k (PowerSeries.mk f * X ^ j) = if j ≤ k then f (k - j) else 0 := by
  rw [coeff_mul_X_pow', PowerSeries.coeff_mk]

end OMA.Helpers_a208600

open OMA.Helpers_a208600 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a208600.main := by
  refine ⟨?_, ?_⟩
  · set f : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a208600.a n : ℚ) with hf
    have e : PowerSeries.mk f * (1 - X) ^ 6 = PowerSeries.mk f * X ^ 0 - C 6 * (PowerSeries.mk f * X ^ 1) +
        C 15 * (PowerSeries.mk f * X ^ 2) - C 20 * (PowerSeries.mk f * X ^ 3) +
        C 15 * (PowerSeries.mk f * X ^ 4) - C 6 * (PowerSeries.mk f * X ^ 5) +
        PowerSeries.mk f * X ^ 6 := by
      simp only [map_ofNat]; ring
    have e2 : (X : PowerSeries ℚ) * (26 + 141 * X + 172 * X ^ 2 + 8 * X ^ 3 + 6 * X ^ 4 - X ^ 5) =
        C 26 * X ^ 1 + C 141 * X ^ 2 + C 172 * X ^ 3 + C 8 * X ^ 4 + C 6 * X ^ 5 - X ^ 6 := by
      simp only [map_ofNat]; ring
    rw [e, e2]
    ext k
    simp only [map_sub, map_add, coeff_C_mul, coeff_mk_mul_X_pow, coeff_X_pow]
    by_cases hk : k ≤ 6
    · interval_cases k <;> simp [hf, aP, P] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 7 := ⟨k - 7, by omega⟩
      simp only [show 0 ≤ m + 7 by omega, show 1 ≤ m + 7 by omega, show 2 ≤ m + 7 by omega,
        show 3 ≤ m + 7 by omega, show 4 ≤ m + 7 by omega, show 5 ≤ m + 7 by omega,
        show 6 ≤ m + 7 by omega, if_true, show m + 7 - 0 = m + 7 from rfl,
        show m + 7 - 1 = m + 6 from rfl, show m + 7 - 2 = m + 5 from rfl,
        show m + 7 - 3 = m + 4 from rfl, show m + 7 - 4 = m + 3 from rfl,
        show m + 7 - 5 = m + 2 from rfl, show m + 7 - 6 = m + 1 from rfl, hf]
      simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, one_ne_zero, and_false, if_false,
        show m + 7 ≠ 1 by omega, show m + 7 ≠ 2 by omega, show m + 7 ≠ 3 by omega,
        show m + 7 ≠ 4 by omega, show m + 7 ≠ 5 by omega, show m + 7 ≠ 6 by omega]
      rw [aP _ (by omega), aP _ (by omega), aP _ (by omega), aP _ (by omega), aP _ (by omega),
        aP _ (by omega), aP _ (by omega)]
      simp only [P]; push_cast; ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    simp only [show m + 7 - 1 = m + 6 from rfl, show m + 7 - 2 = m + 5 from rfl,
      show m + 7 - 3 = m + 4 from rfl, show m + 7 - 4 = m + 3 from rfl,
      show m + 7 - 5 = m + 2 from rfl, show m + 7 - 6 = m + 1 from rfl]
    have key : (((OMA.S_oeis_a208600.a (m + 7) : ℤ)) : ℚ) =
        ((6 * OMA.S_oeis_a208600.a (m + 6) - 15 * OMA.S_oeis_a208600.a (m + 5) +
          20 * OMA.S_oeis_a208600.a (m + 4) - 15 * OMA.S_oeis_a208600.a (m + 3) +
          6 * OMA.S_oeis_a208600.a (m + 2) - OMA.S_oeis_a208600.a (m + 1) : ℤ) : ℚ) := by
      push_cast
      rw [aP _ (by omega), aP _ (by omega), aP _ (by omega), aP _ (by omega), aP _ (by omega),
        aP _ (by omega), aP _ (by omega)]
      simp only [P]; push_cast; ring
    exact_mod_cast key
