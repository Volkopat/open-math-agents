import OMAStatements.S_oeis_a175368

-- Problem: A175368: Number of integer 4-tuples (x,y,z,u) satisfying |x|^3 + |y|^3 + |z|^3 + |u|^3 = n, -n <= x,y,z,u <= n.
-- Upstream: formal-conjectures statements/oeis-a175368.lean:0 (declaration OMA.S_oeis_a175368.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let theta = 1 + 2 Sum_{j>=1} x^(j^3) and Q_N = Sum_{x in [-N, N]} X^(|x|^3) (a finite sum).
-- For m <= N the x^m coefficient of both is #{x in [-N, N] : |x|^3 = m} (1 for m = 0, 2 for a positive
-- cube, 0 otherwise), so theta^4 and Q_N^4 agree up to x^N. Q_N^4 is the sum of X^(|x|^3+|y|^3+|z|^3+|u|^3)
-- over the box [-N, N]^4, whose x^N coefficient is the number of tuples with that sum equal to N.

namespace P1A175368

open OMA.S_oeis_a175368

/-- The exponent of a 4-tuple. -/
def ee (p : ℤ × ℤ × ℤ × ℤ) : ℕ :=
  p.1.natAbs ^ 3 + (p.2.1.natAbs ^ 3 + (p.2.2.1.natAbs ^ 3 + p.2.2.2.natAbs ^ 3))

theorem coefsum {α : Type*} (s : Finset α) (e : α → ℕ) (n : ℕ) :
    PowerSeries.coeff n (∑ p ∈ s, (PowerSeries.X : PowerSeries ℚ) ^ (e p)) =
      ((s.filter (fun p => n = e p)).card : ℚ) := by
  rw [map_sum]
  simp only [PowerSeries.coeff_X_pow]
  rw [Finset.sum_boole]

theorem ps {α β : Type*} (s : Finset α) (t : Finset β) (f : α → ℕ) (g : β → ℕ) :
    (∑ x ∈ s, (PowerSeries.X : PowerSeries ℚ) ^ (f x)) *
        (∑ y ∈ t, (PowerSeries.X : PowerSeries ℚ) ^ (g y)) =
      ∑ q ∈ s ×ˢ t, (PowerSeries.X : PowerSeries ℚ) ^ (f q.1 + g q.2) := by
  rw [Finset.sum_mul_sum, Finset.sum_product]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => (pow_add _ _ _).symm))

theorem Q4 (N : ℕ) :
    (∑ x ∈ Finset.Icc (-(N : ℤ)) N, (PowerSeries.X : PowerSeries ℚ) ^ (x.natAbs ^ 3)) ^ 4 =
      ∑ p ∈ Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N ×ˢ
        Finset.Icc (-(N : ℤ)) N, (PowerSeries.X : PowerSeries ℚ) ^ (ee p) := by
  rw [show ∀ q : PowerSeries ℚ, q ^ 4 = q * (q * (q * q)) from fun q => by ring,
    ps (Finset.Icc (-(N : ℤ)) N) (Finset.Icc (-(N : ℤ)) N) (fun x => x.natAbs ^ 3)
      (fun x => x.natAbs ^ 3),
    ps (Finset.Icc (-(N : ℤ)) N) (Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N)
      (fun x => x.natAbs ^ 3) (fun q => q.1.natAbs ^ 3 + q.2.natAbs ^ 3),
    ps (Finset.Icc (-(N : ℤ)) N)
      (Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N)
      (fun x => x.natAbs ^ 3) (fun q => q.1.natAbs ^ 3 + (q.2.1.natAbs ^ 3 + q.2.2.natAbs ^ 3))]
  rfl

theorem trunc (f g : PowerSeries ℚ) (N : ℕ)
    (h : ∀ m, m ≤ N → PowerSeries.coeff m f = PowerSeries.coeff m g) :
    ∀ k m, m ≤ N → PowerSeries.coeff m (f ^ k) = PowerSeries.coeff m (g ^ k) := by
  intro k
  induction k with
  | zero =>
    intro m _
    rw [pow_zero, pow_zero]
  | succ k ih =>
    intro m hm
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [ih p.1 (by omega), h p.2 (by omega)]

theorem thcoef (m : ℕ) :
    PowerSeries.coeff m (1 + 2 * PowerSeries.mk
      (fun m => (((Finset.Icc 1 m).filter (fun j => j ^ 3 = m)).card : ℚ))) =
      (if m = 0 then 1 else 0) + 2 * (((Finset.Icc 1 m).filter (fun j => j ^ 3 = m)).card : ℚ) := by
  rw [show (2 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 from
      (map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2).symm,
    map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]

theorem tcount (N m : ℕ) (hm : m ≤ N) :
    (((Finset.Icc (-(N : ℤ)) N).filter (fun x => m = x.natAbs ^ 3)).card : ℚ) =
      (if m = 0 then 1 else 0) + 2 * (((Finset.Icc 1 m).filter (fun j => j ^ 3 = m)).card : ℚ) := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have hS : (Finset.Icc (-(N : ℤ)) N).filter (fun x => 0 = x.natAbs ^ 3) = {0} := by
      ext x
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩
        have h1 : x.natAbs = 0 := (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h.symm
        exact Int.natAbs_eq_zero.mp h1
      · rintro rfl
        exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by norm_num⟩
    have hC : (Finset.Icc 1 0).filter (fun j => j ^ 3 = 0) = ∅ := by
      rw [Finset.Icc_eq_empty (show ¬ (1 ≤ 0) by omega), Finset.filter_empty]
    rw [hS, hC, Finset.card_singleton, Finset.card_empty, if_pos rfl]
    norm_num
  · by_cases hc : ∃ j, j ^ 3 = m
    · obtain ⟨j, hj⟩ := hc
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hj
        omega
      have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      have hjle : j ≤ m := by
        calc j ≤ j ^ 3 := le_self_pow hj1 (by norm_num : (3 : ℕ) ≠ 0)
          _ = m := hj
      have hS : (Finset.Icc (-(N : ℤ)) N).filter (fun x => m = x.natAbs ^ 3) =
          {(j : ℤ), -(j : ℤ)} := by
        ext x
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨-, h⟩
          have hx : x.natAbs = j :=
            Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0) (h.symm.trans hj.symm)
          rcases Int.natAbs_eq x with h1 | h1
          · rw [hx] at h1
            exact Or.inl h1
          · rw [hx] at h1
            exact Or.inr h1
        · rintro (rfl | rfl)
          · exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp [hj]⟩
          · exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp [hj]⟩
      have hC : (Finset.Icc 1 m).filter (fun i => i ^ 3 = m) = {j} := by
        ext i
        rw [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨-, h⟩
          exact Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0) (h.trans hj.symm)
        · rintro rfl
          exact ⟨Finset.mem_Icc.mpr ⟨hj1, hjle⟩, hj⟩
      have hne : (j : ℤ) ≠ -(j : ℤ) := by omega
      rw [hS, hC, Finset.card_pair hne, Finset.card_singleton,
        if_neg (show ¬ (m = 0) by omega)]
      norm_num
    · have hS : (Finset.Icc (-(N : ℤ)) N).filter (fun x => m = x.natAbs ^ 3) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x _ h
        exact hc ⟨x.natAbs, h.symm⟩
      have hC : (Finset.Icc 1 m).filter (fun i => i ^ 3 = m) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro i _ h
        exact hc ⟨i, h⟩
      rw [hS, hC, Finset.card_empty, if_neg (show ¬ (m = 0) by omega)]
      norm_num

theorem iffe (p : ℤ × ℤ × ℤ × ℤ) (n : ℕ) :
    |p.1| ^ 3 + |p.2.1| ^ 3 + |p.2.2.1| ^ 3 + |p.2.2.2| ^ 3 = (n : ℤ) ↔ n = ee p := by
  have hcast : ((ee p : ℕ) : ℤ) = |p.1| ^ 3 + |p.2.1| ^ 3 + |p.2.2.1| ^ 3 + |p.2.2.2| ^ 3 := by
    simp only [ee, Nat.cast_add, Nat.cast_pow, Int.natCast_natAbs]
    ring
  constructor
  · intro h
    have h2 : ((ee p : ℕ) : ℤ) = ((n : ℕ) : ℤ) := hcast.trans h
    exact_mod_cast h2.symm
  · intro h
    rw [← hcast, ← h]

end P1A175368

open OMA.S_oeis_a175368 P1A175368 in
theorem OMA.solution : type_of% @OMA.S_oeis_a175368.main := by
  ext n
  have hθ : ∀ m, m ≤ n → PowerSeries.coeff m (1 + 2 * PowerSeries.mk
      (fun m => (((Finset.Icc 1 m).filter (fun j => j ^ 3 = m)).card : ℚ))) =
      PowerSeries.coeff m (∑ x ∈ Finset.Icc (-(n : ℤ)) n,
        (PowerSeries.X : PowerSeries ℚ) ^ (x.natAbs ^ 3)) := by
    intro m hm
    rw [coefsum, thcoef m, tcount n m hm]
  rw [trunc _ _ n hθ 4 n le_rfl, Q4, coefsum, PowerSeries.coeff_mk]
  have hf : (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ
      Finset.Icc (-(n : ℤ)) n).filter (fun p : ℤ × ℤ × ℤ × ℤ =>
        |p.1| ^ 3 + |p.2.1| ^ 3 + |p.2.2.1| ^ 3 + |p.2.2.2| ^ 3 = (n : ℤ)) =
      (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ
        Finset.Icc (-(n : ℤ)) n).filter (fun p => n = ee p) :=
    Finset.filter_congr (fun p _ => iffe p n)
  rw [← hf]
  rfl
