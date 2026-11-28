import OMAStatements.S_oeis_a008590

-- Problem: A008590: Multiples of 8.
-- Upstream: formal-conjectures statements/oeis-a008590.lean:0 (declaration OMA.S_oeis_a008590.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: gcd(m-k, m) = gcd(k, m), so the terms k and m-k of each sum are equal and cancel mod 2;
-- only the terms k = m and k = m/2 remain. With minFac and the largest proper divisor of m and m/2
-- the parity follows in four cases (m odd, m = 2, m = 2j with j odd, m = 4i).

open OMA.S_oeis_a008590 in
theorem OMA.solution : type_of% @OMA.S_oeis_a008590.main := by
  have key : ∀ (f : ℕ → ℕ) (m : ℕ),
      (Even (∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1), f (Nat.gcd k m)) ↔
        Even (∑ k ∈ ((Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1)).filter
          (fun k => k = m ∨ 2 * k = m), f (Nat.gcd k m))) := by
    intro f m
    rw [← ZMod.natCast_eq_zero_iff_even, ← ZMod.natCast_eq_zero_iff_even,
      ← Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1))
        (fun k => k = m ∨ 2 * k = m), Nat.cast_add]
    have hz : ((∑ k ∈ ((Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1)).filter
        (fun k => ¬(k = m ∨ 2 * k = m)), f (Nat.gcd k m) : ℕ) : ZMod 2) = 0 := by
      rw [Nat.cast_sum]
      refine Finset.sum_involution (fun a _ => m - a) ?_ ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_Icc] at ha
        show (f (Nat.gcd a m) : ZMod 2) + (f (Nat.gcd (m - a) m) : ZMod 2) = 0
        rw [Nat.gcd_self_sub_left (by omega : a ≤ m), ← Nat.cast_add,
          ZMod.natCast_eq_zero_iff_even]
        exact ⟨f (Nat.gcd a m), rfl⟩
      · intro a ha _
        simp only [Finset.mem_filter, Finset.mem_Icc] at ha
        show m - a ≠ a
        omega
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_Icc] at ha
        show m - a ∈ _
        simp only [Finset.mem_filter, Finset.mem_Icc]
        rw [Nat.gcd_self_sub_left (by omega : a ≤ m)]
        omega
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_Icc] at ha
        show m - (m - a) = a
        omega
    rw [hz, add_zero]
  have hT1 : ∀ m : ℕ, m % 2 = 1 → 2 ≤ m →
      ((Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1)).filter
        (fun k => k = m ∨ 2 * k = m) = {m} := by
    intro m hm hm2
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · intro h
      omega
    · intro h
      rw [h, Nat.gcd_self]
      omega
  have hT2 : ∀ j : ℕ, 2 ≤ j →
      ((Finset.Icc 1 (2 * j)).filter (fun k => Nat.gcd k (2 * j) ≠ 1)).filter
        (fun k => k = 2 * j ∨ 2 * k = 2 * j) = {j, 2 * j} := by
    intro j hj
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      omega
    · intro h
      rcases h with h | h
      · rw [h, Nat.gcd_mul_left_right]
        omega
      · rw [h, Nat.gcd_self]
        omega
  have hT3 : ((Finset.Icc 1 2).filter (fun k => Nat.gcd k 2 ≠ 1)).filter
      (fun k => k = 2 ∨ 2 * k = 2) = {2} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · intro h
      rcases h with ⟨⟨hk, hg⟩, h | h⟩
      · exact h
      · have hk1 : k = 1 := by omega
        rw [hk1] at hg
        exact absurd (Nat.gcd_one_left 2) hg
    · intro h
      rw [h, Nat.gcd_self]
      omega
  have hodd : ∀ (f : ℕ → ℕ) (m : ℕ), m % 2 = 1 → 2 ≤ m →
      (Even (∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1), f (Nat.gcd k m)) ↔
        Even (f m)) := by
    intro f m hm hm2
    rw [key f m, hT1 m hm hm2, Finset.sum_singleton, Nat.gcd_self]
  have heven : ∀ (f : ℕ → ℕ) (j : ℕ), 2 ≤ j →
      (Even (∑ k ∈ (Finset.Icc 1 (2 * j)).filter (fun k => Nat.gcd k (2 * j) ≠ 1),
          f (Nat.gcd k (2 * j))) ↔ Even (f j + f (2 * j))) := by
    intro f j hj
    rw [key f (2 * j), hT2 j hj, Finset.sum_pair (by omega : j ≠ 2 * j),
      Nat.gcd_mul_left_right, Nat.gcd_self]
  have htwo : ∀ (f : ℕ → ℕ),
      (Even (∑ k ∈ (Finset.Icc 1 2).filter (fun k => Nat.gcd k 2 ≠ 1), f (Nat.gcd k 2)) ↔
        Even (f 2)) := by
    intro f
    rw [key f 2, hT3, Finset.sum_singleton, Nat.gcd_self]
  have hf1 : ∀ n i : ℕ, n = 2 * i → 1 ≤ i → (Nat.properDivisors n).sup id = i := by
    intro n i hn hi
    apply le_antisymm
    · apply Finset.sup_le
      intro d hd
      rw [Nat.mem_properDivisors] at hd
      obtain ⟨⟨e, he⟩, hlt⟩ := hd
      have he2 : 2 ≤ e := by
        rcases Nat.lt_or_ge e 2 with h | h
        · interval_cases e
          · rw [Nat.mul_zero] at he
            omega
          · rw [Nat.mul_one] at he
            omega
        · exact h
      have hde : d * 2 ≤ d * e := Nat.mul_le_mul (le_refl d) he2
      show d ≤ i
      omega
    · apply Finset.le_sup (f := id)
      rw [Nat.mem_properDivisors]
      exact ⟨⟨2, by omega⟩, by omega⟩
  have hmin2 : ∀ n : ℕ, 2 ∣ n → Nat.minFac n = 2 := fun n h => (Nat.minFac_eq_two_iff n).mpr h
  have hminodd : ∀ n : ℕ, n % 2 = 1 → ¬ Even (Nat.minFac n) := by
    intro n hn he
    have h2 : 2 ∣ Nat.minFac n := even_iff_two_dvd.mp he
    have h3 : 2 ∣ n := dvd_trans h2 (Nat.minFac_dvd n)
    omega
  intro m hm
  rcases Nat.even_or_odd' m with ⟨j, hj | hj⟩
  · by_cases hj1 : j = 1
    · have hm2 : m = 2 := by omega
      subst hm2
      have h1 : Even (S1 2) ↔ Even ((Nat.properDivisors 2).sup id) :=
        htwo (fun g => (Nat.properDivisors g).sup id)
      rw [h1, hf1 2 1 rfl le_rfl]
      constructor
      · rintro ⟨h, -⟩
        exact absurd h Nat.not_even_one
      · intro h
        omega
    · have hj2 : 2 ≤ j := by omega
      subst hj
      have h1 : Even (S1 (2 * j)) ↔
          Even ((Nat.properDivisors j).sup id + (Nat.properDivisors (2 * j)).sup id) :=
        heven (fun g => (Nat.properDivisors g).sup id) j hj2
      have h2 : Even (S2 (2 * j)) ↔ Even (Nat.minFac j + Nat.minFac (2 * j)) :=
        heven (fun g => Nat.minFac g) j hj2
      rw [h1, h2, hmin2 (2 * j) (dvd_mul_right 2 j), hf1 (2 * j) j rfl (by omega)]
      rcases Nat.even_or_odd' j with ⟨i, hi | hi⟩
      · subst hi
        rw [hmin2 (2 * i) (dvd_mul_right 2 i), hf1 (2 * i) i rfl (by omega)]
        constructor
        · rintro ⟨⟨r, hr⟩, -⟩
          omega
        · intro h
          obtain ⟨c, hc⟩ := h
          exact ⟨⟨3 * c, by omega⟩, ⟨2, rfl⟩⟩
      · subst hi
        have hno := hminodd (2 * i + 1) (by omega)
        constructor
        · rintro ⟨-, h⟩
          rw [Nat.even_add] at h
          exact absurd (h.mpr ⟨1, rfl⟩) hno
        · intro h
          omega
  · have hmod : m % 2 = 1 := by omega
    have h2 : Even (S2 m) ↔ Even (Nat.minFac m) := hodd (fun g => Nat.minFac g) m hmod hm
    rw [h2]
    constructor
    · rintro ⟨-, h⟩
      exact absurd h (hminodd m hmod)
    · intro h
      omega
