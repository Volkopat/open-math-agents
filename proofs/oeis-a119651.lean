import OMAStatements.S_oeis_a119651

-- Problem: A119651: Number of different values of exactly n standard American coins (pennies, nickels, dimes and quarters).
-- Upstream: formal-conjectures statements/oeis-a119651.lean:0 (declaration OMA.S_oeis_a119651.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: n coins with k nickels, d dimes and q quarters are worth n + 4k + 9d + 24q cents,
-- so a(n) is the size of V(n) = {4j + 9k + 24l : j + k + l ≤ n}. For n ≥ 8 the new values
-- V(n+1) minus V(n) are exactly the new values V(n) minus V(n-1) shifted by 24 (trade four 9s
-- for three 4s and a 24, or six 4s for one 24, or remove a 24), so the differences of a are
-- constant from a(8) - a(7) = 24 on. The small values come from a kernel computation; the g.f.
-- follows by comparing coefficients.

/-- The values 4j + 9k + 24l with j + k + l ≤ n. -/
def kV119651 (n : ℕ) : Finset ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 ≤ n)).image
    (fun t : ℕ × ℕ × ℕ => 4 * t.1 + 9 * t.2.1 + 24 * t.2.2)

theorem kmem119651 (n v : ℕ) :
    v ∈ kV119651 n ↔ ∃ j k l : ℕ, j + k + l ≤ n ∧ 4 * j + 9 * k + 24 * l = v := by
  unfold kV119651
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨j, k, l⟩, ht, e⟩
    exact ⟨j, k, l, (Finset.mem_filter.1 ht).2, e⟩
  · rintro ⟨j, k, l, h, e⟩
    exact ⟨(j, k, l), Finset.mem_filter.2 ⟨Finset.mem_product.2
      ⟨Finset.mem_range.2 (show j < n + 1 by omega), Finset.mem_product.2
        ⟨Finset.mem_range.2 (show k < n + 1 by omega),
          Finset.mem_range.2 (show l < n + 1 by omega)⟩⟩, h⟩, e⟩

theorem kmono119651 (i : ℕ) : kV119651 i ⊆ kV119651 (i + 1) := by
  intro v hv
  obtain ⟨j, k, l, h, e⟩ := (kmem119651 _ _).1 hv
  exact (kmem119651 _ _).2 ⟨j, k, l, by omega, e⟩

theorem kbridge119651 (n : ℕ) : OMA.S_oeis_a119651.a n = (kV119651 n).card := by
  have h : OMA.S_oeis_a119651.coinValues n = (kV119651 n).image (fun v => v + n) := by
    ext w
    unfold OMA.S_oeis_a119651.coinValues
    rw [Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨⟨p, k, d, q⟩, ht, e⟩
      have hs : p + k + d + q = n := (Finset.mem_filter.1 ht).2
      have e' : p + 5 * k + 10 * d + 25 * q = w := e
      exact ⟨4 * k + 9 * d + 24 * q, (kmem119651 n _).2 ⟨k, d, q, by omega, rfl⟩,
        show 4 * k + 9 * d + 24 * q + n = w by omega⟩
    · rintro ⟨v, hv, e⟩
      obtain ⟨j, k, l, h, e2⟩ := (kmem119651 n v).1 hv
      refine ⟨(n - j - k - l, j, k, l), Finset.mem_filter.2 ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_product.2 ⟨Finset.mem_range.2 (show n - j - k - l < n + 1 by omega),
          Finset.mem_product.2 ⟨Finset.mem_range.2 (show j < n + 1 by omega),
            Finset.mem_product.2 ⟨Finset.mem_range.2 (show k < n + 1 by omega),
              Finset.mem_range.2 (show l < n + 1 by omega)⟩⟩⟩
      · show n - j - k - l + j + k + l = n
        omega
      · show n - j - k - l + 5 * j + 10 * k + 25 * l = w
        omega
  unfold OMA.S_oeis_a119651.a
  rw [h, Finset.card_image_of_injective _ (add_left_injective n)]

theorem kshift119651 (n : ℕ) (hn : 7 ≤ n) :
    kV119651 (n + 2) \ kV119651 (n + 1) =
      (kV119651 (n + 1) \ kV119651 n).image (fun v => v + 24) := by
  ext w
  rw [Finset.mem_sdiff, Finset.mem_image]
  constructor
  · rintro ⟨hw2, hw1⟩
    obtain ⟨j, k, l, h, e⟩ := (kmem119651 _ _).1 hw2
    have key : 24 ≤ w ∧ w - 24 ∈ kV119651 (n + 1) := by
      rcases Nat.eq_zero_or_pos l with hl | hl
      · rcases le_or_gt 4 k with hk | hk
        · exact ⟨by omega, (kmem119651 (n + 1) (w - 24)).2 ⟨j + 3, k - 4, 0, by omega, by omega⟩⟩
        · rcases le_or_gt 6 j with hj | hj
          · exact absurd ((kmem119651 (n + 1) w).2 ⟨j - 6, k, 1, by omega, by omega⟩) hw1
          · exact absurd ((kmem119651 (n + 1) w).2 ⟨j, k, 0, by omega, by omega⟩) hw1
      · exact ⟨by omega, (kmem119651 (n + 1) (w - 24)).2 ⟨j, k, l - 1, by omega, by omega⟩⟩
    obtain ⟨k24, key2⟩ := key
    refine ⟨w - 24, Finset.mem_sdiff.2 ⟨key2, fun h0 => hw1 ?_⟩, by omega⟩
    obtain ⟨j', k', l', h', e'⟩ := (kmem119651 _ _).1 h0
    exact (kmem119651 _ _).2 ⟨j', k', l' + 1, by omega, by omega⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨hv1, hv0⟩ := Finset.mem_sdiff.1 hv
    obtain ⟨j, k, l, h, e⟩ := (kmem119651 _ _).1 hv1
    refine ⟨(kmem119651 _ _).2 ⟨j, k, l + 1, by omega, by omega⟩, fun h24 => hv0 ?_⟩
    obtain ⟨j', k', l', h', e'⟩ := (kmem119651 _ _).1 h24
    rcases Nat.eq_zero_or_pos l' with hl | hl
    · rcases le_or_gt 6 j' with hj | hj
      · exact (kmem119651 _ _).2 ⟨j' - 6, k', 0, by omega, by omega⟩
      · rcases le_or_gt 4 k' with hk | hk
        · exact (kmem119651 _ _).2 ⟨j' + 3, k' - 4, 0, by omega, by omega⟩
        · exact (kmem119651 _ _).2 ⟨j, k, l, by omega, e⟩
    · exact (kmem119651 _ _).2 ⟨j', k', l' - 1, by omega, by omega⟩

theorem kc119651 : (kV119651 1).card = 4 ∧ (kV119651 2).card = 10 ∧ (kV119651 3).card = 20 ∧
    (kV119651 4).card = 34 ∧ (kV119651 5).card = 52 ∧ (kV119651 6).card = 73 ∧
    (kV119651 7).card = 96 ∧ (kV119651 8).card = 120 := by
  decide +kernel

theorem kstep119651 (n : ℕ) (hn : 7 ≤ n) :
    (kV119651 (n + 1)).card = (kV119651 n).card + 24 := by
  induction n, hn using Nat.le_induction with
  | base =>
    show (kV119651 8).card = (kV119651 7).card + 24
    have h7 := kc119651.2.2.2.2.2.2.1
    have h8 := kc119651.2.2.2.2.2.2.2
    omega
  | succ m hm ih =>
    show (kV119651 (m + 2)).card = (kV119651 (m + 1)).card + 24
    have s1 : kV119651 (m + 1) ⊆ kV119651 (m + 2) := kmono119651 (m + 1)
    have s0 : kV119651 m ⊆ kV119651 (m + 1) := kmono119651 m
    have e1 := Finset.card_sdiff_add_card_eq_card s1
    have e0 := Finset.card_sdiff_add_card_eq_card s0
    rw [kshift119651 m hm, Finset.card_image_of_injective _ (add_left_injective 24)] at e1
    omega

open OMA.S_oeis_a119651 in
theorem OMA.solution : type_of% @OMA.S_oeis_a119651.main := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := kc119651
  have hclosed : ∀ n : ℕ, 7 ≤ n → a n = 24 * (n - 3) := by
    intro n hn
    rw [kbridge119651 n]
    induction n, hn using Nat.le_induction with
    | base => omega
    | succ m hm ih =>
      have hs := kstep119651 m hm
      omega
  have hrec : ∀ n : ℕ, 9 ≤ n → (a n : ℤ) = 2 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ) := by
    intro n hn
    have h1 := hclosed n (by omega)
    have h2 := hclosed (n - 1) (by omega)
    have h3 := hclosed (n - 2) (by omega)
    omega
  have q1 : (a 1 : ℚ) = 4 := by
    have h : a 1 = 4 := (kbridge119651 1).trans c1
    exact_mod_cast h
  have q2 : (a 2 : ℚ) = 10 := by
    have h : a 2 = 10 := (kbridge119651 2).trans c2
    exact_mod_cast h
  have q3 : (a 3 : ℚ) = 20 := by
    have h : a 3 = 20 := (kbridge119651 3).trans c3
    exact_mod_cast h
  have q4 : (a 4 : ℚ) = 34 := by
    have h : a 4 = 34 := (kbridge119651 4).trans c4
    exact_mod_cast h
  have q5 : (a 5 : ℚ) = 52 := by
    have h : a 5 = 52 := (kbridge119651 5).trans c5
    exact_mod_cast h
  have q6 : (a 6 : ℚ) = 73 := by
    have h : a 6 = 73 := (kbridge119651 6).trans c6
    exact_mod_cast h
  have q7 : (a 7 : ℚ) = 96 := by
    have h : a 7 = 96 := (kbridge119651 7).trans c7
    exact_mod_cast h
  have q8 : (a 8 : ℚ) = 120 := by
    have h : a 8 = 120 := (kbridge119651 8).trans c8
    exact_mod_cast h
  have e : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - PowerSeries.X) ^ 2 =
      PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
          (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * PowerSeries.X ^ 1)
        + PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * PowerSeries.X ^ 2 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    ring
  have e2 : (PowerSeries.X * (4 + 2 * PowerSeries.X + 4 * PowerSeries.X ^ 2 +
      4 * PowerSeries.X ^ 3 + 4 * PowerSeries.X ^ 4 + 3 * PowerSeries.X ^ 5 +
      2 * PowerSeries.X ^ 6 + PowerSeries.X ^ 7) : PowerSeries ℚ) =
      PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4
        + PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
        + PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4
        + PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4
        + PowerSeries.X ^ 5 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4
        + PowerSeries.X ^ 6 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3
        + PowerSeries.X ^ 7 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
        + PowerSeries.X ^ 8 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3]
    ring
  have gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - PowerSeries.X) ^ 2 =
      PowerSeries.X * (4 + 2 * PowerSeries.X + 4 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 +
        4 * PowerSeries.X ^ 4 + 3 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 6 +
        PowerSeries.X ^ 7) := by
    refine e.trans (Eq.trans ?_ e2.symm)
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C,
      PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 9 with hm | hm
    · interval_cases m
      · norm_num
      · norm_num [q1]
      · norm_num [q1, q2]
      · norm_num [q1, q2, q3]
      · norm_num [q2, q3, q4]
      · rw [if_neg (show ¬ ((5 : ℕ) = 0 : Prop) by decide), if_pos (show (1 ≤ (5 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((5 : ℕ) - 1 = 0 : Prop) by decide),
          if_pos (show (2 ≤ (5 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((5 : ℕ) - 2 = 0 : Prop) by decide),
          if_pos (show (1 ≤ (5 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((5 : ℕ) - 1 = 0 : Prop) by decide),
          if_pos (show (2 ≤ (5 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((5 : ℕ) - 2 = 0 : Prop) by decide),
          if_pos (show (3 ≤ (5 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((5 : ℕ) - 3 = 0 : Prop) by decide),
          if_pos (show (4 ≤ (5 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((5 : ℕ) - 4 = 0 : Prop) by decide),
          if_pos (show ((5 : ℕ) ≤ 5 : Prop) by decide),
          if_pos (show ((5 : ℕ) - 5 = 0 : Prop) by decide),
          if_neg (show ¬ (6 ≤ (5 : ℕ) : Prop) by decide),
          if_neg (show ¬ (7 ≤ (5 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((5 : ℕ) = 8 : Prop) by decide), show (5 : ℕ) - 1 = 4 from rfl,
          show (5 : ℕ) - 2 = 3 from rfl, q5, q4, q3]
        norm_num
      · rw [if_neg (show ¬ ((6 : ℕ) = 0 : Prop) by decide), if_pos (show (1 ≤ (6 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((6 : ℕ) - 1 = 0 : Prop) by decide),
          if_pos (show (2 ≤ (6 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((6 : ℕ) - 2 = 0 : Prop) by decide),
          if_pos (show (1 ≤ (6 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((6 : ℕ) - 1 = 0 : Prop) by decide),
          if_pos (show (2 ≤ (6 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((6 : ℕ) - 2 = 0 : Prop) by decide),
          if_pos (show (3 ≤ (6 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((6 : ℕ) - 3 = 0 : Prop) by decide),
          if_pos (show (4 ≤ (6 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((6 : ℕ) - 4 = 0 : Prop) by decide),
          if_pos (show (5 ≤ (6 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((6 : ℕ) - 5 = 0 : Prop) by decide),
          if_pos (show ((6 : ℕ) ≤ 6 : Prop) by decide),
          if_pos (show ((6 : ℕ) - 6 = 0 : Prop) by decide),
          if_neg (show ¬ (7 ≤ (6 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((6 : ℕ) = 8 : Prop) by decide), show (6 : ℕ) - 1 = 5 from rfl,
          show (6 : ℕ) - 2 = 4 from rfl, q6, q5, q4]
        norm_num
      · rw [if_neg (show ¬ ((7 : ℕ) = 0 : Prop) by decide), if_pos (show (1 ≤ (7 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((7 : ℕ) - 1 = 0 : Prop) by decide),
          if_pos (show (2 ≤ (7 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((7 : ℕ) - 2 = 0 : Prop) by decide),
          if_pos (show (1 ≤ (7 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((7 : ℕ) - 1 = 0 : Prop) by decide),
          if_pos (show (2 ≤ (7 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((7 : ℕ) - 2 = 0 : Prop) by decide),
          if_pos (show (3 ≤ (7 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((7 : ℕ) - 3 = 0 : Prop) by decide),
          if_pos (show (4 ≤ (7 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((7 : ℕ) - 4 = 0 : Prop) by decide),
          if_pos (show (5 ≤ (7 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((7 : ℕ) - 5 = 0 : Prop) by decide),
          if_pos (show (6 ≤ (7 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((7 : ℕ) - 6 = 0 : Prop) by decide),
          if_pos (show ((7 : ℕ) ≤ 7 : Prop) by decide),
          if_pos (show ((7 : ℕ) - 7 = 0 : Prop) by decide),
          if_neg (show ¬ ((7 : ℕ) = 8 : Prop) by decide), show (7 : ℕ) - 1 = 6 from rfl,
          show (7 : ℕ) - 2 = 5 from rfl, q7, q6, q5]
        norm_num
      · rw [if_neg (show ¬ ((8 : ℕ) = 0 : Prop) by decide), if_pos (show (1 ≤ (8 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((8 : ℕ) - 1 = 0 : Prop) by decide),
          if_pos (show (2 ≤ (8 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((8 : ℕ) - 2 = 0 : Prop) by decide),
          if_pos (show (1 ≤ (8 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((8 : ℕ) - 1 = 0 : Prop) by decide),
          if_pos (show (2 ≤ (8 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((8 : ℕ) - 2 = 0 : Prop) by decide),
          if_pos (show (3 ≤ (8 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((8 : ℕ) - 3 = 0 : Prop) by decide),
          if_pos (show (4 ≤ (8 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((8 : ℕ) - 4 = 0 : Prop) by decide),
          if_pos (show (5 ≤ (8 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((8 : ℕ) - 5 = 0 : Prop) by decide),
          if_pos (show (6 ≤ (8 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((8 : ℕ) - 6 = 0 : Prop) by decide),
          if_pos (show (7 ≤ (8 : ℕ) : Prop) by decide),
          if_neg (show ¬ ((8 : ℕ) - 7 = 0 : Prop) by decide),
          if_pos (show ((8 : ℕ) = 8 : Prop) by decide), show (8 : ℕ) - 1 = 7 from rfl,
          show (8 : ℕ) - 2 = 6 from rfl, q8, q7, q6]
        norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 9 := ⟨m - 9, by omega⟩
      have n0 : ¬ (k + 9 = 0) := by omega
      have n8 : ¬ (k + 9 = 8) := by omega
      have p1 : 1 ≤ k + 9 := by omega
      have p2 : 2 ≤ k + 9 := by omega
      have p3 : 3 ≤ k + 9 := by omega
      have p4 : 4 ≤ k + 9 := by omega
      have p5 : 5 ≤ k + 9 := by omega
      have p6 : 6 ≤ k + 9 := by omega
      have p7 : 7 ≤ k + 9 := by omega
      have m1 : ¬ (k + 9 - 1 = 0) := by omega
      have m2 : ¬ (k + 9 - 2 = 0) := by omega
      have m3 : ¬ (k + 9 - 3 = 0) := by omega
      have m4 : ¬ (k + 9 - 4 = 0) := by omega
      have m5 : ¬ (k + 9 - 5 = 0) := by omega
      have m6 : ¬ (k + 9 - 6 = 0) := by omega
      have m7 : ¬ (k + 9 - 7 = 0) := by omega
      rw [if_neg n0, if_pos p1, if_pos p1, if_neg m1, if_neg m1, if_pos p2, if_pos p2,
        if_neg m2, if_neg m2, if_pos p3, if_neg m3, if_pos p4, if_neg m4, if_pos p5, if_neg m5,
        if_pos p6, if_neg m6, if_pos p7, if_neg m7, if_neg n8,
        show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega]
      have h9 : a (k + 9) = 24 * k + 144 := by
        have := hclosed (k + 9) (by omega)
        omega
      have h8 : a (k + 8) = 24 * k + 120 := by
        have := hclosed (k + 8) (by omega)
        omega
      have h7 : a (k + 7) = 24 * k + 96 := by
        have := hclosed (k + 7) (by omega)
        omega
      have h9q : (a (k + 9) : ℚ) = 24 * (k : ℚ) + 144 := by exact_mod_cast h9
      have h8q : (a (k + 8) : ℚ) = 24 * (k : ℚ) + 120 := by exact_mod_cast h8
      have h7q : (a (k + 7) : ℚ) = 24 * (k : ℚ) + 96 := by exact_mod_cast h7
      linear_combination h9q - 2 * h8q + h7q
  exact ⟨gf, hrec, hclosed⟩
