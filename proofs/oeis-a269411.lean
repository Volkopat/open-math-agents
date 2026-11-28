import OMAStatements.S_oeis_a269411

-- Problem: A269411: Number of length-5 0..n arrays with no repeated value greater than or equal to the previous repeated value.
-- Upstream: formal-conjectures statements/oeis-a269411.lean:0 (declaration OMA.S_oeis_a269411.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: sum out the entries one at a time, in the order x5, x4, x1, x3, x2. For fixed
-- x1..x4 the condition on x5 only matters at x5 = x4, so the count E over x5 is (n+1) or n or 0.
-- Summing E over x4 gives D = n^2 + 2n (x1 /= x2 /= x3), n^2 + n + x2 - 1 (x1 = x2 > x3),
-- n^2 + x2 (x1 = x2 < x3), n^2 + x3 (x1 /= x2 = x3), 0 (x1 = x2 = x3). Summing over x1 and
-- then x3 gives K(x2) = n^4 + 4n^3 + (3n - 1) x2, and the sum over x2 gives
-- 2a(n) + n = 2n^5 + 10n^4 + 11n^3 + 2n^2. The recurrence is the vanishing sixth difference of
-- this quintic, and the g.f. follows by comparing coefficients.

open OMA.S_oeis_a269411 in
theorem OMA.solution : type_of% @OMA.S_oeis_a269411.main := by
  -- sums over range (n + 1) of constants and of simple indicators
  have Lc : ∀ n c : ℕ, ∑ _x ∈ Finset.range (n + 1), c = (n + 1) * c := by
    intro n c
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have Leq : ∀ n e c : ℕ, e ≤ n →
      ∑ x ∈ Finset.range (n + 1), (if x = e then c else 0) = c := by
    intro n e c he
    rw [Finset.sum_ite_eq']
    exact if_pos (Finset.mem_range.mpr (by omega))
  have Llt : ∀ n t c : ℕ, t ≤ n + 1 →
      ∑ x ∈ Finset.range (n + 1), (if x < t then c else 0) = t * c := by
    intro n t c ht
    rw [← Finset.sum_filter]
    have e : (Finset.range (n + 1)).filter (fun x => x < t) = Finset.range t := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [e, Finset.sum_const, Finset.card_range, smul_eq_mul]
  -- summing a pointwise identity with indicators at one point e and below one bound t
  have G : ∀ (n : ℕ) (g : ℕ → ℕ) (e t c d A B C : ℕ), e ≤ n → t ≤ n + 1 →
      (∀ x, x ≤ n → g x + (if x = e then c else 0) + (if x < t then d else 0) =
        A + (if x < t then B else 0) + (if x = e then C else 0)) →
      ∑ x ∈ Finset.range (n + 1), g x + c + t * d = (n + 1) * A + t * B + C := by
    intro n g e t c d A B C he ht h
    have h1 : ∑ x ∈ Finset.range (n + 1),
        (g x + (if x = e then c else 0) + (if x < t then d else 0)) =
        ∑ x ∈ Finset.range (n + 1),
        (A + (if x < t then B else 0) + (if x = e then C else 0)) :=
      Finset.sum_congr rfl (fun x hx => h x (by rw [Finset.mem_range] at hx; omega))
    simp only [Finset.sum_add_distrib] at h1
    have s1 := Leq n e c he
    have s2 := Leq n e C he
    have s3 := Llt n t d ht
    have s4 := Llt n t B ht
    have s5 := Lc n A
    linarith
  -- the count over x5
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ, ∀ n x1 x2 x3 x4, E n x1 x2 x3 x4 =
      ∑ x5 ∈ Finset.range (n + 1), (if ok x1 x2 x3 x4 x5 then 1 else 0) :=
    ⟨_, fun _ _ _ _ _ => rfl⟩
  have hEv : ∀ (n x1 x2 x3 x4 p q : ℕ), x4 ≤ n →
      (∀ x5, x5 ≠ x4 → (if ok x1 x2 x3 x4 x5 then 1 else 0) = q) →
      (if ok x1 x2 x3 x4 x4 then 1 else 0) + p = q →
      E n x1 x2 x3 x4 + p = (n + 1) * q := by
    intro n x1 x2 x3 x4 p q hx4 h1 h2
    have hm : x4 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have e1 : ∑ x5 ∈ (Finset.range (n + 1)).erase x4, (if ok x1 x2 x3 x4 x5 then 1 else 0) =
        ∑ _x5 ∈ (Finset.range (n + 1)).erase x4, q :=
      Finset.sum_congr rfl (fun x5 hx5 => h1 x5 (Finset.ne_of_mem_erase hx5))
    rw [Finset.sum_const, Finset.card_erase_of_mem hm, Finset.card_range, smul_eq_mul,
      Nat.add_sub_cancel] at e1
    rw [hE, ← Finset.add_sum_erase (Finset.range (n + 1)) _ hm, e1]
    linarith
  -- the count over x4 and x5, by the pattern of x1, x2, x3
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℕ → ℕ → ℕ → ℕ, ∀ n x2 x3 x1, D n x2 x3 x1 =
      ∑ x4 ∈ Finset.range (n + 1), E n x1 x2 x3 x4 := ⟨_, fun _ _ _ _ => rfl⟩
  have DA : ∀ n x2 x3 x1, x1 ≠ x2 → x2 ≠ x3 → x3 ≤ n → D n x2 x3 x1 = n * n + 2 * n := by
    intro n x2 x3 x1 h12 h23 hx3
    have hp : ∀ x4, x4 ≤ n → E n x1 x2 x3 x4 + (if x4 = x3 then 1 else 0) +
        (if x4 < 0 then 0 else 0) = (n + 1) + (if x4 < 0 then 0 else 0) +
        (if x4 = x3 then 0 else 0) := by
      intro x4 hx4
      by_cases h : x4 = x3
      · have := hEv n x1 x2 x3 x4 1 1 hx4 (fun x5 hx5 => by split_ifs <;> omega)
          (by split_ifs <;> omega)
        split_ifs <;> omega
      · have := hEv n x1 x2 x3 x4 0 1 hx4 (fun x5 hx5 => by split_ifs <;> omega)
          (by split_ifs <;> omega)
        split_ifs <;> omega
    have hG := G n (E n x1 x2 x3) x3 0 1 0 (n + 1) 0 0 hx3 (by omega) hp
    rw [hD]
    linarith
  have DB1 : ∀ n x2 x3 x1, x1 = x2 → x3 < x2 → x2 ≤ n →
      D n x2 x3 x1 + 1 = (n + 1) * n + x2 := by
    intro n x2 x3 x1 h12 h32 hx2
    have hp : ∀ x4, x4 ≤ n → E n x1 x2 x3 x4 + (if x4 = x3 then 1 else 0) +
        (if x4 < x2 then 0 else 0) = n + (if x4 < x2 then 1 else 0) +
        (if x4 = x3 then 0 else 0) := by
      intro x4 hx4
      by_cases h : x4 = x3 ∨ x2 ≤ x4
      · have := hEv n x1 x2 x3 x4 1 1 hx4 (fun x5 hx5 => by split_ifs <;> omega)
          (by split_ifs <;> omega)
        split_ifs <;> omega
      · have := hEv n x1 x2 x3 x4 0 1 hx4 (fun x5 hx5 => by split_ifs <;> omega)
          (by split_ifs <;> omega)
        split_ifs <;> omega
    have hG := G n (E n x1 x2 x3) x3 x2 1 0 n 1 0 (by omega) (by omega) hp
    rw [hD]
    linarith
  have DB2 : ∀ n x2 x3 x1, x1 = x2 → x2 < x3 → x3 ≤ n → D n x2 x3 x1 = n * n + x2 := by
    intro n x2 x3 x1 h12 h23 hx3
    have hp : ∀ x4, x4 ≤ n → E n x1 x2 x3 x4 + (if x4 = x3 then n else 0) +
        (if x4 < x2 then 0 else 0) = n + (if x4 < x2 then 1 else 0) +
        (if x4 = x3 then 0 else 0) := by
      intro x4 hx4
      by_cases h : x4 = x3
      · have := hEv n x1 x2 x3 x4 0 0 hx4 (fun x5 hx5 => by split_ifs <;> omega)
          (by split_ifs <;> omega)
        split_ifs <;> omega
      · by_cases h' : x4 < x2
        · have := hEv n x1 x2 x3 x4 0 1 hx4 (fun x5 hx5 => by split_ifs <;> omega)
            (by split_ifs <;> omega)
          split_ifs
          omega
        · have := hEv n x1 x2 x3 x4 1 1 hx4 (fun x5 hx5 => by split_ifs <;> omega)
            (by split_ifs <;> omega)
          split_ifs
          omega
    have hG := G n (E n x1 x2 x3) x3 x2 n 0 n 1 0 hx3 (by omega) hp
    rw [hD]
    linarith
  have DC : ∀ n x2 x3 x1, x1 ≠ x2 → x2 = x3 → x3 ≤ n → D n x2 x3 x1 = n * n + x3 := by
    intro n x2 x3 x1 h12 h23 hx3
    have hp : ∀ x4, x4 ≤ n → E n x1 x2 x3 x4 + (if x4 = x3 then n else 0) +
        (if x4 < x3 then 0 else 0) = n + (if x4 < x3 then 1 else 0) +
        (if x4 = x3 then 0 else 0) := by
      intro x4 hx4
      by_cases h : x4 = x3
      · have := hEv n x1 x2 x3 x4 0 0 hx4 (fun x5 hx5 => by split_ifs <;> omega)
          (by split_ifs <;> omega)
        split_ifs <;> omega
      · by_cases h' : x4 < x3
        · have := hEv n x1 x2 x3 x4 0 1 hx4 (fun x5 hx5 => by split_ifs <;> omega)
            (by split_ifs <;> omega)
          split_ifs
          omega
        · have := hEv n x1 x2 x3 x4 1 1 hx4 (fun x5 hx5 => by split_ifs <;> omega)
            (by split_ifs <;> omega)
          split_ifs
          omega
    have hG := G n (E n x1 x2 x3) x3 x3 n 0 n 1 0 hx3 (by omega) hp
    rw [hD]
    linarith
  have DD : ∀ n x2 x3 x1, x1 = x2 → x2 = x3 → D n x2 x3 x1 = 0 := by
    intro n x2 x3 x1 h12 h23
    rw [hD]
    apply Finset.sum_eq_zero
    intro x4 hx4
    have := hEv n x1 x2 x3 x4 0 0 (by rw [Finset.mem_range] at hx4; omega)
      (fun x5 hx5 => by split_ifs <;> omega) (by split_ifs <;> omega)
    omega
  -- the sum over x1
  obtain ⟨H, hH⟩ : ∃ H : ℕ → ℕ → ℕ → ℕ, ∀ n x2 x3, H n x2 x3 =
      ∑ x1 ∈ Finset.range (n + 1), D n x2 x3 x1 := ⟨_, fun _ _ _ => rfl⟩
  have HE : ∀ n x2 x3, x2 = x3 → x3 ≤ n → H n x2 x3 = n * (n * n + x3) := by
    intro n x2 x3 h23 hx3
    have hp : ∀ x1, x1 ≤ n → D n x2 x3 x1 + (if x1 = x2 then n * n + x3 else 0) +
        (if x1 < 0 then 0 else 0) = (n * n + x3) + (if x1 < 0 then 0 else 0) +
        (if x1 = x2 then 0 else 0) := by
      intro x1 hx1
      by_cases h : x1 = x2
      · have := DD n x2 x3 x1 h h23
        split_ifs <;> omega
      · have := DC n x2 x3 x1 h h23 hx3
        split_ifs <;> omega
    have hG := G n (D n x2 x3) x2 0 (n * n + x3) 0 (n * n + x3) 0 0 (by omega) (by omega) hp
    rw [hH]
    linarith
  have HL : ∀ n x2 x3, x3 < x2 → x2 ≤ n → H n x2 x3 + 1 = n ^ 3 + 3 * n ^ 2 + n + x2 := by
    intro n x2 x3 h32 hx2
    have hp : ∀ x1, x1 ≤ n → D n x2 x3 x1 + (if x1 = x2 then n * n + 2 * n + 1 else 0) +
        (if x1 < 0 then 0 else 0) = (n * n + 2 * n) + (if x1 < 0 then 0 else 0) +
        (if x1 = x2 then (n + 1) * n + x2 else 0) := by
      intro x1 hx1
      by_cases h : x1 = x2
      · have := DB1 n x2 x3 x1 h h32 hx2
        split_ifs <;> omega
      · have := DA n x2 x3 x1 h (by omega) (by omega)
        split_ifs <;> omega
    have hG := G n (D n x2 x3) x2 0 (n * n + 2 * n + 1) 0 (n * n + 2 * n) 0
      ((n + 1) * n + x2) (by omega) (by omega) hp
    rw [hH]
    linarith
  have HG : ∀ n x2 x3, x2 < x3 → x3 ≤ n → H n x2 x3 = n ^ 3 + 3 * n ^ 2 + x2 := by
    intro n x2 x3 h23 hx3
    have hp : ∀ x1, x1 ≤ n → D n x2 x3 x1 + (if x1 = x2 then n * n + 2 * n else 0) +
        (if x1 < 0 then 0 else 0) = (n * n + 2 * n) + (if x1 < 0 then 0 else 0) +
        (if x1 = x2 then n * n + x2 else 0) := by
      intro x1 hx1
      by_cases h : x1 = x2
      · have := DB2 n x2 x3 x1 h h23 hx3
        split_ifs <;> omega
      · have := DA n x2 x3 x1 h (by omega) hx3
        split_ifs <;> omega
    have hG := G n (D n x2 x3) x2 0 (n * n + 2 * n) 0 (n * n + 2 * n) 0 (n * n + x2)
      (by omega) (by omega) hp
    rw [hH]
    linarith
  -- the sum over x3
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℕ → ℕ, ∀ n x2, K n x2 =
      ∑ x3 ∈ Finset.range (n + 1), H n x2 x3 := ⟨_, fun _ _ => rfl⟩
  have KK : ∀ n x2, x2 ≤ n → K n x2 + x2 = n ^ 4 + 4 * n ^ 3 + 3 * n * x2 := by
    intro n x2 hx2
    have hp : ∀ x3, x3 ≤ n → H n x2 x3 + (if x3 = x2 then 3 * n ^ 2 + x2 else 0) +
        (if x3 < x2 then 1 else 0) = (n ^ 3 + 3 * n ^ 2 + x2) + (if x3 < x2 then n else 0) +
        (if x3 = x2 then n * x2 else 0) := by
      intro x3 hx3
      rcases Nat.lt_trichotomy x3 x2 with h | h | h
      · have := HL n x2 x3 h hx2
        split_ifs <;> omega
      · have h' : H n x2 x3 = n * (n * n + x2) := by
          rw [HE n x2 x3 h.symm hx3, h]
        have hlt : ¬ x3 < x2 := by omega
        rw [if_pos h, if_pos h, if_neg hlt, if_neg hlt]
        linarith
      · have := HG n x2 x3 h hx3
        split_ifs <;> omega
    have hG := G n (H n x2) x2 x2 (3 * n ^ 2 + x2) 1 (n ^ 3 + 3 * n ^ 2 + x2) n (n * x2)
      hx2 (by omega) hp
    rw [hK]
    linarith
  -- a(n) as the iterated sum
  have hsum : ∀ n, a n = ∑ x2 ∈ Finset.range (n + 1), K n x2 := by
    intro n
    have e1 : a n = ∑ x1 ∈ Finset.range (n + 1), ∑ x2 ∈ Finset.range (n + 1),
        ∑ x3 ∈ Finset.range (n + 1), D n x2 x3 x1 := by
      unfold a
      rw [Finset.card_filter]
      simp only [Finset.sum_product, hD, hE]
    rw [e1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x2 _ => ?_)
    rw [hK, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun x3 _ => (hH n x2 x3).symm)
  -- the closed form
  have hcf : ∀ n, 2 * a n + n = 2 * n ^ 5 + 10 * n ^ 4 + 11 * n ^ 3 + 2 * n ^ 2 := by
    intro n
    have e1 := hsum n
    have h1 : ∑ x2 ∈ Finset.range (n + 1), (K n x2 + x2) =
        ∑ x2 ∈ Finset.range (n + 1), (n ^ 4 + 4 * n ^ 3 + 3 * n * x2) :=
      Finset.sum_congr rfl (fun x2 hx2 => KK n x2 (by rw [Finset.mem_range] at hx2; omega))
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Lc n] at h1
    have h2 := Finset.sum_range_id_mul_two (n + 1)
    rw [Nat.add_sub_cancel] at h2
    have h3 : (∑ i ∈ Finset.range (n + 1), i) * 2 * (3 * n) = (n + 1) * n * (3 * n) := by
      rw [h2]
    linarith
  have hcfz : ∀ n, (2 : ℤ) * (a n : ℤ) + (n : ℤ) =
      2 * (n : ℤ) ^ 5 + 10 * (n : ℤ) ^ 4 + 11 * (n : ℤ) ^ 3 + 2 * (n : ℤ) ^ 2 := by
    intro n
    exact_mod_cast hcf n
  have hcfq : ∀ n, (2 : ℚ) * (a n : ℚ) + (n : ℚ) =
      2 * (n : ℚ) ^ 5 + 10 * (n : ℚ) ^ 4 + 11 * (n : ℚ) ^ 3 + 2 * (n : ℚ) ^ 2 := by
    intro n
    exact_mod_cast hcf n
  have a0 : a 0 = 0 := by
    have h := hcf 0
    norm_num at h
    omega
  have a1 : a 1 = 12 := by
    have h := hcf 1
    norm_num at h
    omega
  have a2 : a 2 = 159 := by
    have h := hcf 2
    norm_num at h
    omega
  have a3 : a 3 = 804 := by
    have h := hcf 3
    norm_num at h
    omega
  have a4 : a 4 = 2670 := by
    have h := hcf 4
    norm_num at h
    omega
  have a5 : a 5 = 6960 := by
    have h := hcf 5
    norm_num at h
    omega
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
      show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega,
      show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega]
    have h1 := hcfz (k + 1)
    have h2 := hcfz (k + 2)
    have h3 := hcfz (k + 3)
    have h4 := hcfz (k + 4)
    have h5 := hcfz (k + 5)
    have h6 := hcfz (k + 6)
    have h7 := hcfz (k + 7)
    push_cast at h1 h2 h3 h4 h5 h6 h7
    linarith
  · have e : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 6 =
        PowerSeries.mk (fun n => (a n : ℚ))
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 15 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 20 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 15 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 5)
          + PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 6 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 15,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 20]
      ring
    have e2 : (3 * PowerSeries.X * (4 + 29 * PowerSeries.X + 10 * PowerSeries.X ^ 2 -
        3 * PowerSeries.X ^ 3) : PowerSeries ℚ) =
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 12 * PowerSeries.X ^ 1 +
          (PowerSeries.C : ℚ →+* PowerSeries ℚ) 87 * PowerSeries.X ^ 2 +
          (PowerSeries.C : ℚ →+* PowerSeries ℚ) 30 * PowerSeries.X ^ 3 -
          (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9 * PowerSeries.X ^ 4 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 12,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 87,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 30,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9]
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub]
    simp only [PowerSeries.coeff_C_mul_X_pow]
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]
    rcases Nat.lt_or_ge m 6 with hm | hm
    · interval_cases m <;> norm_num [a0, a1, a2, a3, a4, a5]
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 6 := ⟨m - 6, by omega⟩
      rw [if_pos (show 1 ≤ j + 6 by omega), if_pos (show 2 ≤ j + 6 by omega),
        if_pos (show 3 ≤ j + 6 by omega), if_pos (show 4 ≤ j + 6 by omega),
        if_pos (show 5 ≤ j + 6 by omega), if_pos (show 6 ≤ j + 6 by omega),
        if_neg (show ¬ (j + 6 = 1) by omega), if_neg (show ¬ (j + 6 = 2) by omega),
        if_neg (show ¬ (j + 6 = 3) by omega), if_neg (show ¬ (j + 6 = 4) by omega),
        show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
        show j + 6 - 3 = j + 3 by omega, show j + 6 - 4 = j + 2 by omega,
        show j + 6 - 5 = j + 1 by omega, show j + 6 - 6 = j by omega]
      have h0 := hcfq j
      have h1 := hcfq (j + 1)
      have h2 := hcfq (j + 2)
      have h3 := hcfq (j + 3)
      have h4 := hcfq (j + 4)
      have h5 := hcfq (j + 5)
      have h6 := hcfq (j + 6)
      push_cast at h1 h2 h3 h4 h5 h6
      linarith
