import OMAStatements.S_oeis_a200039

-- Problem: A200039: Number of -n..n arrays x(0..2) of 3 elements with sum zero and with zeroth through 2nd differences all nonzero.
-- Upstream: formal-conjectures statements/oeis-a200039.lean:0 (declaration OMA.S_oeis_a200039.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: negation swaps the arrays with x(1) < 0 and those with x(1) > 0. An array with
-- x(1) > 0 is (p, q, -(p+q)), (-(p+q), p, q) or (-p, p+q, -q) with p, q >= 1 and p + q <= n,
-- and the conditions only exclude p = q in the first two forms. The pairs (p, q) correspond to
-- (p + q - 1, p - 1) with 0 <= p - 1 < p + q - 1 < n, so there are n(n-1)/2 of them, and n/2
-- of them have p = q. Hence a(n) = 2 (3 n(n-1)/2 - 2 (n/2)) = 3n^2 - 3n - 4 floor(n/2), which
-- gives both closed forms and the recurrence behind the g.f. (coefficient comparison).

open OMA.S_oeis_a200039 in
theorem OMA.solution : type_of% @OMA.S_oeis_a200039.main := by
  have hgauss : ∀ m : ℕ, ((∑ i ∈ Finset.range m, i : ℕ) : ℤ) * 2 = (m : ℤ) * m - m := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_add_one]
      linear_combination ih
  have hA : ∀ n : ℕ, (a n : ℤ) = 3 * (n : ℤ) ^ 2 - 3 * n - 4 * ((n / 2 : ℕ) : ℤ) := by
    intro n
    obtain ⟨T, hT⟩ : ∃ T : Finset (ℕ × ℕ), T = ((Finset.range (n + 1)) ×ˢ
        (Finset.range (n + 1))).filter (fun pq => 1 ≤ pq.1 ∧ 1 ≤ pq.2 ∧ pq.1 + pq.2 ≤ n) :=
      ⟨_, rfl⟩
    have hTU : T.card = ((Finset.range n).sigma (fun s => Finset.range s)).card := by
      refine Finset.card_bij' (fun pq _ => (⟨pq.1 + pq.2 - 1, pq.1 - 1⟩ : (_ : ℕ) × ℕ))
        (fun x _ => (x.2 + 1, x.1 - x.2)) ?_ ?_ ?_ ?_
      · rintro ⟨p, q⟩ h
        simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
        simp only [Finset.mem_sigma, Finset.mem_range]
        omega
      · rintro ⟨s, i⟩ h
        simp only [Finset.mem_sigma, Finset.mem_range] at h
        rw [hT]
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩, ?_⟩
        · show i + 1 < n + 1
          omega
        · show s - i < n + 1
          omega
        · show 1 ≤ i + 1 ∧ 1 ≤ s - i ∧ i + 1 + (s - i) ≤ n
          omega
      · rintro ⟨p, q⟩ h
        simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
        simp only [Prod.mk.injEq]
        omega
      · rintro ⟨s, i⟩ h
        simp only [Finset.mem_sigma, Finset.mem_range] at h
        exact Sigma.ext (show i + 1 + (s - i) - 1 = s by omega)
          (heq_of_eq (show i + 1 - 1 = i by omega))
    have hU : ((Finset.range n).sigma (fun s => Finset.range s)).card =
        ∑ s ∈ Finset.range n, s := by
      rw [Finset.card_sigma]
      simp only [Finset.card_range]
    have hdiag : (T.filter (fun pq => pq.1 = pq.2)).card = n / 2 := by
      rw [← Finset.card_range (n / 2)]
      refine Finset.card_bij' (fun pq _ => pq.1 - 1) (fun k _ => (k + 1, k + 1)) ?_ ?_ ?_ ?_
      · rintro ⟨p, q⟩ h
        simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
        omega
      · intro k h
        rw [Finset.mem_range] at h
        refine Finset.mem_filter.mpr ⟨?_, rfl⟩
        rw [hT]
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩, ?_⟩
        · show k + 1 < n + 1
          omega
        · show k + 1 < n + 1
          omega
        · show 1 ≤ k + 1 ∧ 1 ≤ k + 1 ∧ k + 1 + (k + 1) ≤ n
          omega
      · rintro ⟨p, q⟩ h
        simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
        simp only [Prod.mk.injEq]
        omega
      · intro k _
        show k + 1 - 1 = k
        omega
    have hsplitT : (T.filter (fun pq => pq.1 = pq.2)).card +
        (T.filter (fun pq => ¬ pq.1 = pq.2)).card = T.card :=
      Finset.card_filter_add_card_filter_not _
    have hsplit1 : ((goodSet n).filter (fun x => 0 < x.2.1)).card +
        ((goodSet n).filter (fun x => ¬ 0 < x.2.1)).card = (goodSet n).card :=
      Finset.card_filter_add_card_filter_not _
    have hneg : ((goodSet n).filter (fun x => ¬ 0 < x.2.1)).card =
        ((goodSet n).filter (fun x => 0 < x.2.1)).card := by
      refine Finset.card_bij' (fun x _ => (-x.1, -x.2.1, -x.2.2))
        (fun x _ => (-x.1, -x.2.1, -x.2.2)) ?_ ?_ ?_ ?_
      · rintro ⟨x0, x1, x2⟩ h
        simp only [goodSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h ⊢
        omega
      · rintro ⟨x0, x1, x2⟩ h
        simp only [goodSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h ⊢
        omega
      · rintro ⟨x0, x1, x2⟩ _
        simp only [neg_neg]
      · rintro ⟨x0, x1, x2⟩ _
        simp only [neg_neg]
    have hsplit2 : (((goodSet n).filter (fun x => 0 < x.2.1)).filter (fun x => 0 < x.1)).card +
        (((goodSet n).filter (fun x => 0 < x.2.1)).filter (fun x => ¬ 0 < x.1)).card =
        ((goodSet n).filter (fun x => 0 < x.2.1)).card :=
      Finset.card_filter_add_card_filter_not _
    have hsplit3 : ((((goodSet n).filter (fun x => 0 < x.2.1)).filter
          (fun x => ¬ 0 < x.1)).filter (fun x => 0 < x.2.2)).card +
        ((((goodSet n).filter (fun x => 0 < x.2.1)).filter
          (fun x => ¬ 0 < x.1)).filter (fun x => ¬ 0 < x.2.2)).card =
        (((goodSet n).filter (fun x => 0 < x.2.1)).filter (fun x => ¬ 0 < x.1)).card :=
      Finset.card_filter_add_card_filter_not _
    have hK1 : (((goodSet n).filter (fun x => 0 < x.2.1)).filter (fun x => 0 < x.1)).card =
        (T.filter (fun pq => ¬ pq.1 = pq.2)).card := by
      refine Finset.card_bij' (fun x _ => (x.1.toNat, x.2.1.toNat))
        (fun pq _ => ((pq.1 : ℤ), (pq.2 : ℤ), -((pq.1 : ℤ) + (pq.2 : ℤ)))) ?_ ?_ ?_ ?_
      · rintro ⟨x0, x1, x2⟩ h
        simp only [goodSet, hT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_range] at h ⊢
        omega
      · rintro ⟨p, q⟩ h
        simp only [goodSet, hT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_range] at h ⊢
        omega
      · rintro ⟨x0, x1, x2⟩ h
        simp only [goodSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h
        simp only [Prod.mk.injEq]
        omega
      · rintro ⟨p, q⟩ _
        simp only [Prod.mk.injEq]
        omega
    have hK2 : ((((goodSet n).filter (fun x => 0 < x.2.1)).filter
          (fun x => ¬ 0 < x.1)).filter (fun x => 0 < x.2.2)).card =
        (T.filter (fun pq => ¬ pq.1 = pq.2)).card := by
      refine Finset.card_bij' (fun x _ => (x.2.1.toNat, x.2.2.toNat))
        (fun pq _ => (-((pq.1 : ℤ) + (pq.2 : ℤ)), (pq.1 : ℤ), (pq.2 : ℤ))) ?_ ?_ ?_ ?_
      · rintro ⟨x0, x1, x2⟩ h
        simp only [goodSet, hT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_range] at h ⊢
        omega
      · rintro ⟨p, q⟩ h
        simp only [goodSet, hT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_range] at h ⊢
        omega
      · rintro ⟨x0, x1, x2⟩ h
        simp only [goodSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h
        simp only [Prod.mk.injEq]
        omega
      · rintro ⟨p, q⟩ _
        simp only [Prod.mk.injEq]
        omega
    have hK3 : ((((goodSet n).filter (fun x => 0 < x.2.1)).filter
          (fun x => ¬ 0 < x.1)).filter (fun x => ¬ 0 < x.2.2)).card = T.card := by
      refine Finset.card_bij' (fun x _ => ((-x.1).toNat, (-x.2.2).toNat))
        (fun pq _ => (-(pq.1 : ℤ), (pq.1 : ℤ) + (pq.2 : ℤ), -(pq.2 : ℤ))) ?_ ?_ ?_ ?_
      · rintro ⟨x0, x1, x2⟩ h
        simp only [goodSet, hT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_range] at h ⊢
        omega
      · rintro ⟨p, q⟩ h
        simp only [goodSet, hT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_range] at h ⊢
        omega
      · rintro ⟨x0, x1, x2⟩ h
        simp only [goodSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h
        simp only [Prod.mk.injEq]
        omega
      · rintro ⟨p, q⟩ _
        simp only [Prod.mk.injEq]
        omega
    have hS : (goodSet n).card + 4 * (n / 2) = 6 * T.card := by
      omega
    have hS' : ((goodSet n).card : ℤ) + 4 * ((n / 2 : ℕ) : ℤ) = 6 * (T.card : ℤ) := by
      exact_mod_cast hS
    have hT2 : (T.card : ℤ) * 2 = (n : ℤ) * n - n := by
      rw [hTU, hU]
      exact hgauss n
    show ((goodSet n).card : ℤ) = 3 * (n : ℤ) ^ 2 - 3 * n - 4 * ((n / 2 : ℕ) : ℤ)
    linear_combination hS' + 3 * hT2
  have hrecZ : ∀ j : ℕ, (a (j + 5) : ℤ) - 2 * a (j + 4) + 2 * a (j + 2) - a (j + 1) = 0 := by
    intro j
    have hf : (((j + 5) / 2 : ℕ) : ℤ) - 2 * (((j + 4) / 2 : ℕ) : ℤ) +
        2 * (((j + 2) / 2 : ℕ) : ℤ) - (((j + 1) / 2 : ℕ) : ℤ) = 0 := by
      omega
    have c5 : ((j + 5 : ℕ) : ℤ) = (j : ℤ) + 5 := by
      push_cast
      ring
    have c4 : ((j + 4 : ℕ) : ℤ) = (j : ℤ) + 4 := by
      push_cast
      ring
    have c2 : ((j + 2 : ℕ) : ℤ) = (j : ℤ) + 2 := by
      push_cast
      ring
    have c1 : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by
      push_cast
      ring
    rw [hA (j + 5), hA (j + 4), hA (j + 2), hA (j + 1), c5, c4, c2, c1]
    linear_combination (-4 : ℤ) * hf
  have hrecN : ∀ j : ℕ, a (j + 5) + 2 * a (j + 2) = 2 * a (j + 4) + a (j + 1) := by
    intro j
    have h := hrecZ j
    omega
  have hrecQ : ∀ j : ℕ, (a (j + 5) : ℚ) - 2 * a (j + 4) + 2 * a (j + 2) - a (j + 1) = 0 := by
    intro j
    have h : (a (j + 5) : ℚ) + 2 * a (j + 2) = 2 * a (j + 4) + a (j + 1) := by
      exact_mod_cast hrecN j
    linarith
  have a1 : (a 1 : ℚ) = 0 := by
    have h := hA 1
    norm_num at h
    exact_mod_cast h
  have a2 : (a 2 : ℚ) = 2 := by
    have h := hA 2
    norm_num at h
    exact_mod_cast h
  have a3 : (a 3 : ℚ) = 14 := by
    have h := hA 3
    norm_num at h
    exact_mod_cast h
  have a4 : (a 4 : ℚ) = 28 := by
    have h := hA 4
    norm_num at h
    exact_mod_cast h
  have hBD : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
      ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X)) =
      2 * PowerSeries.X + 10 * PowerSeries.X ^ 2 := by
    have e : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X)) =
        PowerSeries.mk (fun n => (a (n + 1) : ℚ))
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
            (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * PowerSeries.X ^ 1)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
            (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * PowerSeries.X ^ 3)
          - PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * PowerSeries.X ^ 4 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
      ring
    have e2 : (2 * PowerSeries.X + 10 * PowerSeries.X ^ 2 : PowerSeries ℚ) =
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * PowerSeries.X ^ 1
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 * PowerSeries.X ^ 2 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10]
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk]
    rcases Nat.lt_or_ge m 4 with hm | hm
    · interval_cases m
      · norm_num [a1]
      · norm_num [a1, a2]
      · norm_num [a2, a3]
      · norm_num [a1, a3, a4]
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 4 := ⟨m - 4, by omega⟩
      rw [if_pos (show 1 ≤ j + 4 by omega), if_pos (show 3 ≤ j + 4 by omega),
        if_pos (show 4 ≤ j + 4 by omega), if_pos (show 1 ≤ j + 4 by omega),
        if_pos (show 2 ≤ j + 4 by omega), PowerSeries.coeff_C, PowerSeries.coeff_C,
        if_neg (show ¬ (j + 4 - 1 = 0) by omega), if_neg (show ¬ (j + 4 - 2 = 0) by omega),
        show j + 4 - 1 + 1 = j + 4 by omega, show j + 4 - 3 + 1 = j + 2 by omega,
        show j + 4 - 4 + 1 = j + 1 by omega, show j + 4 + 1 = j + 5 by omega]
      linarith [hrecQ j]
  refine ⟨?_, fun n _ hn => ?_, fun n _ hn => ?_⟩
  · rw [mul_assoc, hBD]
    ring
  · obtain ⟨m, rfl⟩ := hn
    rw [hA, show (m + m) / 2 = m by omega]
    push_cast
    ring
  · obtain ⟨m, rfl⟩ := hn
    rw [hA, show (2 * m + 1) / 2 = m by omega]
    push_cast
    ring
