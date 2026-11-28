import OMAStatements.S_oeis_a022693

open scoped PowerSeries.WithPiTopology

/-- The weight of a part `i` repeated `c` times: `(-1)^c * i^c`. -/
def bc22f (i c : ℕ) : ℤ := (-1 : ℤ) ^ c * (i : ℤ) ^ c

/-- The factor of `Nat.Partition.genFun f` attached to the part `k + 1`, stated over a general
commutative semiring exactly as in `Nat.Partition.hasProd_genFun`. -/
noncomputable def bc22G {R : Type*} [CommSemiring R] [TopologicalSpace R] (f : ℕ → ℕ → R)
    (k : ℕ) : PowerSeries R :=
  1 + ∑' j : ℕ, f (k + 1) (j + 1) • (PowerSeries.X : PowerSeries R) ^ ((k + 1) * (j + 1))

/-- The factor for the weight `bc22f`. -/
noncomputable def bc22F (k : ℕ) : PowerSeries ℤ := bc22G bc22f k

theorem bc22_tsum (c n : ℕ) (hc : 0 < c) :
    (∑' j : ℕ, if n = c * (j + 1) then bc22f c (j + 1) else 0) =
      if n ≠ 0 ∧ c ∣ n then bc22f c (n / c) else 0 := by
  by_cases h : n ≠ 0 ∧ c ∣ n
  · rw [if_pos h]
    obtain ⟨hn, t, rfl⟩ := h
    have ht : 0 < t := Nat.pos_of_ne_zero (fun h0 => hn (by rw [h0, mul_zero]))
    rw [tsum_eq_single (t - 1)]
    · rw [if_pos (show c * t = c * (t - 1 + 1) by rw [Nat.sub_add_cancel ht]),
        Nat.sub_add_cancel ht, Nat.mul_div_cancel_left t hc]
    · intro j hj
      rw [if_neg]
      intro hj'
      apply hj
      have h2 := Nat.eq_of_mul_eq_mul_left hc hj'
      omega
  · rw [if_neg h]
    have h' : ∀ j : ℕ, ¬ (n = c * (j + 1)) := by
      intro j hj
      apply h
      refine ⟨?_, ⟨j + 1, hj⟩⟩
      rw [hj]
      exact Nat.mul_ne_zero (by omega) (by omega)
    first
      | rw [show (fun j : ℕ => if n = c * (j + 1) then bc22f c (j + 1) else 0) = fun _ => 0 from
          funext (fun j => if_neg (h' j)), tsum_zero]
      | simp [h']

theorem bc22_coeff_F (k n : ℕ) :
    PowerSeries.coeff n (bc22F k) = if (k + 1) ∣ n then bc22f (k + 1) (n / (k + 1)) else 0 := by
  unfold bc22F bc22G
  rw [map_add, (Nat.Partition.summable_genFun_term bc22f k).map_tsum _
    (PowerSeries.WithPiTopology.continuous_coeff _ _)]
  simp only [PowerSeries.coeff_smul, map_smul, PowerSeries.coeff_X_pow, PowerSeries.coeff_one,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [bc22_tsum (k + 1) n (by omega)]
  by_cases h0 : n = 0
  · subst h0
    simp [bc22f]
  · by_cases hd : (k + 1) ∣ n
    · simp [h0, hd]
    · simp [h0, hd]

theorem bc22_inv (k : ℕ) :
    (1 + PowerSeries.C (((k + 1 : ℕ)) : ℤ) * PowerSeries.X ^ (k + 1)) * bc22F k = 1 := by
  ext n
  rw [add_mul, one_mul, mul_assoc, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_one, bc22_coeff_F k n]
  by_cases hd : (k + 1) ∣ n
  · obtain ⟨t, rfl⟩ := hd
    rw [if_pos (dvd_mul_right (k + 1) t), Nat.mul_div_cancel_left t (show 0 < k + 1 by omega)]
    rcases t with _ | s
    · simp [bc22f]
    · have e : (k + 1) * (s + 1) = (k + 1) * s + (k + 1) := by ring
      have h1 : k + 1 ≤ (k + 1) * (s + 1) := by omega
      have h2 : (k + 1) * (s + 1) - (k + 1) = (k + 1) * s := by omega
      have hne : (k + 1) * (s + 1) ≠ 0 := by omega
      rw [if_pos h1, if_neg hne, h2, bc22_coeff_F k ((k + 1) * s),
        if_pos (dvd_mul_right (k + 1) s), Nat.mul_div_cancel_left s (show 0 < k + 1 by omega)]
      unfold bc22f
      ring
  · have hn0 : n ≠ 0 := by
      rintro rfl
      exact hd (dvd_zero _)
    rw [if_neg hd, if_neg hn0, zero_add]
    split_ifs with h1
    · rw [bc22_coeff_F k (n - (k + 1)), if_neg, mul_zero]
      intro h3
      apply hd
      have h4 := dvd_add h3 (dvd_refl (k + 1))
      rwa [Nat.sub_add_cancel h1] at h4
    · rw [mul_zero]

theorem bc22_F_mod (N k : ℕ) (hk : N ≤ k) :
    (PowerSeries.X : PowerSeries ℤ) ^ (N + 1) ∣ bc22F k - 1 := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub, bc22_coeff_F k m, PowerSeries.coeff_one]
  by_cases h0 : m = 0
  · subst h0
    simp [bc22f]
  · have hnd : ¬ (k + 1) ∣ m := by
      intro h
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h
      omega
    rw [if_neg hnd, if_neg h0, sub_zero]

theorem bc22_prod_mod (N : ℕ) (s : Finset ℕ) (hs : ∀ k ∈ s, N ≤ k) :
    (PowerSeries.X : PowerSeries ℤ) ^ (N + 1) ∣ (∏ k ∈ s, bc22F k) - 1 := by
  refine Finset.prod_induction bc22F
    (fun a => (PowerSeries.X : PowerSeries ℤ) ^ (N + 1) ∣ a - 1) ?_ ?_ ?_
  · intro a b ha hb
    show (PowerSeries.X : PowerSeries ℤ) ^ (N + 1) ∣ a * b - 1
    have e : a * b - 1 = a * (b - 1) + (a - 1) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right hb a) ha
  · show (PowerSeries.X : PowerSeries ℤ) ^ (N + 1) ∣ 1 - 1
    simp
  · intro k hk
    exact bc22_F_mod N k (hs k hk)

theorem bc22_icc_range (N : ℕ) :
    ∏ m ∈ Finset.Icc 1 N, (1 + PowerSeries.C (m : ℤ) * PowerSeries.X ^ m : PowerSeries ℤ) =
      ∏ k ∈ Finset.range N,
        (1 + PowerSeries.C (((k + 1 : ℕ)) : ℤ) * PowerSeries.X ^ (k + 1) : PowerSeries ℤ) := by
  induction N with
  | zero => first | simp | rfl
  | succ N ih =>
    rw [Finset.prod_Icc_succ_top (show 1 ≤ N + 1 by omega), ih, Finset.prod_range_succ]

theorem bc22_P0 (N : ℕ) :
    PowerSeries.coeff 0
      (∏ m ∈ Finset.Icc 1 N, (1 + PowerSeries.C (m : ℤ) * PowerSeries.X ^ m : PowerSeries ℤ)) = 1 := by
  rw [bc22_icc_range, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_prod]
  apply Finset.prod_eq_one
  intro k _
  simp

theorem bc22_key (s : Multiset ℕ) :
    s.toFinsupp.prod bc22f = (-1 : ℤ) ^ (Multiset.card s) * ((s.prod : ℕ) : ℤ) := by
  simp_rw [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  unfold bc22f
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Multiset.toFinset_sum_count_eq,
    Finset.prod_multiset_count s]
  push_cast
  try rfl

theorem bc22_uniq (P : ℕ → PowerSeries ℤ) (hP : ∀ N, PowerSeries.coeff 0 (P N) = 1)
    (f g : PowerSeries ℤ)
    (hf : ∀ N : ℕ, PowerSeries.coeff N (P N * f) = if N = 0 then 1 else 0)
    (hg : ∀ N : ℕ, PowerSeries.coeff N (P N * g) = if N = 0 then 1 else 0) :
    ∀ n, PowerSeries.coeff n f = PowerSeries.coeff n g := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  have h := (hf n).trans (hg n).symm
  have hmem : ((0 : ℕ), n) ∈ Finset.HasAntidiagonal.antidiagonal n :=
    Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add n)
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul, ← Finset.add_sum_erase _ _ hmem,
    ← Finset.add_sum_erase _ _ hmem] at h
  have hs : (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
        PowerSeries.coeff x.1 (P n) * PowerSeries.coeff x.2 f) =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
        PowerSeries.coeff x.1 (P n) * PowerSeries.coeff x.2 g := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hx2 : x.2 < n := by
      obtain ⟨hne, hsum⟩ := hx
      rcases x with ⟨a, b⟩
      have hsum' : a + b = n := hsum
      have hne' : ¬ (a = 0 ∧ b = n) := fun hab => hne (by rw [hab.1, hab.2])
      show b < n
      omega
    rw [ih x.2 hx2]
  rw [hs, add_left_inj] at h
  have h5 : PowerSeries.coeff 0 (P n) * PowerSeries.coeff n f =
      PowerSeries.coeff 0 (P n) * PowerSeries.coeff n g := h
  rw [hP n, one_mul, one_mul] at h5
  exact h5

theorem bc22_hG (N : ℕ) :
    PowerSeries.coeff N
      ((∏ m ∈ Finset.Icc 1 N, (1 + PowerSeries.C (m : ℤ) * PowerSeries.X ^ m : PowerSeries ℤ)) *
        Nat.Partition.genFun bc22f) = if N = 0 then 1 else 0 := by
  have hlim : ∀ d : ℕ, ∀ᶠ M in Filter.atTop,
      PowerSeries.coeff d (∏ k ∈ Finset.range M, bc22F k) =
        PowerSeries.coeff d (Nat.Partition.genFun bc22f) := by
    intro d
    have h1 : HasProd bc22F (Nat.Partition.genFun bc22f) := Nat.Partition.hasProd_genFun bc22f
    have h2 : Filter.Tendsto (fun s : Finset ℕ => PowerSeries.coeff d (∏ k ∈ s, bc22F k))
        Filter.atTop (nhds (PowerSeries.coeff d (Nat.Partition.genFun bc22f))) := by
      first
        | exact (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℤ _ _ _).1 h1 d
        | (rw [HasProd, SummationFilter.unconditional_filter,
            PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at h1
           exact h1 d)
        | (rw [HasProd, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at h1
           exact h1 d)
    have h3 := h2.comp Filter.tendsto_finset_range
    rw [nhds_discrete ℤ, Filter.tendsto_pure] at h3
    exact h3
  obtain ⟨M, hM, hNM⟩ := ((Filter.eventually_all.2 (fun i : Fin (N + 1) => hlim i.val)).and
    (Filter.eventually_ge_atTop N)).exists
  have e1 : ∀ A : PowerSeries ℤ, PowerSeries.coeff N (A * Nat.Partition.genFun bc22f) =
      PowerSeries.coeff N (A * ∏ k ∈ Finset.range M, bc22F k) := by
    intro A
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp2 : p.2 < N + 1 := by
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      omega
    have h3 : PowerSeries.coeff p.2 (∏ k ∈ Finset.range M, bc22F k) =
        PowerSeries.coeff p.2 (Nat.Partition.genFun bc22f) := hM ⟨p.2, hp2⟩
    rw [h3]
  rw [e1, bc22_icc_range, ← Finset.prod_range_mul_prod_Ico bc22F hNM, ← mul_assoc,
    ← Finset.prod_mul_distrib, Finset.prod_eq_one (fun k _ => bc22_inv k), one_mul]
  have hd := bc22_prod_mod N (Finset.Ico N M) (fun k hk => (Finset.mem_Ico.1 hk).1)
  rw [PowerSeries.X_pow_dvd_iff] at hd
  have h4 := hd N (by omega)
  rw [map_sub, PowerSeries.coeff_one] at h4
  exact sub_eq_zero.1 h4

theorem OMA.solution : type_of% @OMA.S_oeis_a022693.main := by
  intro f hf n
  rw [bc22_uniq
    (fun N => ∏ m ∈ Finset.Icc 1 N, (1 + PowerSeries.C (m : ℤ) * PowerSeries.X ^ m : PowerSeries ℤ))
    bc22_P0 f (Nat.Partition.genFun bc22f) hf bc22_hG n, Nat.Partition.coeff_genFun]
  exact Finset.sum_congr rfl (fun p _ => bc22_key p.parts)
