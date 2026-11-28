import OMAStatements.S_oeis_a364305

-- Problem: OEIS A364305
-- Credit: @EmadY
--
-- Proof of Peter Bala's prime-power supercongruence for
--   a(n) = (8n)! (5n)! (3n)! / ((6n)! (4n)!^2 n!^2)
-- via factorial p-adic valuation bounds, prime-factor splitting into p-coprime
-- factorial blocks, and the Wolstenholme-Jacobsthal-Kazandzidis prime-power
-- block congruence (cf. Mestrovic, eq. 39).

private def unitFact (p M : ℕ) : ℕ :=
  ∏ j ∈ (Finset.Icc 1 M).filter (fun j => ¬ p ∣ j), j

private def num (m : ℕ) : ℕ :=
  (8 * m).factorial * (5 * m).factorial * (3 * m).factorial

private def den (m : ℕ) : ℕ :=
  (6 * m).factorial * (4 * m).factorial ^ 2 * m.factorial ^ 2

private lemma mul_div_decomp (c m d : ℕ) (hd : 0 < d) :
    (c * m) / d = c * (m / d) + (c * (m % d)) / d := by
  have hm : c * m = d * (c * (m / d)) + c * (m % d) := by
    calc c * m = c * (d * (m / d) + m % d) := by rw [Nat.div_add_mod]
    _ = d * (c * (m / d)) + c * (m % d) := by ring
  rw [hm, Nat.mul_add_div hd]

private lemma div_sum_le (m d : ℕ) (hd : 0 < d) :
    (6 * m) / d + 2 * ((4 * m) / d) + 2 * (m / d) ≤
      (8 * m) / d + (5 * m) / d + (3 * m) / d := by
  rw [mul_div_decomp 6 m d hd, mul_div_decomp 4 m d hd,
    mul_div_decomp 8 m d hd, mul_div_decomp 5 m d hd, mul_div_decomp 3 m d hd]
  set r := m % d
  have hr : r < d := Nat.mod_lt m hd
  suffices h : (6 * r) / d + 2 * ((4 * r) / d) ≤
      (8 * r) / d + (5 * r) / d + (3 * r) / d by omega
  have ub : ∀ c k : ℕ, c * r < (k + 1) * d → (c * r) / d ≤ k := fun c k hlt =>
    Nat.le_of_not_lt fun hge => by
      have h1 : (k + 1) * d ≤ (c * r) / d * d := Nat.mul_le_mul_right d hge
      have h2 : (c * r) / d * d ≤ c * r := Nat.div_mul_le_self (c * r) d
      omega
  have lb : ∀ c k : ℕ, k * d ≤ c * r → k ≤ (c * r) / d := fun c k hle =>
    Nat.le_of_not_lt fun hlt => by
      have h1 : d * ((c * r) / d + 1) ≤ d * k := Nat.mul_le_mul_left d hlt
      have h2 : c * r < d * ((c * r) / d + 1) := Nat.lt_mul_div_succ (c * r) hd
      have h3 : d * k = k * d := Nat.mul_comm d k
      omega
  have := lb 8 0 (by omega); have := lb 5 0 (by omega); have := lb 3 0 (by omega)
  if h1 : 6 * r < d then
    have := ub 6 0 (by omega); have := ub 4 0 (by omega); omega
  else if h2 : 4 * r < d then
    have := ub 6 1 (by omega); have := ub 4 0 (by omega); have := lb 8 1 (by omega); omega
  else if h3 : 3 * r < d then
    have := ub 6 1 (by omega); have := ub 4 1 (by omega)
    have := lb 8 2 (by omega); have := lb 5 1 (by omega); omega
  else if h4 : 2 * r < d then
    have := ub 6 2 (by omega); have := ub 4 1 (by omega)
    have := lb 8 2 (by omega); have := lb 5 1 (by omega); have := lb 3 1 (by omega); omega
  else if h5 : 3 * r < 2 * d then
    have := ub 6 3 (by omega); have := ub 4 2 (by omega)
    have := lb 8 4 (by omega); have := lb 5 2 (by omega); have := lb 3 1 (by omega); omega
  else if h6 : 4 * r < 3 * d then
    have := ub 6 4 (by omega); have := ub 4 2 (by omega)
    have := lb 8 5 (by omega); have := lb 5 3 (by omega); have := lb 3 2 (by omega); omega
  else if h7 : 6 * r < 5 * d then
    have := ub 6 4 (by omega); have := ub 4 3 (by omega)
    have := lb 8 6 (by omega); have := lb 5 3 (by omega); have := lb 3 2 (by omega); omega
  else
    have := ub 6 5 (by omega); have := ub 4 3 (by omega)
    have := lb 8 6 (by omega); have := lb 5 4 (by omega); have := lb 3 2 (by omega); omega

private lemma den_dvd_num (m : ℕ) : den m ∣ num m := by
  rw [← Nat.factorization_prime_le_iff_dvd (by unfold den; positivity) (by unfold num; positivity)]
  intro q hq
  have : Fact q.Prime := ⟨hq⟩
  set b := Nat.log q (8 * m) + 1
  have hb : ∀ k : ℕ, k ≤ 8 * m → Nat.log q k < b := fun k hk =>
    (Nat.log_mono_right hk).trans_lt (Nat.lt_succ_self _)
  have hden : (den m).factorization q =
      ∑ i ∈ Finset.Ico 1 b, ((6 * m) / q ^ i + 2 * ((4 * m) / q ^ i) + 2 * (m / q ^ i)) := by
    unfold den
    rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_pow, Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Nat.factorization_def _ hq]
    rw [padicValNat_factorial (hb _ (by omega)),
      padicValNat_factorial (hb _ (by omega)),
      padicValNat_factorial (hb _ (by omega)),
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hnum : (num m).factorization q =
      ∑ i ∈ Finset.Ico 1 b, ((8 * m) / q ^ i + (5 * m) / q ^ i + (3 * m) / q ^ i) := by
    unfold num
    rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity)]
    simp only [Finsupp.add_apply, Nat.factorization_def _ hq]
    rw [padicValNat_factorial (hb _ (by omega)),
      padicValNat_factorial (hb _ (by omega)),
      padicValNat_factorial (hb _ (by omega)),
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hden, hnum]
  exact Finset.sum_le_sum fun i _ => div_sum_le m (q ^ i) (pow_pos hq.pos i)

private lemma a_mul_den (m : ℕ) :
    OMA.S_oeis_a364305.a m * (den m : ℤ) = (num m : ℤ) := by
  change ((num m / den m : ℕ) : ℤ) * (den m : ℤ) = (num m : ℤ)
  exact_mod_cast Nat.div_mul_cancel (den_dvd_num m)

private lemma prod_Icc_eq_factorial (n : ℕ) : ∏ j ∈ Finset.Icc 1 n, j = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.factorial_succ, ← ih, Finset.prod_Icc_succ_top (by omega), mul_comm]

private lemma factorial_mul_prime {p : ℕ} (hp : p.Prime) (L : ℕ) :
    (L * p).factorial = p ^ L * L.factorial * unitFact p (L * p) := by
  rw [← prod_Icc_eq_factorial (L * p),
    ← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (L * p)) (fun j => p ∣ j)]
  unfold unitFact
  congr 1
  have hfilt : (Finset.Icc 1 (L * p)).filter (fun j => p ∣ j) =
      (Finset.Icc 1 L).image (fun i => p * i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hj1, hj2⟩, i, rfl⟩
      refine ⟨i, ⟨?_, ?_⟩, rfl⟩
      · rcases eq_or_ne i 0 with rfl | hi
        · simp at hj1
        · omega
      · exact Nat.le_of_mul_le_mul_left (by linarith) hp.pos
    · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, i, rfl⟩
      · nlinarith [hp.pos]
      · nlinarith [hp.pos]
  rw [hfilt, Finset.prod_image (fun a _ b _ h => mul_left_cancel₀ hp.ne_zero h),
    Finset.prod_mul_distrib, prod_Icc_eq_factorial, Finset.prod_const, Nat.card_Icc]
  have hcard : L + 1 - 1 = L := by omega
  rw [hcard]

private lemma coprime_unitFact {p : ℕ} (hp : p.Prime) (M : ℕ) :
    Nat.Coprime p (unitFact p M) := by
  unfold unitFact
  exact Nat.Coprime.prod_right fun j hj =>
    hp.coprime_iff_not_dvd.mpr (Finset.mem_filter.mp hj).2

private lemma a_cross_mul {p n k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    OMA.S_oeis_a364305.a (n * p ^ k) *
      ((unitFact p (6 * n * p ^ k) : ℤ) * unitFact p (4 * n * p ^ k) ^ 2 *
        unitFact p (n * p ^ k) ^ 2) =
    OMA.S_oeis_a364305.a (n * p ^ (k - 1)) *
      ((unitFact p (8 * n * p ^ k) : ℤ) * unitFact p (5 * n * p ^ k) *
        unitFact p (3 * n * p ^ k)) := by
  set m := n * p ^ (k - 1)
  have hpk : p ^ k = p ^ (k - 1) * p := by
    conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ]
  have hscale : ∀ c : ℕ,
      (c * (n * p ^ k)).factorial =
        p ^ (c * m) * (c * m).factorial * unitFact p (c * n * p ^ k) := by
    intro c
    have hc1 : c * (n * p ^ k) = (c * m) * p := by dsimp [m]; rw [hpk]; ring
    have hc2 : c * n * p ^ k = (c * m) * p := by
      calc c * n * p ^ k = c * (n * p ^ k) := by rw [mul_assoc]
      _ = (c * m) * p := hc1
    rw [hc1, hc2, factorial_mul_prime hp (c * m)]
  have hscale1 : (n * p ^ k).factorial = p ^ m * m.factorial * unitFact p (n * p ^ k) := by
    simpa [one_mul] using hscale 1
  have hnum_split : num (n * p ^ k) =
      p ^ (16 * m) * num m *
        (unitFact p (8 * n * p ^ k) * unitFact p (5 * n * p ^ k) * unitFact p (3 * n * p ^ k)) := by
    unfold num
    rw [hscale 8, hscale 5, hscale 3]
    have hexp : p ^ (8 * m) * p ^ (5 * m) * p ^ (3 * m) = p ^ (16 * m) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    calc
      (p ^ (8 * m) * (8 * m).factorial * unitFact p (8 * n * p ^ k)) *
          (p ^ (5 * m) * (5 * m).factorial * unitFact p (5 * n * p ^ k)) *
          (p ^ (3 * m) * (3 * m).factorial * unitFact p (3 * n * p ^ k))
        = (p ^ (8 * m) * p ^ (5 * m) * p ^ (3 * m)) *
            ((8 * m).factorial * (5 * m).factorial * (3 * m).factorial) *
            (unitFact p (8 * n * p ^ k) * unitFact p (5 * n * p ^ k) *
              unitFact p (3 * n * p ^ k)) := by ring
      _ = _ := by rw [hexp]
  have hden_split : den (n * p ^ k) =
      p ^ (16 * m) * den m *
        (unitFact p (6 * n * p ^ k) * unitFact p (4 * n * p ^ k) ^ 2 *
          unitFact p (n * p ^ k) ^ 2) := by
    unfold den
    rw [hscale 6, hscale 4, hscale1]
    have hexp : p ^ (6 * m) * (p ^ (4 * m)) ^ 2 * (p ^ m) ^ 2 = p ^ (16 * m) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega
    calc
      (p ^ (6 * m) * (6 * m).factorial * unitFact p (6 * n * p ^ k)) *
          (p ^ (4 * m) * (4 * m).factorial * unitFact p (4 * n * p ^ k)) ^ 2 *
          (p ^ m * m.factorial * unitFact p (n * p ^ k)) ^ 2
        = (p ^ (6 * m) * (p ^ (4 * m)) ^ 2 * (p ^ m) ^ 2) *
            ((6 * m).factorial * (4 * m).factorial ^ 2 * m.factorial ^ 2) *
            (unitFact p (6 * n * p ^ k) * unitFact p (4 * n * p ^ k) ^ 2 *
              unitFact p (n * p ^ k) ^ 2) := by ring
      _ = _ := by rw [hexp]
  have hC_pos : 0 < p ^ (16 * m) * den m := by
    have hp_pos := hp.pos
    unfold den
    positivity
  have hC_ne : ((p ^ (16 * m) * den m : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hC_pos.ne'
  apply mul_right_cancel₀ hC_ne
  have h1 := a_mul_den (n * p ^ k)
  have h2 := a_mul_den m
  rw [hden_split, hnum_split] at h1
  push_cast at h1 ⊢
  linear_combination h1 - (p : ℤ) ^ (16 * m) *
    ((unitFact p (8 * n * p ^ k) : ℤ) * unitFact p (5 * n * p ^ k) * unitFact p (3 * n * p ^ k)) *
    h2

private lemma dvd_sub_a_of_unitFact {p n k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (h : ((p : ℤ) ^ (3 * k)) ∣
      ((unitFact p (8 * n * p ^ k) : ℤ) * unitFact p (5 * n * p ^ k) * unitFact p (3 * n * p ^ k)) -
      ((unitFact p (6 * n * p ^ k) : ℤ) * unitFact p (4 * n * p ^ k) ^ 2 *
        unitFact p (n * p ^ k) ^ 2)) :
    ((p : ℤ) ^ (3 * k) ∣ OMA.S_oeis_a364305.a (n * p ^ k) - OMA.S_oeis_a364305.a (n * p ^ (k - 1))) := by
  set P_num : ℤ :=
    (unitFact p (8 * n * p ^ k) : ℤ) * unitFact p (5 * n * p ^ k) * unitFact p (3 * n * p ^ k)
  set P_den : ℤ :=
    (unitFact p (6 * n * p ^ k) : ℤ) * unitFact p (4 * n * p ^ k) ^ 2 * unitFact p (n * p ^ k) ^ 2
  have hcross : OMA.S_oeis_a364305.a (n * p ^ k) * P_den =
      OMA.S_oeis_a364305.a (n * p ^ (k - 1)) * P_num :=
    a_cross_mul hp hk
  have hident :
      (OMA.S_oeis_a364305.a (n * p ^ k) - OMA.S_oeis_a364305.a (n * p ^ (k - 1))) * P_den =
        OMA.S_oeis_a364305.a (n * p ^ (k - 1)) * (P_num - P_den) := by
    linear_combination hcross
  have hdvd_prod : (p : ℤ) ^ (3 * k) ∣
      (OMA.S_oeis_a364305.a (n * p ^ k) - OMA.S_oeis_a364305.a (n * p ^ (k - 1))) * P_den := by
    rw [hident]
    exact dvd_mul_of_dvd_right h _
  have hcop_nat : Nat.Coprime (p ^ (3 * k))
      (unitFact p (6 * n * p ^ k) * unitFact p (4 * n * p ^ k) ^ 2 * unitFact p (n * p ^ k) ^ 2) :=
    (((coprime_unitFact hp _).mul_right ((coprime_unitFact hp _).pow_right 2)).mul_right
      ((coprime_unitFact hp _).pow_right 2)).pow_left (3 * k)
  have hcop : IsCoprime ((p : ℤ) ^ (3 * k)) P_den := by
    simpa [P_den] using hcop_nat.isCoprime
  exact hcop.dvd_of_dvd_mul_right hdvd_prod

private lemma prod_add_of_sq_eq_zero {ι R : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset ι) (f : ι → R) (z : R) (hz : z * z = 0) :
    (∏ i ∈ s, (f i + z)) = (∏ i ∈ s, f i) + z * ∑ i ∈ s, ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.prod_insert ha, Finset.sum_insert ha,
      Finset.erase_insert ha]
    have hsum :
        ∑ i ∈ s, ∏ j ∈ (insert a s).erase i, f j =
          f a * ∑ i ∈ s, ∏ j ∈ s.erase i, f j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne hia.symm,
        Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    rw [hsum]
    linear_combination (∑ i ∈ s, ∏ j ∈ s.erase i, f j) * hz

private lemma pow_odd_mod_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (k : ℕ) :
    p ^ k % 2 = 1 := by
  have hp_mod : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with rfl | h
    · omega
    · exact h
  induction k with
  | zero => rfl
  | succ j ih => rw [pow_succ, Nat.mul_mod, ih, hp_mod]

private lemma filter_Icc_eq_half_union_image {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    (Finset.Icc 1 (p ^ k - 1)).filter (fun r => ¬ p ∣ r) =
      (Finset.Icc 1 ((p ^ k - 1) / 2)).filter (fun r => ¬ p ∣ r) ∪
        ((Finset.Icc 1 ((p ^ k - 1) / 2)).filter (fun r => ¬ p ∣ r)).image (fun r => p ^ k - r) := by
  have hpk5 : 5 ≤ p ^ k :=
    le_trans (by simpa using hp5 : 5 ≤ p ^ 1) (Nat.pow_le_pow_right (by omega) hk)
  have hmod : p ^ k % 2 = 1 := pow_odd_mod_two hp hp5 k
  obtain ⟨q_pk, hq_pk⟩ := dvd_pow_self p (by omega : k ≠ 0)
  ext x
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hx1, hx2⟩, hxp⟩
    by_cases hxhalf : x ≤ (p ^ k - 1) / 2
    · exact Or.inl ⟨⟨hx1, hxhalf⟩, hxp⟩
    · refine Or.inr ⟨p ^ k - x, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      rintro ⟨q, hq⟩
      apply hxp
      refine ⟨q_pk - q, ?_⟩
      rw [Nat.mul_sub_left_distrib, ← hq_pk, ← hq]
      omega
  · rintro (⟨⟨hx1, hx2⟩, hxp⟩ | ⟨r, ⟨⟨hr1, hr2⟩, hrp⟩, rfl⟩)
    · exact ⟨⟨hx1, by omega⟩, hxp⟩
    · refine ⟨⟨by omega, by omega⟩, ?_⟩
      rintro ⟨q, hq⟩
      apply hrp
      refine ⟨q_pk - q, ?_⟩
      rw [Nat.mul_sub_left_distrib, ← hq_pk, ← hq]
      omega

private lemma disjoint_half_image_sub {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    Disjoint ((Finset.Icc 1 ((p ^ k - 1) / 2)).filter (fun r => ¬ p ∣ r))
      (((Finset.Icc 1 ((p ^ k - 1) / 2)).filter (fun r => ¬ p ∣ r)).image (fun r => p ^ k - r)) := by
  have hpk5 : 5 ≤ p ^ k :=
    le_trans (by simpa using hp5 : 5 ≤ p ^ 1) (Nat.pow_le_pow_right (by omega) hk)
  have hmod : p ^ k % 2 = 1 := pow_odd_mod_two hp hp5 k
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image] at hx1 hx2
  rcases hx2 with ⟨r, ⟨⟨hr1, hr2⟩, _⟩, rfl⟩
  omega

private lemma dvd_sum_erase_prod_half {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    ((p : ℤ) ^ k) ∣
      ∑ r ∈ (Finset.Icc 1 ((p ^ k - 1) / 2)).filter (fun r => ¬ p ∣ r),
        ∏ s ∈ ((Finset.Icc 1 ((p ^ k - 1) / 2)).filter (fun r => ¬ p ∣ r)).erase r,
          ((s : ℤ) * ((p : ℤ) ^ k - s)) := by
  let R_half := (Finset.Icc 1 ((p ^ k - 1) / 2)).filter (fun r => ¬ p ∣ r)
  change ((p : ℤ) ^ k) ∣ ∑ r ∈ R_half, ∏ s ∈ R_half.erase r, ((s : ℤ) * ((p : ℤ) ^ k - s))
  have hpk5 : 5 ≤ p ^ k :=
    le_trans (by simpa using hp5 : 5 ≤ p ^ 1) (Nat.pow_le_pow_right (by omega) hk)
  have : NeZero (p ^ k) := ⟨by omega⟩
  suffices hdvd :
      (((p ^ k : ℕ) : ℤ)) ∣ ∑ r ∈ R_half, ∏ s ∈ R_half.erase r, ((s : ℤ) * ((p : ℤ) ^ k - s)) by
    simpa only [Nat.cast_pow] using hdvd
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  let A : ℕ → ZMod (p ^ k) := fun s => - (s : ZMod (p ^ k)) ^ 2
  have hcast :
      ((∑ r ∈ R_half, ∏ s ∈ R_half.erase r, ((s : ℤ) * ((p : ℤ) ^ k - s)) : ℤ) : ZMod (p ^ k)) =
        ∑ r ∈ R_half, ∏ s ∈ R_half.erase r, A s := by
    push_cast
    refine Finset.sum_congr rfl fun r _ => Finset.prod_congr rfl fun s _ => ?_
    have hpz : ((p : ZMod (p ^ k)) ^ k) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [hpz]
    dsimp [A]
    ring
  rw [hcast]
  have hinv_of_mem : ∀ x : ℕ, x < p ^ k → ¬ p ∣ x →
      (x : ZMod (p ^ k)) * (x : ZMod (p ^ k))⁻¹ = 1 := by
    intro x hlt hxp
    have hcop : Nat.Coprime x (p ^ k) := ((hp.coprime_iff_not_dvd.mpr hxp).symm).pow_right k
    rw [ZMod.mul_inv_eq_gcd, ZMod.val_natCast_of_lt hlt, hcop.gcd_eq_one, Nat.cast_one]
  have hfactor :
      ∑ r ∈ R_half, ∏ s ∈ R_half.erase r, A s =
        (- ∏ s ∈ R_half, A s) * ∑ r ∈ R_half, ((r : ZMod (p ^ k))⁻¹) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr_mem := hr
    simp only [R_half, Finset.mem_filter, Finset.mem_Icc] at hr_mem
    have hinv : (r : ZMod (p ^ k)) * (r : ZMod (p ^ k))⁻¹ = 1 :=
      hinv_of_mem r (by omega) hr_mem.2
    calc ∏ s ∈ R_half.erase r, A s
        = (1 : ZMod (p ^ k)) ^ 2 * ∏ s ∈ R_half.erase r, A s := by ring
      _ = ((r : ZMod (p ^ k)) * (r : ZMod (p ^ k))⁻¹) ^ 2 * ∏ s ∈ R_half.erase r, A s := by
          rw [hinv]
      _ = - ((r : ZMod (p ^ k))⁻¹) ^ 2 * (A r * ∏ s ∈ R_half.erase r, A s) := by
          dsimp [A]; ring
      _ = (- ∏ s ∈ R_half, A s) * ((r : ZMod (p ^ k))⁻¹) ^ 2 := by
          rw [Finset.mul_prod_erase R_half A hr]; ring
  rw [hfactor]
  suffices hzero : ∑ r ∈ R_half, ((r : ZMod (p ^ k))⁻¹) ^ 2 = 0 by
    rw [hzero, mul_zero]
  let R_full := (Finset.Icc 1 (p ^ k - 1)).filter (fun r => ¬ p ∣ r)
  let g : ℕ → ZMod (p ^ k) := fun x => ((x : ZMod (p ^ k))⁻¹) ^ 2
  have hdouble : ∑ x ∈ R_full, g x = 2 * ∑ r ∈ R_half, g r := by
    have hunion : R_full = R_half ∪ R_half.image (fun r => p ^ k - r) :=
      filter_Icc_eq_half_union_image hp hp5 hk
    have hdisj : Disjoint R_half (R_half.image (fun r => p ^ k - r)) :=
      disjoint_half_image_sub hp hp5 hk
    rw [hunion, Finset.sum_union hdisj]
    have hinj : Set.InjOn (fun r => p ^ k - r) R_half := by
      intro r₁ hr₁ r₂ hr₂ heq
      simp only [R_half, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hr₁ hr₂
      dsimp at heq
      omega
    rw [Finset.sum_image hinj]
    have hsymm : ∑ r ∈ R_half, g (p ^ k - r) = ∑ r ∈ R_half, g r := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr_full : p ^ k - r ∈ R_full := by
        rw [hunion]
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hr)
      simp only [R_half, R_full, Finset.mem_filter, Finset.mem_Icc] at hr hr_full
      have hinv1 : (r : ZMod (p ^ k)) * (r : ZMod (p ^ k))⁻¹ = 1 :=
        hinv_of_mem r (by omega) hr.2
      have hinv2 : ((p ^ k - r : ℕ) : ZMod (p ^ k)) * ((p ^ k - r : ℕ) : ZMod (p ^ k))⁻¹ = 1 :=
        hinv_of_mem (p ^ k - r) (by omega) hr_full.2
      have hsub_cast : ((p ^ k - r : ℕ) : ZMod (p ^ k)) = - (r : ZMod (p ^ k)) := by
        have hadd : ((p ^ k - r : ℕ) : ZMod (p ^ k)) + (r : ZMod (p ^ k)) = 0 := by
          rw [← Nat.cast_add, Nat.sub_add_cancel (by omega), ZMod.natCast_self]
        linear_combination hadd
      have hneg_inv : ((p ^ k - r : ℕ) : ZMod (p ^ k))⁻¹ = - (r : ZMod (p ^ k))⁻¹ := by
        calc ((p ^ k - r : ℕ) : ZMod (p ^ k))⁻¹
            = ((p ^ k - r : ℕ) : ZMod (p ^ k))⁻¹ *
                ((r : ZMod (p ^ k)) * (r : ZMod (p ^ k))⁻¹) := by rw [hinv1, mul_one]
          _ = (((p ^ k - r : ℕ) : ZMod (p ^ k)) * ((p ^ k - r : ℕ) : ZMod (p ^ k))⁻¹) *
                (- (r : ZMod (p ^ k))⁻¹) := by rw [hsub_cast]; ring
          _ = - (r : ZMod (p ^ k))⁻¹ := by rw [hinv2, one_mul]
      dsimp [g]
      rw [hneg_inv]
      ring
    rw [hsymm, two_mul]
  have hfull_eq_units :
      R_full = Finset.univ.image (fun v : (ZMod (p ^ k))ˣ => (v : ZMod (p ^ k)).val) := by
    ext x
    simp only [R_full, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hxp⟩
      have hcop : Nat.Coprime x (p ^ k) := ((hp.coprime_iff_not_dvd.mpr hxp).symm).pow_right k
      refine ⟨ZMod.unitOfCoprime x hcop, ?_⟩
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt (by omega)]
    · rintro ⟨v, rfl⟩
      have hcop : Nat.Coprime (v : ZMod (p ^ k)).val (p ^ k) := ZMod.val_coe_unit_coprime v
      have hnotdvd : ¬ p ∣ (v : ZMod (p ^ k)).val := by
        intro hpd
        have h1 : p ∣ 1 := by
          rw [← hcop.gcd_eq_one]
          exact Nat.dvd_gcd hpd (dvd_pow_self p (by omega))
        exact hp.not_dvd_one h1
      have hpos : 1 ≤ (v : ZMod (p ^ k)).val :=
        Nat.pos_of_ne_zero fun h0 => hnotdvd (h0 ▸ dvd_zero p)
      have hlt : (v : ZMod (p ^ k)).val < p ^ k := ZMod.val_lt _
      exact ⟨⟨hpos, by omega⟩, hnotdvd⟩
  have hsum_units :
      ∑ x ∈ R_full, g x = ∑ v : (ZMod (p ^ k))ˣ, ((v : ZMod (p ^ k))) ^ 2 := by
    rw [hfull_eq_units]
    have hinj_val :
        Set.InjOn (fun v : (ZMod (p ^ k))ˣ => (v : ZMod (p ^ k)).val)
          ↑(Finset.univ : Finset (ZMod (p ^ k))ˣ) := by
      intro v₁ _ v₂ _ heq
      exact Units.ext (ZMod.val_injective (p ^ k) heq)
    rw [Finset.sum_image hinj_val]
    have hcongr :
        ∑ v : (ZMod (p ^ k))ˣ, g (v : ZMod (p ^ k)).val =
          ∑ v : (ZMod (p ^ k))ˣ, (((v⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) ^ 2 := by
      refine Finset.sum_congr rfl fun v _ => ?_
      dsimp [g]
      rw [ZMod.natCast_zmod_val]
      have hcop : Nat.Coprime (v : ZMod (p ^ k)).val (p ^ k) := ZMod.val_coe_unit_coprime v
      have hv_inv : (v : ZMod (p ^ k)) * (v : ZMod (p ^ k))⁻¹ = 1 := by
        rw [ZMod.mul_inv_eq_gcd, hcop.gcd_eq_one, Nat.cast_one]
      have hinv_eq : (v : ZMod (p ^ k))⁻¹ = ((v⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) := by
        calc (v : ZMod (p ^ k))⁻¹
            = (((v⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * (v : ZMod (p ^ k))) *
                (v : ZMod (p ^ k))⁻¹ := by rw [Units.inv_mul, one_mul]
          _ = ((v⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) *
                ((v : ZMod (p ^ k)) * (v : ZMod (p ^ k))⁻¹) := by ring
          _ = ((v⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) := by rw [hv_inv, mul_one]
      rw [hinv_eq]
    rw [hcongr]
    exact Fintype.sum_equiv (Equiv.inv (ZMod (p ^ k))ˣ) _ _ fun _ => rfl
  let S : ZMod (p ^ k) := ∑ v : (ZMod (p ^ k))ˣ, ((v : ZMod (p ^ k))) ^ 2
  have h2cop : Nat.Coprime 2 (p ^ k) :=
    ((hp.coprime_iff_not_dvd.mpr fun h => by
      have := Nat.le_of_dvd (by omega) h; omega).symm).pow_right k
  have h3cop : Nat.Coprime 3 (p ^ k) :=
    ((hp.coprime_iff_not_dvd.mpr fun h => by
      have := Nat.le_of_dvd (by omega) h; omega).symm).pow_right k
  let u2 : (ZMod (p ^ k))ˣ := ZMod.unitOfCoprime 2 h2cop
  let u3 : (ZMod (p ^ k))ˣ := ZMod.unitOfCoprime 3 h3cop
  have hu2 : (u2 : ZMod (p ^ k)) = 2 := by simp [u2]
  have hu3 : (u3 : ZMod (p ^ k)) = 3 := by simp [u3]
  have h4S : 4 * S = S := by
    have heq :
        ∑ v : (ZMod (p ^ k))ˣ, (((u2 * v : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) ^ 2 = S :=
      Fintype.sum_equiv (Equiv.mulLeft u2) _ _ fun _ => rfl
    have h4 :
        ∑ v : (ZMod (p ^ k))ˣ, (((u2 * v : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) ^ 2 = 4 * S := by
      dsimp [S]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hu2]
      ring
    rw [← h4, heq]
  have h3S : (u3 : ZMod (p ^ k)) * S = 0 := by
    rw [hu3]
    linear_combination h4S
  have hS0 : S = 0 := by
    calc S = (((u3⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * (u3 : ZMod (p ^ k))) * S := by
          rw [Units.inv_mul, one_mul]
      _ = ((u3⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * ((u3 : ZMod (p ^ k)) * S) := by ring
      _ = 0 := by rw [h3S, mul_zero]
  have h2zero : (u2 : ZMod (p ^ k)) * ∑ r ∈ R_half, g r = 0 := by
    rw [hu2, ← hdouble, hsum_units]
    exact hS0
  calc ∑ r ∈ R_half, g r
      = (((u2⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * (u2 : ZMod (p ^ k))) *
          ∑ r ∈ R_half, g r := by rw [Units.inv_mul, one_mul]
    _ = ((u2⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) *
          ((u2 : ZMod (p ^ k)) * ∑ r ∈ R_half, g r) := by ring
    _ = 0 := by rw [h2zero, mul_zero]

private def block (p k t : ℕ) : ℕ :=
  ∏ r ∈ (Finset.Icc 1 (p ^ k - 1)).filter (fun r => ¬ p ∣ r), (t * p ^ k + r)

private lemma block_cast_int {p k t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    (block p k t : ℤ) =
      ∏ r ∈ (Finset.Icc 1 ((p ^ k - 1) / 2)).filter (fun r => ¬ p ∣ r),
        ((r : ℤ) * ((p : ℤ) ^ k - r) + (t : ℤ) * (t + 1) * (p : ℤ) ^ (2 * k)) := by
  let R_half := (Finset.Icc 1 ((p ^ k - 1) / 2)).filter (fun r => ¬ p ∣ r)
  have hpk5 : 5 ≤ p ^ k :=
    le_trans (by simpa using hp5 : 5 ≤ p ^ 1) (Nat.pow_le_pow_right (by omega) hk)
  have hunion : (Finset.Icc 1 (p ^ k - 1)).filter (fun r => ¬ p ∣ r) =
      R_half ∪ R_half.image (fun r => p ^ k - r) :=
    filter_Icc_eq_half_union_image hp hp5 hk
  have hdisj : Disjoint R_half (R_half.image (fun r => p ^ k - r)) :=
    disjoint_half_image_sub hp hp5 hk
  have hinj : Set.InjOn (fun r => p ^ k - r) R_half := by
    intro r₁ hr₁ r₂ hr₂ heq
    dsimp only at heq
    simp only [R_half, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hr₁ hr₂
    omega
  have hprod :
      block p k t =
        ∏ r ∈ R_half, ((t * p ^ k + r) * (t * p ^ k + (p ^ k - r))) := by
    unfold block
    rw [hunion, Finset.prod_union hdisj, Finset.prod_image hinj, ← Finset.prod_mul_distrib]
  rw [hprod, Nat.cast_prod]
  refine Finset.prod_congr rfl fun r hr => ?_
  simp only [Finset.mem_filter, Finset.mem_Icc] at hr
  have hrle : r ≤ p ^ k := by omega
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub hrle, Nat.cast_pow]
  have hpow : ((p : ℤ) ^ k) ^ 2 = (p : ℤ) ^ (2 * k) := by
    rw [← pow_mul, mul_comm]
  linear_combination (t : ℤ) * ((t : ℤ) + 1) * hpow

private lemma block_mod_eq {p k t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    ((p : ℤ) ^ (3 * k)) ∣ (block p k t : ℤ) - (block p k 0 : ℤ) := by
  let R_half := (Finset.Icc 1 ((p ^ k - 1) / 2)).filter (fun r => ¬ p ∣ r)
  let N : ℕ := p ^ (3 * k)
  let g : ℕ → ℤ := fun r => (r : ℤ) * ((p : ℤ) ^ k - r)
  let w : ℤ := (t : ℤ) * (t + 1) * (p : ℤ) ^ (2 * k)
  let f : ℕ → ZMod N := fun r => (g r : ZMod N)
  let z : ZMod N := (w : ZMod N)
  have hz : z * z = 0 := by
    have hzz : z * z = ((w * w : ℤ) : ZMod N) := by simp [z]
    rw [hzz, ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [N]
    have hww : w * w = ((t : ℤ) * (t + 1)) ^ 2 * (p : ℤ) ^ (4 * k) := by
      dsimp [w]
      have hp4 : ((p : ℤ) ^ (2 * k)) ^ 2 = (p : ℤ) ^ (4 * k) := by
        rw [← pow_mul]
        congr 1
        omega
      linear_combination ((t : ℤ) * ((t : ℤ) + 1)) ^ 2 * hp4
    rw [hww]
    exact dvd_mul_of_dvd_right (pow_dvd_pow (p : ℤ) (by omega)) _
  have hbt : ((block p k t : ℤ) : ZMod N) = ∏ r ∈ R_half, (f r + z) := by
    rw [block_cast_int hp hp5 hk]
    push_cast [R_half, f, g, z, w]
    rfl
  have hb0 : ((block p k 0 : ℤ) : ZMod N) = ∏ r ∈ R_half, f r := by
    rw [block_cast_int hp hp5 hk]
    simp [R_half, f, g]
  have hterm : z * (∑ r ∈ R_half, ∏ s ∈ R_half.erase r, f s) = 0 := by
    let S : ℤ := ∑ r ∈ R_half, ∏ s ∈ R_half.erase r, g s
    have hcast :
        z * (∑ r ∈ R_half, ∏ s ∈ R_half.erase r, f s) = ((w * S : ℤ) : ZMod N) := by
      simp [z, f, S]
    rw [hcast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [N]
    have hw_dvd : ((p : ℤ) ^ (2 * k)) ∣ w := ⟨(t : ℤ) * (t + 1), by dsimp [w]; ring⟩
    have hfoil : ((p : ℤ) ^ k) ∣ S := dvd_sum_erase_prod_half hp hp5 hk
    have hmul : ((p : ℤ) ^ (2 * k) * (p : ℤ) ^ k) ∣ w * S := mul_dvd_mul hw_dvd hfoil
    have hp3 : (p : ℤ) ^ (2 * k) * (p : ℤ) ^ k = (p : ℤ) ^ (3 * k) := by
      rw [← pow_add]
      congr 1
      omega
    rwa [hp3] at hmul
  have hexp := prod_add_of_sq_eq_zero R_half f z hz
  rw [hterm, add_zero] at hexp
  have heq : ((block p k t : ℤ) : ZMod N) = ((block p k 0 : ℤ) : ZMod N) := by
    rw [hbt, hb0, hexp]
  have hsub : (((block p k t : ℤ) - (block p k 0 : ℤ) : ℤ) : ZMod N) = 0 := by
    rw [Int.cast_sub, heq, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hsub
  simpa [N] using hsub

private lemma unitFact_mul_pow_eq_prod_block {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (M : ℕ) :
    unitFact p (M * p ^ k) = ∏ t ∈ Finset.range M, block p k t := by
  have hpdvd : p ∣ p ^ k := dvd_pow_self p (by omega)
  have hpk1 : 1 ≤ p ^ k := Nat.one_le_pow k p hp.pos
  induction M with
  | zero =>
    simp [unitFact]
  | succ M ih =>
    rw [Finset.prod_range_succ, ← ih]
    unfold unitFact block
    have hsplit :
        (Finset.Icc 1 ((M + 1) * p ^ k)).filter (fun j => ¬ p ∣ j) =
          (Finset.Icc 1 (M * p ^ k)).filter (fun j => ¬ p ∣ j) ∪
            ((Finset.Icc 1 (p ^ k - 1)).filter (fun r => ¬ p ∣ r)).image
              (fun r => M * p ^ k + r) := by
      have hm1 : (M + 1) * p ^ k = M * p ^ k + p ^ k := Nat.succ_mul M (p ^ k)
      ext j
      simp only [hm1, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hj1, hj2⟩, hndvd⟩
        rcases le_or_gt j (M * p ^ k) with hle | hgt
        · exact Or.inl ⟨⟨hj1, hle⟩, hndvd⟩
        · have hjne : j ≠ M * p ^ k + p ^ k := by
            rintro rfl
            exact hndvd (dvd_add (dvd_mul_of_dvd_right hpdvd M) hpdvd)
          refine Or.inr ⟨j - M * p ^ k, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
          intro hd
          apply hndvd
          have heq : M * p ^ k + (j - M * p ^ k) = j := by omega
          rw [← heq]
          exact dvd_add (dvd_mul_of_dvd_right hpdvd M) hd
      · rintro (⟨⟨hj1, hj2⟩, hndvd⟩ | ⟨r, ⟨⟨hr1, hr2⟩, hrndvd⟩, rfl⟩)
        · exact ⟨⟨hj1, by omega⟩, hndvd⟩
        · refine ⟨⟨by omega, by omega⟩, ?_⟩
          intro hd
          apply hrndvd
          exact (Nat.dvd_add_right (dvd_mul_of_dvd_right hpdvd M)).mp hd
    have hdisj :
        Disjoint ((Finset.Icc 1 (M * p ^ k)).filter (fun j => ¬ p ∣ j))
          (((Finset.Icc 1 (p ^ k - 1)).filter (fun r => ¬ p ∣ r)).image
            (fun r => M * p ^ k + r)) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image] at hj1 hj2
      rcases hj2 with ⟨r, hr, rfl⟩
      omega
    have hinj :
        Set.InjOn (fun r => M * p ^ k + r)
          ((Finset.Icc 1 (p ^ k - 1)).filter (fun r => ¬ p ∣ r)) := by
      intro r₁ _ r₂ _ heq
      dsimp only at heq
      omega
    rw [hsplit, Finset.prod_union hdisj, Finset.prod_image hinj]

private lemma unitFact_mul_pow_mod {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) (M : ℕ) :
    ((p : ℤ) ^ (3 * k)) ∣ (unitFact p (M * p ^ k) : ℤ) - (unitFact p (p ^ k) : ℤ) ^ M := by
  let N : ℕ := p ^ (3 * k)
  have hb0 : block p k 0 = unitFact p (p ^ k) := by
    have h1 := unitFact_mul_pow_eq_prod_block hp hk 1
    simpa using h1.symm
  have hbt : ∀ t : ℕ, ((block p k t : ℕ) : ZMod N) = ((unitFact p (p ^ k) : ℕ) : ZMod N) := by
    intro t
    have hd := block_mod_eq (t := t) hp hp5 hk
    have hz : (((block p k t : ℤ) - (block p k 0 : ℤ) : ℤ) : ZMod N) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      simpa [N] using hd
    rw [hb0, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, sub_eq_zero] at hz
    exact hz
  have hprod :
      ((unitFact p (M * p ^ k) : ℕ) : ZMod N) = ((unitFact p (p ^ k) : ℕ) : ZMod N) ^ M := by
    rw [unitFact_mul_pow_eq_prod_block hp hk M, Nat.cast_prod]
    calc
      ∏ t ∈ Finset.range M, ((block p k t : ℕ) : ZMod N) =
          ∏ _t ∈ Finset.range M, ((unitFact p (p ^ k) : ℕ) : ZMod N) :=
        Finset.prod_congr rfl fun t _ => hbt t
      _ = ((unitFact p (p ^ k) : ℕ) : ZMod N) ^ M := by
        rw [Finset.prod_const, Finset.card_range]
  have hsub :
      (((unitFact p (M * p ^ k) : ℤ) - (unitFact p (p ^ k) : ℤ) ^ M : ℤ) : ZMod N) = 0 := by
    push_cast
    rw [hprod, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hsub
  simpa [N] using hsub

private lemma dvd_P_num_sub_P_den {p n k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    ((p : ℤ) ^ (3 * k)) ∣
      ((unitFact p (8 * n * p ^ k) : ℤ) * unitFact p (5 * n * p ^ k) * unitFact p (3 * n * p ^ k)) -
      ((unitFact p (6 * n * p ^ k) : ℤ) * unitFact p (4 * n * p ^ k) ^ 2 * unitFact p (n * p ^ k) ^ 2) := by
  let N : ℕ := p ^ (3 * k)
  let u : ZMod N := ((unitFact p (p ^ k) : ℕ) : ZMod N)
  have hu : ∀ M : ℕ, ((unitFact p (M * p ^ k) : ℕ) : ZMod N) = u ^ M := by
    intro M
    have hd := unitFact_mul_pow_mod hp hp5 hk M
    have hz :
        (((unitFact p (M * p ^ k) : ℤ) - (unitFact p (p ^ k) : ℤ) ^ M : ℤ) : ZMod N) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      simpa [N] using hd
    push_cast at hz
    exact sub_eq_zero.mp hz
  have hnum :
      (((unitFact p (8 * n * p ^ k) : ℤ) * unitFact p (5 * n * p ^ k) * unitFact p (3 * n * p ^ k) : ℤ) : ZMod N) =
        u ^ (16 * n) := by
    push_cast
    rw [hu (8 * n), hu (5 * n), hu (3 * n), ← pow_add, ← pow_add]
    congr 1
    omega
  have hden :
      (((unitFact p (6 * n * p ^ k) : ℤ) * unitFact p (4 * n * p ^ k) ^ 2 * unitFact p (n * p ^ k) ^ 2 : ℤ) : ZMod N) =
        u ^ (16 * n) := by
    push_cast
    rw [hu (6 * n), hu (4 * n), hu n, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  have hsub :
      ((((unitFact p (8 * n * p ^ k) : ℤ) * unitFact p (5 * n * p ^ k) * unitFact p (3 * n * p ^ k)) -
        ((unitFact p (6 * n * p ^ k) : ℤ) * unitFact p (4 * n * p ^ k) ^ 2 * unitFact p (n * p ^ k) ^ 2) : ℤ) : ZMod N) = 0 := by
    rw [Int.cast_sub, hnum, hden, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hsub
  simpa [N] using hsub

theorem OMA.solution : type_of% @OMA.S_oeis_a364305.main := by
  intro p hp hp5 n k _hn hk
  exact dvd_sub_a_of_unitFact hp hk (dvd_P_num_sub_P_den hp hp5 hk)
