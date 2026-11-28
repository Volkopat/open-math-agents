import OMAStatements.S_oeis_a156684

-- Problem: A156684: The number of primitive Pythagorean triples A^2+B^2=C^2 with 0 < A < B < C and gcd(A,B)=1, and both legs less than n.
-- Upstream: formal-conjectures statements/oeis-a156684.lean:0 (declaration OMA.S_oeis_a156684.main)
-- Credit: @Progren (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Finset
open scoped Topology

namespace OeisA156684Proof

/-! ### Part 1: Euclid Parametrization Bijection -/

private def euclidPairs (M : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter fun p =>
    p.2 < p.1 ∧ (p.1 + p.2) % 2 = 1 ∧ p.1 ^ 2 - p.2 ^ 2 ≤ M ∧ 2 * p.1 * p.2 ≤ M

private def primEuclidPairs (M : ℕ) : Finset (ℕ × ℕ) :=
  (euclidPairs M).filter fun p => Nat.Coprime p.1 p.2

private lemma sq_sub_odd {m k : ℕ} (hkm : k < m) (hpar : (m + k) % 2 = 1) :
    (m ^ 2 - k ^ 2) % 2 = 1 := by
  have hle : k ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hkm.le 2
  have hmod1 : m ^ 2 % 2 = m % 2 := by
    rw [sq, Nat.mul_mod]; have := Nat.mod_lt m zero_lt_two; interval_cases (m % 2) <;> rfl
  have hmod2 : k ^ 2 % 2 = k % 2 := by
    rw [sq, Nat.mul_mod]; have := Nat.mod_lt k zero_lt_two; interval_cases (k % 2) <;> rfl
  omega

private lemma pyth_euclid_id {m k : ℕ} (hkm : k ≤ m) :
    (m ^ 2 - k ^ 2) ^ 2 + (2 * m * k) ^ 2 = (m ^ 2 + k ^ 2) ^ 2 := by
  have hle : k ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hkm 2
  zify [hle]
  ring

private lemma le_sq_sub_of_lt {m k : ℕ} (hkm : k < m) : m ≤ m ^ 2 - k ^ 2 := by
  have hfac : (m - k) * (m + k) = m ^ 2 - k ^ 2 := by
    zify [hkm.le, Nat.pow_le_pow_left hkm.le 2]
    ring
  have h1 : m ≤ 1 * (m + k) := by omega
  have h2 : 1 * (m + k) ≤ (m - k) * (m + k) := Nat.mul_le_mul_right (m + k) (by omega)
  omega

private lemma coprime_sq_sub_two_mul {m k : ℕ} (hkm : k < m)
    (hcop : Nat.Coprime m k) (hpar : (m + k) % 2 = 1) :
    Nat.Coprime (m ^ 2 - k ^ 2) (2 * m * k) := by
  have hparZ : ((m : ℤ) % 2 = 0 ∧ (k : ℤ) % 2 = 1) ∨ ((m : ℤ) % 2 = 1 ∧ (k : ℤ) % 2 = 0) := by
    omega
  have hgcdZ : Int.gcd (m : ℤ) (k : ℤ) = 1 := by
    simpa [Int.gcd] using hcop
  have hcls := (PythagoreanTriple.coprime_classification
    (x := (m : ℤ) ^ 2 - (k : ℤ) ^ 2) (y := 2 * (m : ℤ) * (k : ℤ))
    (z := (m : ℤ) ^ 2 + (k : ℤ) ^ 2)).mpr
    ⟨m, k, Or.inl ⟨rfl, rfl⟩, Or.inl rfl, hgcdZ, hparZ⟩
  have hcast1 : ((m ^ 2 - k ^ 2 : ℕ) : ℤ) = (m : ℤ) ^ 2 - (k : ℤ) ^ 2 := by
    have hle : k ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hkm.le 2
    zify [hle]
  have hcast2 : ((2 * m * k : ℕ) : ℤ) = 2 * (m : ℤ) * (k : ℤ) := by push_cast; ring
  have hgcd : Int.gcd ((m ^ 2 - k ^ 2 : ℕ) : ℤ) ((2 * m * k : ℕ) : ℤ) = 1 := by
    rw [hcast1, hcast2]
    exact hcls.2
  simpa only [Nat.Coprime, Int.gcd, Int.natAbs_natCast] using hgcd

private lemma a_succ_eq_card_primEuclidPairs (M : ℕ) :
    OMA.S_oeis_a156684.a (M + 1) = (primEuclidPairs M).card := by
  unfold OMA.S_oeis_a156684.a
  symm
  refine Finset.card_bij
    (fun p _ => (min (p.1 ^ 2 - p.2 ^ 2) (2 * p.1 * p.2),
                 max (p.1 ^ 2 - p.2 ^ 2) (2 * p.1 * p.2)))
    ?_ ?_ ?_
  · intro p hp
    simp only [primEuclidPairs, euclidPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc] at hp
    rcases hp with ⟨⟨⟨⟨hm1, _⟩, ⟨hk1, _⟩⟩, hkm, hpar, hsub, hmul⟩, hcop⟩
    set u := p.1 ^ 2 - p.2 ^ 2
    set v := 2 * p.1 * p.2
    have hu_pos : 0 < u := by
      have : p.2 ^ 2 < p.1 ^ 2 := Nat.pow_lt_pow_left hkm (by decide)
      omega
    have hv_pos : 0 < v := by positivity
    have hu_odd : u % 2 = 1 := sq_sub_odd hkm hpar
    have hv_even : v % 2 = 0 := by
      have : v = 2 * (p.1 * p.2) := by dsimp only [v]; ring
      omega
    have hne : u ≠ v := by omega
    have hlt : min u v < max u v := by
      rcases lt_or_gt_of_ne hne with h | h
      · rw [min_eq_left h.le, max_eq_right h.le]; exact h
      · rw [min_eq_right h.le, max_eq_left h.le]; exact h
    have hcop_uv : Nat.Coprime u v := coprime_sq_sub_two_mul hkm hcop hpar
    have hcop_mm : Nat.Coprime (min u v) (max u v) := by
      rcases le_total u v with h | h
      · rwa [min_eq_left h, max_eq_right h]
      · rw [min_eq_right h, max_eq_left h]; exact hcop_uv.symm
    have hsq_sum : (min u v) ^ 2 + (max u v) ^ 2 = (p.1 ^ 2 + p.2 ^ 2) ^ 2 := by
      have hswap : (min u v) ^ 2 + (max u v) ^ 2 = u ^ 2 + v ^ 2 := by
        rcases le_total u v with h | h
        · rw [min_eq_left h, max_eq_right h]
        · rw [min_eq_right h, max_eq_left h, add_comm]
      rw [hswap]
      exact pyth_euclid_id hkm.le
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨?_, ?_⟩, ?_, hlt, hcop_mm, ?_⟩
    · exact Nat.lt_succ_of_le (min_le_of_left_le hsub)
    · exact Nat.lt_succ_of_le (max_le hsub hmul)
    · exact lt_min hu_pos hv_pos
    · rw [hsq_sum, Nat.sqrt_eq']
  · intro p1 hp1 p2 hp2 heq
    simp only [primEuclidPairs, euclidPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc] at hp1 hp2
    rcases hp1 with ⟨⟨_, hkm1, hpar1, _, _⟩, _⟩
    rcases hp2 with ⟨⟨_, hkm2, hpar2, _, _⟩, _⟩
    set u1 := p1.1 ^ 2 - p1.2 ^ 2
    set v1 := 2 * p1.1 * p1.2
    set u2 := p2.1 ^ 2 - p2.2 ^ 2
    set v2 := 2 * p2.1 * p2.2
    have hu1_odd : u1 % 2 = 1 := sq_sub_odd hkm1 hpar1
    have hv1_even : v1 % 2 = 0 := by
      have : v1 = 2 * (p1.1 * p1.2) := by dsimp only [v1]; ring
      omega
    have hu2_odd : u2 % 2 = 1 := sq_sub_odd hkm2 hpar2
    have hv2_even : v2 % 2 = 0 := by
      have : v2 = 2 * (p2.1 * p2.2) := by dsimp only [v2]; ring
      omega
    have hmin : min u1 v1 = min u2 v2 := congrArg Prod.fst heq
    have hmax : max u1 v1 = max u2 v2 := congrArg Prod.snd heq
    have huv : u1 = u2 ∧ v1 = v2 := by
      rcases le_total u1 v1 with h1 | h1 <;> rcases le_total u2 v2 with h2 | h2
      · rw [min_eq_left h1, min_eq_left h2] at hmin
        rw [max_eq_right h1, max_eq_right h2] at hmax
        exact ⟨hmin, hmax⟩
      · rw [min_eq_left h1, min_eq_right h2] at hmin; omega
      · rw [min_eq_right h1, min_eq_left h2] at hmin; omega
      · rw [min_eq_right h1, min_eq_right h2] at hmin
        rw [max_eq_left h1, max_eq_left h2] at hmax
        exact ⟨hmax, hmin⟩
    have hsum_sq : (p1.1 ^ 2 + p1.2 ^ 2) ^ 2 = (p2.1 ^ 2 + p2.2 ^ 2) ^ 2 := by
      rw [← pyth_euclid_id hkm1.le, ← pyth_euclid_id hkm2.le]
      change u1 ^ 2 + v1 ^ 2 = u2 ^ 2 + v2 ^ 2
      rw [huv.1, huv.2]
    have hsum : p1.1 ^ 2 + p1.2 ^ 2 = p2.1 ^ 2 + p2.2 ^ 2 :=
      Nat.pow_left_injective (by decide : 2 ≠ 0) hsum_sq
    have hle1 : p1.2 ^ 2 ≤ p1.1 ^ 2 := Nat.pow_le_pow_left hkm1.le 2
    have hle2 : p2.2 ^ 2 ≤ p2.1 ^ 2 := Nat.pow_le_pow_left hkm2.le 2
    have hsub_eq : p1.1 ^ 2 - p1.2 ^ 2 = p2.1 ^ 2 - p2.2 ^ 2 := huv.1
    have hsq1 : p1.1 ^ 2 = p2.1 ^ 2 := by omega
    have hsq2 : p1.2 ^ 2 = p2.2 ^ 2 := by omega
    exact Prod.ext (Nat.pow_left_injective (by decide : 2 ≠ 0) hsq1)
                   (Nat.pow_left_injective (by decide : 2 ≠ 0) hsq2)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
    rcases hq with ⟨⟨hxM, hyM⟩, hx_pos, hxy, hcop, hsqrt⟩
    set z := Nat.sqrt (q.1 ^ 2 + q.2 ^ 2)
    have hpyth : PythagoreanTriple (q.1 : ℤ) (q.2 : ℤ) (z : ℤ) := by
      show (q.1 : ℤ) * (q.1 : ℤ) + (q.2 : ℤ) * (q.2 : ℤ) = (z : ℤ) * (z : ℤ)
      have hsq : q.1 ^ 2 + q.2 ^ 2 = z ^ 2 := hsqrt.symm
      zify at hsq
      nlinarith
    have hcopZ : Int.gcd (q.1 : ℤ) (q.2 : ℤ) = 1 := by
      simpa [Int.gcd] using hcop
    obtain ⟨m', k', hlegs, _, hgcd', hpar'⟩ :=
      PythagoreanTriple.coprime_classification.mp ⟨hpyth, hcopZ⟩
    set m := m'.natAbs
    set k := k'.natAbs
    have hm_sq : (m : ℤ) ^ 2 = m' ^ 2 := by simp [m]
    have hk_sq : (k : ℤ) ^ 2 = k' ^ 2 := by simp [k]
    have hcop_mk : Nat.Coprime m k := by
      simpa [Nat.Coprime, Int.gcd, m, k] using hgcd'
    have hpar_mk : (m + k) % 2 = 1 := by
      have hm2 : (m : ℤ) % 2 = m' % 2 := by
        rcases Int.natAbs_eq m' with h | h <;> omega
      have hk2 : (k : ℤ) % 2 = k' % 2 := by
        rcases Int.natAbs_eq k' with h | h <;> omega
      omega
    have hcase_helper : ∀ (a b : ℕ), 0 < a → 0 < b → a ≤ M → b ≤ M →
        (a : ℤ) = m' ^ 2 - k' ^ 2 → (b : ℤ) = 2 * m' * k' →
        (m, k) ∈ primEuclidPairs M ∧ m ^ 2 - k ^ 2 = a ∧ 2 * m * k = b := by
      intro a b ha hb haM hbM ha_eq hb_eq
      have hmk_pos : 0 < m' * k' := by linarith
      have hmul_eq : (m : ℤ) * (k : ℤ) = m' * k' := by
        have h1 : ((m * k : ℕ) : ℤ) = |m' * k'| := by
          rw [← Int.natAbs_mul, Int.natCast_natAbs]
        rw [abs_of_pos hmk_pos] at h1
        push_cast at h1
        exact h1
      have h2mk : 2 * m * k = b := by
        have : ((2 * m * k : ℕ) : ℤ) = (b : ℤ) := by
          push_cast; linarith
        exact Int.ofNat.inj this
      have hkm : k < m := by
        have : (k : ℤ) ^ 2 < (m : ℤ) ^ 2 := by linarith
        have : k ^ 2 < m ^ 2 := by exact_mod_cast this
        nlinarith
      have hsub_eq : m ^ 2 - k ^ 2 = a := by
        have hle : k ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hkm.le 2
        have : ((m ^ 2 - k ^ 2 : ℕ) : ℤ) = (a : ℤ) := by
          zify [hle]; linarith
        exact Int.ofNat.inj this
      have hk_pos : 1 ≤ k := by
        by_contra h
        have hk0 : k = 0 := by omega
        rw [hk0, mul_zero] at h2mk
        omega
      have hm_le : m ≤ M := le_trans (le_sq_sub_of_lt hkm) (by omega)
      refine ⟨?_, hsub_eq, h2mk⟩
      simp only [primEuclidPairs, euclidPairs, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc]
      exact ⟨⟨⟨⟨by omega, hm_le⟩, ⟨hk_pos, by omega⟩⟩, hkm, hpar_mk, by omega, by omega⟩, hcop_mk⟩
    rcases hlegs with ⟨hx_eq, hy_eq⟩ | ⟨hx_eq, hy_eq⟩
    · obtain ⟨hmem, hsub, hmul⟩ := hcase_helper q.1 q.2 hx_pos (by omega)
        (Nat.lt_succ_iff.mp hxM) (Nat.lt_succ_iff.mp hyM) hx_eq hy_eq
      refine ⟨(m, k), hmem, ?_⟩
      simp only [hsub, hmul, min_eq_left hxy.le, max_eq_right hxy.le]
    · obtain ⟨hmem, hsub, hmul⟩ := hcase_helper q.2 q.1 (by omega) hx_pos
        (Nat.lt_succ_iff.mp hyM) (Nat.lt_succ_iff.mp hxM) hy_eq hx_eq
      refine ⟨(m, k), hmem, ?_⟩
      simp only [hsub, hmul, min_eq_right hxy.le, max_eq_left hxy.le]

/-! ### Part 2: Möbius Inversion Over Odd Divisors -/

private def G (M : ℕ) : ℕ := (euclidPairs M).card

private lemma sum_moebius_divisors_eq (g : ℕ) :
    ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℤ) = if g = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f g) ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply] using h

private lemma card_euclidPairs_dvd (M d : ℕ) (hd : 1 ≤ d) (hd_odd : d % 2 = 1) :
    ((euclidPairs M).filter fun p => d ∣ p.1 ∧ d ∣ p.2).card = G (M / d ^ 2) := by
  unfold G
  symm
  refine Finset.card_bij (fun p _ => (d * p.1, d * p.2)) ?_ ?_ ?_
  · intro p hp
    simp only [euclidPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
    rcases hp with ⟨⟨⟨hm1, _⟩, ⟨hk1, _⟩⟩, hkm, hpar, hsub, hmul⟩
    have hd2_pos : 0 < d ^ 2 := by positivity
    have hsub' : (d * p.1) ^ 2 - (d * p.2) ^ 2 ≤ M := by
      have h1 : (d * p.1) ^ 2 - (d * p.2) ^ 2 = d ^ 2 * (p.1 ^ 2 - p.2 ^ 2) := by
        zify [Nat.pow_le_pow_left hkm.le 2,
              Nat.pow_le_pow_left (Nat.mul_le_mul_left d hkm.le) 2]
        ring
      rw [h1]
      exact (Nat.le_div_iff_mul_le hd2_pos).mp hsub |> fun h => by linarith
    have hmul' : 2 * (d * p.1) * (d * p.2) ≤ M := by
      have h1 : 2 * (d * p.1) * (d * p.2) = d ^ 2 * (2 * p.1 * p.2) := by ring
      rw [h1]
      exact (Nat.le_div_iff_mul_le hd2_pos).mp hmul |> fun h => by linarith
    have hkm' : d * p.2 < d * p.1 := Nat.mul_lt_mul_of_pos_left hkm (by omega)
    have hdm_le : d * p.1 ≤ M := le_trans (le_sq_sub_of_lt hkm') hsub'
    have hpar' : (d * p.1 + d * p.2) % 2 = 1 := by
      rw [← mul_add, Nat.mul_mod, hd_odd, hpar]
    refine ⟨⟨⟨⟨by nlinarith, hdm_le⟩, ⟨by nlinarith, by nlinarith⟩⟩,
      hkm', hpar', hsub', hmul'⟩,
      dvd_mul_right d p.1, dvd_mul_right d p.2⟩
  · intro p1 _ p2 _ heq
    have h1 : d * p1.1 = d * p2.1 := congrArg Prod.fst heq
    have h2 : d * p1.2 = d * p2.2 := congrArg Prod.snd heq
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left (by omega) h1)
                   (Nat.eq_of_mul_eq_mul_left (by omega) h2)
  · intro q hq
    simp only [euclidPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
    rcases hq with ⟨⟨⟨⟨hm1, _⟩, ⟨hk1, _⟩⟩, hkm, hpar, hsub, hmul⟩, ⟨m', hm'⟩, ⟨k', hk'⟩⟩
    have hd2_pos : 0 < d ^ 2 := by positivity
    have hk'1 : 1 ≤ k' := by
      by_contra h
      have hk0 : k' = 0 := by omega
      rw [hk0, mul_zero] at hk'
      omega
    have hkm' : k' < m' := by
      rw [hm', hk'] at hkm
      exact Nat.lt_of_mul_lt_mul_left hkm
    have hpar' : (m' + k') % 2 = 1 := by
      rw [hm', hk', ← mul_add, Nat.mul_mod, hd_odd] at hpar
      omega
    have hsub' : m' ^ 2 - k' ^ 2 ≤ M / d ^ 2 := by
      rw [Nat.le_div_iff_mul_le hd2_pos]
      have h1 : (m' ^ 2 - k' ^ 2) * d ^ 2 = (d * m') ^ 2 - (d * k') ^ 2 := by
        zify [Nat.pow_le_pow_left hkm'.le 2,
              Nat.pow_le_pow_left (Nat.mul_le_mul_left d hkm'.le) 2]
        ring
      rw [h1, ← hm', ← hk']
      exact hsub
    have hmul' : 2 * m' * k' ≤ M / d ^ 2 := by
      rw [Nat.le_div_iff_mul_le hd2_pos]
      have h1 : 2 * m' * k' * d ^ 2 = 2 * (d * m') * (d * k') := by ring
      rw [h1, ← hm', ← hk']
      exact hmul
    have hm'_le : m' ≤ M / d ^ 2 := le_trans (le_sq_sub_of_lt hkm') hsub'
    refine ⟨(m', k'), ?_, Prod.ext hm'.symm hk'.symm⟩
    simp only [euclidPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨by omega, hm'_le⟩, ⟨hk'1, by omega⟩⟩, hkm', hpar', hsub', hmul'⟩

private lemma a_succ_eq_moebius_sum_int (M : ℕ) :
    (OMA.S_oeis_a156684.a (M + 1) : ℤ) =
      ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d % 2 = 1),
        (ArithmeticFunction.moebius d : ℤ) * (G (M / d ^ 2) : ℤ) := by
  rw [a_succ_eq_card_primEuclidPairs]
  have h1 : ((primEuclidPairs M).card : ℤ) =
      ∑ p ∈ euclidPairs M, ∑ d ∈ (Nat.gcd p.1 p.2).divisors, (ArithmeticFunction.moebius d : ℤ) := by
    have hsum : ∑ p ∈ euclidPairs M, (if Nat.gcd p.1 p.2 = 1 then (1 : ℤ) else 0) =
        ((primEuclidPairs M).card : ℤ) := by
      simp [primEuclidPairs, Nat.Coprime]
    rw [← hsum]
    refine Finset.sum_congr rfl fun p _ => (sum_moebius_divisors_eq _).symm
  rw [h1]
  set D := (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d % 2 = 1)
  have hsub : ∀ p ∈ euclidPairs M, (Nat.gcd p.1 p.2).divisors ⊆ D := by
    intro p hp d hd
    simp only [euclidPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    rcases hp with ⟨⟨⟨hm1, _⟩, ⟨hk1, _⟩⟩, hkm, hpar, hsubM, _⟩
    have hd_dvd : d ∣ Nat.gcd p.1 p.2 := Nat.dvd_of_mem_divisors hd
    have hd_pos : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hd1 : d ∣ p.1 := hd_dvd.trans (Nat.gcd_dvd_left p.1 p.2)
    have hd2 : d ∣ p.2 := hd_dvd.trans (Nat.gcd_dvd_right p.1 p.2)
    have hd_odd : d % 2 = 1 := by
      by_contra h
      have h2d : 2 ∣ d := by omega
      have h2m : 2 ∣ p.1 := h2d.trans hd1
      have h2k : 2 ∣ p.2 := h2d.trans hd2
      omega
    rcases hd1 with ⟨m', hm'⟩
    rcases hd2 with ⟨k', hk'⟩
    have hkm' : k' < m' := by
      rw [hm', hk'] at hkm
      exact Nat.lt_of_mul_lt_mul_left hkm
    have hd2_le : d ^ 2 ≤ M := by
      have h1 : d ^ 2 * (m' ^ 2 - k' ^ 2) = p.1 ^ 2 - p.2 ^ 2 := by
        rw [hm', hk']
        zify [Nat.pow_le_pow_left hkm'.le 2,
              Nat.pow_le_pow_left (Nat.mul_le_mul_left d hkm'.le) 2]
        ring
      have h2 : 1 ≤ m' ^ 2 - k' ^ 2 := by
        have : k' ^ 2 < m' ^ 2 := Nat.pow_lt_pow_left hkm' (by decide)
        omega
      nlinarith
    have hd_le_sqrt : d ≤ Nat.sqrt M := Nat.le_sqrt.mpr (by nlinarith)
    simp only [D, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hd_pos, hd_le_sqrt⟩, hd_odd⟩
  have h2 : ∑ p ∈ euclidPairs M, ∑ d ∈ (Nat.gcd p.1 p.2).divisors, (ArithmeticFunction.moebius d : ℤ) =
      ∑ p ∈ euclidPairs M, ∑ d ∈ D,
        if d ∣ p.1 ∧ d ∣ p.2 then (ArithmeticFunction.moebius d : ℤ) else 0 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp_orig := hp
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    simp only [euclidPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    have hg0 : Nat.gcd p.1 p.2 ≠ 0 := (Nat.gcd_pos_of_pos_left p.2 (by omega)).ne'
    constructor
    · intro ⟨hd_dvd, _⟩
      exact ⟨hsub p hp_orig (Nat.mem_divisors.mpr ⟨hd_dvd, hg0⟩),
        hd_dvd.trans (Nat.gcd_dvd_left _ _), hd_dvd.trans (Nat.gcd_dvd_right _ _)⟩
    · intro ⟨_, hd1, hd2⟩
      exact ⟨Nat.dvd_gcd hd1 hd2, hg0⟩
  rw [h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [D, Finset.mem_filter, Finset.mem_Icc] at hd
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [card_euclidPairs_dvd M d hd.1.1 hd.2]

private lemma a_succ_eq_moebius_sum_real (M : ℕ) :
    (OMA.S_oeis_a156684.a (M + 1) : ℝ) =
      ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d % 2 = 1),
        (ArithmeticFunction.moebius d : ℝ) * (G (M / d ^ 2) : ℝ) := by
  have h := congrArg (Int.cast (R := ℝ)) (a_succ_eq_moebius_sum_int M)
  simpa using h

/-! ### Part 3: Row Count and Area Asymptotics for `G X` -/

private def rowUpper (X k : ℕ) : ℕ :=
  min (Nat.sqrt (X + k ^ 2)) (X / (2 * k))

private lemma card_odd_step_Icc (k u : ℕ) (hku : k ≤ u) :
    ((Finset.Icc (k + 1) u).filter fun m => (m + k) % 2 = 1).card = (u - k + 1) / 2 := by
  symm
  rw [← Finset.card_range ((u - k + 1) / 2)]
  refine Finset.card_bij (fun j _ => k + 1 + 2 * j) ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_range] at hj
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  · intro j1 _ j2 _ h; omega
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    refine ⟨(m - k - 1) / 2, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · omega

private lemma G_eq_sum_rows (X : ℕ) :
    G X = ∑ k ∈ Finset.Icc 1 (Nat.sqrt (X / 2)), (rowUpper X k - k + 1) / 2 := by
  unfold G
  let K := Nat.sqrt (X / 2)
  have hcard : (euclidPairs X).card =
      ∑ k ∈ Finset.Icc 1 K, ((euclidPairs X).filter fun p => p.2 = k).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · intro hp
        have hp' := hp
        simp only [euclidPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp'
        rcases hp' with ⟨⟨⟨_, _⟩, ⟨hk1, _⟩⟩, hkm, _, _, hmul⟩
        have hk2 : p.2 ^ 2 ≤ X / 2 := by
          have : 2 * p.2 ^ 2 ≤ 2 * p.1 * p.2 := by nlinarith
          omega
        exact ⟨p.2, ⟨hk1, Nat.le_sqrt.mpr (by nlinarith)⟩, hp, rfl⟩
      · rintro ⟨_, _, hp, _⟩; exact hp
    · intro k1 _ k2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter] at hp1 hp2
      exact hne (hp1.2.symm.trans hp2.2)
  rw [hcard]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_Icc] at hk
  have hk_le_u : k ≤ rowUpper X k := by
    unfold rowUpper
    refine le_min ?_ ?_
    · exact Nat.le_sqrt.mpr (by nlinarith)
    · rw [Nat.le_div_iff_mul_le (by omega)]
      have hk2 : k * k ≤ X / 2 := Nat.le_sqrt.mp hk.2
      have hmul2 : k * (2 * k) = 2 * (k * k) := by ring
      omega
  rw [← card_odd_step_Icc k (rowUpper X k) hk_le_u]
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp only [euclidPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    rcases hp with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, hkm, hpar, hsub, hmul⟩, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, hpar⟩
    unfold rowUpper
    refine le_min ?_ ?_
    · exact Nat.le_sqrt.mpr (by rw [← sq]; omega)
    · rw [Nat.le_div_iff_mul_le (by omega)]
      linarith
  · intro p1 hp1 p2 hp2 h1
    simp only [Finset.mem_filter] at hp1 hp2
    exact Prod.ext h1 (hp1.2.trans hp2.2.symm)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    rcases hm with ⟨⟨hkm, hmu⟩, hpar⟩
    have hmu1 : m ≤ Nat.sqrt (X + k ^ 2) := le_trans hmu (min_le_left _ _)
    have hmu2 : m ≤ X / (2 * k) := le_trans hmu (min_le_right _ _)
    have hsub : m ^ 2 - k ^ 2 ≤ X := by
      have : m * m ≤ X + k ^ 2 := Nat.le_sqrt.mp hmu1
      rw [← sq] at this
      omega
    have hmul : 2 * m * k ≤ X := by
      have : m * (2 * k) ≤ X := (Nat.le_div_iff_mul_le (by omega)).mp hmu2
      linarith
    have hmX : m ≤ X := by
      have : 2 * m * 1 ≤ 2 * m * k := Nat.mul_le_mul_left (2 * m) hk.1
      omega
    have hkX : k ≤ X := by omega
    refine ⟨(m, k), ?_, rfl⟩
    simp only [euclidPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨⟨by omega, hmX⟩, ⟨hk.1, hkX⟩⟩, by omega, hpar, hsub, hmul⟩, trivial⟩

private noncomputable def α : ℝ := Real.sqrt ((Real.sqrt 2 - 1) / 2)

private lemma α_sq : α ^ 2 = (Real.sqrt 2 - 1) / 2 := by
  unfold α
  refine Real.sq_sqrt ?_
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

private lemma α_pos : 0 < α := by
  unfold α
  refine Real.sqrt_pos.mpr ?_
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

private lemma α_lt_inv_sqrt_two : α < 1 / Real.sqrt 2 := by
  have h2 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hinv : 0 < 1 / Real.sqrt 2 := by positivity
  have hlt : α ^ 2 < (1 / Real.sqrt 2) ^ 2 := by
    rw [α_sq, div_pow, one_pow, hsq2]
    have : Real.sqrt 2 < 2 := by nlinarith
    linarith
  nlinarith [α_pos, hinv]

private lemma sqrt_one_add_α_sq : Real.sqrt (1 + α ^ 2) = 1 / (2 * α) := by
  have hα : 0 < α := α_pos
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h4 : 4 * α ^ 2 * (1 + α ^ 2) = 1 := by
    rw [α_sq]; nlinarith
  have h1 : (1 / (2 * α)) ^ 2 = 1 + α ^ 2 := by
    field_simp
    linarith
  rw [← h1, Real.sqrt_sq (by positivity)]

private lemma α_add_sqrt : α + Real.sqrt (1 + α ^ 2) = Real.sqrt (1 + Real.sqrt 2) := by
  have hpos : 0 ≤ α + Real.sqrt (1 + α ^ 2) := add_nonneg α_pos.le (Real.sqrt_nonneg _)
  have hsq : (α + Real.sqrt (1 + α ^ 2)) ^ 2 = 1 + Real.sqrt 2 := by
    have h1 : Real.sqrt (1 + α ^ 2) ^ 2 = 1 + α ^ 2 := Real.sq_sqrt (by positivity)
    have h2 : α * Real.sqrt (1 + α ^ 2) = 1 / 2 := by
      rw [sqrt_one_add_α_sq]; field_simp [α_pos.ne']
    nlinarith [α_sq]
  rw [← hsq, Real.sqrt_sq hpos]

private noncomputable def g (x : ℝ) : ℝ :=
  if x ≤ α then Real.sqrt (1 + x ^ 2) - x else 1 / (2 * x) - x

private lemma g_eq_min {x : ℝ} (hx : 0 < x) :
    g x = min (Real.sqrt (1 + x ^ 2)) (1 / (2 * x)) - x := by
  unfold g
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  by_cases h : x ≤ α
  · rw [if_pos h]
    have hx2 : x ^ 2 ≤ α ^ 2 := by nlinarith [α_pos]
    have hle : Real.sqrt (1 + x ^ 2) ≤ 1 / (2 * x) := by
      have hsq : 1 + x ^ 2 ≤ (1 / (2 * x)) ^ 2 := by
        rw [div_pow, one_pow, le_div_iff₀ (by positivity)]
        have h4α : 4 * α ^ 2 * (1 + α ^ 2) = 1 := by rw [α_sq]; nlinarith
        nlinarith
      calc Real.sqrt (1 + x ^ 2) ≤ Real.sqrt ((1 / (2 * x)) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = 1 / (2 * x) := Real.sqrt_sq (by positivity)
    rw [min_eq_left hle]
  · rw [if_neg h]
    have hgt : α < x := not_le.mp h
    have hx2 : α ^ 2 < x ^ 2 := by nlinarith [α_pos]
    have hle : 1 / (2 * x) ≤ Real.sqrt (1 + x ^ 2) := by
      have hsq : (1 / (2 * x)) ^ 2 ≤ 1 + x ^ 2 := by
        rw [div_pow, one_pow, div_le_iff₀ (by positivity)]
        have h4α : 4 * α ^ 2 * (1 + α ^ 2) = 1 := by rw [α_sq]; nlinarith
        nlinarith
      calc 1 / (2 * x) = Real.sqrt ((1 / (2 * x)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (1 + x ^ 2) := Real.sqrt_le_sqrt hsq
    rw [min_eq_right hle]

private lemma g_antitone_left {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.sqrt (1 + y ^ 2) - y ≤ Real.sqrt (1 + x ^ 2) - x := by
  have hxpos : 0 < Real.sqrt (1 + x ^ 2) + x := by
    have : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
    linarith
  have hypos : 0 < Real.sqrt (1 + y ^ 2) + y := by
    have : 0 < Real.sqrt (1 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
    linarith
  have hrx : (Real.sqrt (1 + x ^ 2) - x) * (Real.sqrt (1 + x ^ 2) + x) = 1 := by
    have : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
    nlinarith
  have hry : (Real.sqrt (1 + y ^ 2) - y) * (Real.sqrt (1 + y ^ 2) + y) = 1 := by
    have : Real.sqrt (1 + y ^ 2) ^ 2 = 1 + y ^ 2 := Real.sq_sqrt (by positivity)
    nlinarith
  have hle : Real.sqrt (1 + x ^ 2) + x ≤ Real.sqrt (1 + y ^ 2) + y := by
    have : Real.sqrt (1 + x ^ 2) ≤ Real.sqrt (1 + y ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hx_eq : Real.sqrt (1 + x ^ 2) - x = 1 / (Real.sqrt (1 + x ^ 2) + x) := by
    field_simp [hxpos.ne']; linarith
  have hy_eq : Real.sqrt (1 + y ^ 2) - y = 1 / (Real.sqrt (1 + y ^ 2) + y) := by
    field_simp [hypos.ne']; linarith
  rw [hx_eq, hy_eq]
  exact one_div_le_one_div_of_le hxpos hle

private lemma g_antitoneOn : AntitoneOn g (Set.Icc 0 (1 / Real.sqrt 2)) := by
  intro x hx y hy hxy
  unfold g
  by_cases hxα : x ≤ α <;> by_cases hyα : y ≤ α
  · rw [if_pos hxα, if_pos hyα]; exact g_antitone_left hx.1 hxy
  · have hygt : α < y := not_le.mp hyα
    rw [if_pos hxα, if_neg hyα]
    calc 1 / (2 * y) - y ≤ 1 / (2 * α) - α := by
          have : 1 / (2 * y) ≤ 1 / (2 * α) :=
            one_div_le_one_div_of_le (by linarith [α_pos]) (by linarith)
          linarith
      _ = Real.sqrt (1 + α ^ 2) - α := by rw [sqrt_one_add_α_sq]
      _ ≤ Real.sqrt (1 + x ^ 2) - x := g_antitone_left hx.1 hxα
  · linarith
  · have hxgt : α < x := not_le.mp hxα
    rw [if_neg hxα, if_neg hyα]
    have hxpos : 0 < x := lt_trans α_pos hxgt
    have : 1 / (2 * y) ≤ 1 / (2 * x) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith

private lemma g_zero : g 0 = 1 := by
  unfold g
  rw [if_pos α_pos.le]
  norm_num

private lemma g_end : g (1 / Real.sqrt 2) = 0 := by
  unfold g
  rw [if_neg (not_le.mpr α_lt_inv_sqrt_two)]
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp [hpos]
  linarith

private lemma g_nonneg {x : ℝ} (hx : x ∈ Set.Icc 0 (1 / Real.sqrt 2)) : 0 ≤ g x := by
  rw [← g_end]
  exact g_antitoneOn hx ⟨by positivity, le_rfl⟩ hx.2

private lemma g_le_one {x : ℝ} (hx : x ∈ Set.Icc 0 (1 / Real.sqrt 2)) : g x ≤ 1 := by
  rw [← g_zero]
  exact g_antitoneOn ⟨le_rfl, by positivity⟩ hx hx.1

private lemma g_continuousOn : ContinuousOn g (Set.Icc 0 (1 / Real.sqrt 2)) := by
  have h1 : ContinuousOn (fun x : ℝ => Real.sqrt (1 + x ^ 2) - x) (Set.Icc 0 α) := by
    fun_prop
  have h2 : ContinuousOn (fun x : ℝ => 1 / (2 * x) - x) (Set.Icc α (1 / Real.sqrt 2)) := by
    refine ContinuousOn.sub ?_ continuousOn_id
    refine continuousOn_const.div (continuousOn_const.mul continuousOn_id) ?_
    intro x hx
    have : 0 < x := lt_of_lt_of_le α_pos hx.1
    linarith
  have hg1 : Set.EqOn g (fun x : ℝ => Real.sqrt (1 + x ^ 2) - x) (Set.Icc 0 α) := by
    intro x hx; simp [g, hx.2]
  have hg2 : Set.EqOn g (fun x : ℝ => 1 / (2 * x) - x) (Set.Icc α (1 / Real.sqrt 2)) := by
    intro x hx
    unfold g
    by_cases h : x ≤ α
    · have hxa : x = α := le_antisymm h hx.1
      rw [if_pos h, hxa, sqrt_one_add_α_sq]
    · rw [if_neg h]
  have hunion : Set.Icc (0 : ℝ) (1 / Real.sqrt 2) = Set.Icc 0 α ∪ Set.Icc α (1 / Real.sqrt 2) :=
    (Set.Icc_union_Icc_eq_Icc α_pos.le α_lt_inv_sqrt_two.le).symm
  rw [hunion]
  exact (h1.congr hg1).union_of_isClosed (h2.congr hg2) isClosed_Icc isClosed_Icc

private lemma integral_g :
    ∫ x in (0 : ℝ)..(1 / Real.sqrt 2), g x = Real.log (1 + Real.sqrt 2) / 2 := by
  have hint1 : IntervalIntegrable g MeasureTheory.volume 0 α :=
    (g_continuousOn.mono (Set.Icc_subset_Icc_right α_lt_inv_sqrt_two.le)).intervalIntegrable_of_Icc
      α_pos.le
  have hint2 : IntervalIntegrable g MeasureTheory.volume α (1 / Real.sqrt 2) :=
    (g_continuousOn.mono (Set.Icc_subset_Icc_left α_pos.le)).intervalIntegrable_of_Icc
      α_lt_inv_sqrt_two.le
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have hI1 : ∫ x in (0 : ℝ)..α, g x =
      1 / 4 + Real.log (1 + Real.sqrt 2) / 4 - α ^ 2 / 2 := by
    have hcongr : ∫ x in (0 : ℝ)..α, g x = ∫ x in (0 : ℝ)..α, (Real.sqrt (1 + x ^ 2) - x) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le α_pos.le] at hx
      simp [g, hx.2]
    rw [hcongr]
    let F1 : ℝ → ℝ := fun x =>
      (x * Real.sqrt (1 + x ^ 2) + Real.log (x + Real.sqrt (1 + x ^ 2))) / 2 - x ^ 2 / 2
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) α, HasDerivAt F1 (Real.sqrt (1 + x ^ 2) - x) x := by
      intro x hx
      rw [Set.uIcc_of_le α_pos.le] at hx
      have hspos : 0 < 1 + x ^ 2 := by positivity
      have hsr_pos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr hspos
      have hsum_pos : 0 < x + Real.sqrt (1 + x ^ 2) := by linarith [hx.1]
      have hd_pow2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have hd_inner : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x :=
        hd_pow2.const_add 1
      have hd_sqrt : HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2))
          (2 * x / (2 * Real.sqrt (1 + x ^ 2))) x := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hd_inner.sqrt hspos.ne'
      have hd_prod : HasDerivAt (fun t : ℝ => t * Real.sqrt (1 + t ^ 2))
          (1 * Real.sqrt (1 + x ^ 2) + x * (2 * x / (2 * Real.sqrt (1 + x ^ 2)))) x :=
        (hasDerivAt_id x).mul hd_sqrt
      have hd_arg : HasDerivAt (fun t : ℝ => t + Real.sqrt (1 + t ^ 2))
          (1 + 2 * x / (2 * Real.sqrt (1 + x ^ 2))) x :=
        (hasDerivAt_id x).add hd_sqrt
      have hd_log : HasDerivAt (fun t : ℝ => Real.log (t + Real.sqrt (1 + t ^ 2)))
          ((1 + 2 * x / (2 * Real.sqrt (1 + x ^ 2))) / (x + Real.sqrt (1 + x ^ 2))) x :=
        hd_arg.log hsum_pos.ne'
      have hd_F1 := ((hd_prod.add hd_log).div_const 2).sub (hd_pow2.div_const 2)
      refine hd_F1.congr_deriv ?_
      have hsq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt hspos.le
      field_simp [hsr_pos.ne', hsum_pos.ne']
      nlinarith
    have hcont : IntervalIntegrable (fun x : ℝ => Real.sqrt (1 + x ^ 2) - x)
        MeasureTheory.volume 0 α := by
      exact (by fun_prop : Continuous (fun x : ℝ => Real.sqrt (1 + x ^ 2) - x)).intervalIntegrable 0 α
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
    simp only [F1]
    have h0 : (0 * Real.sqrt (1 + 0 ^ 2) + Real.log (0 + Real.sqrt (1 + 0 ^ 2))) / 2 - 0 ^ 2 / 2 = 0 := by
      norm_num
    rw [h0, sub_zero, α_add_sqrt, sqrt_one_add_α_sq]
    have hlog : Real.log (Real.sqrt (1 + Real.sqrt 2)) = Real.log (1 + Real.sqrt 2) / 2 := by
      rw [Real.log_sqrt (by positivity)]
    rw [hlog]
    field_simp [α_pos.ne']
    ring
  have hI2 : ∫ x in α..(1 / Real.sqrt 2), g x =
      Real.log (1 + Real.sqrt 2) / 4 - (1 / 4 - α ^ 2 / 2) := by
    have hcongr : ∫ x in α..(1 / Real.sqrt 2), g x =
        ∫ x in α..(1 / Real.sqrt 2), (1 / (2 * x) - x) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le α_lt_inv_sqrt_two.le] at hx
      unfold g
      by_cases h : x ≤ α
      · have hxa : x = α := le_antisymm h hx.1
        rw [if_pos h, hxa, sqrt_one_add_α_sq]
      · rw [if_neg h]
    rw [hcongr]
    let F2 : ℝ → ℝ := fun x => Real.log x / 2 - x ^ 2 / 2
    have hderiv : ∀ x ∈ Set.uIcc α (1 / Real.sqrt 2), HasDerivAt F2 (1 / (2 * x) - x) x := by
      intro x hx
      rw [Set.uIcc_of_le α_lt_inv_sqrt_two.le] at hx
      have hxpos : 0 < x := lt_of_lt_of_le α_pos hx.1
      have hd_pow2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have hd := ((Real.hasDerivAt_log hxpos.ne').div_const 2).sub (hd_pow2.div_const 2)
      refine hd.congr_deriv ?_
      field_simp [hxpos.ne']
    have hcont : IntervalIntegrable (fun x : ℝ => 1 / (2 * x) - x)
        MeasureTheory.volume α (1 / Real.sqrt 2) := by
      refine ContinuousOn.intervalIntegrable_of_Icc α_lt_inv_sqrt_two.le ?_
      refine ContinuousOn.sub ?_ continuousOn_id
      refine continuousOn_const.div (continuousOn_const.mul continuousOn_id) ?_
      intro x hx
      have : 0 < x := lt_of_lt_of_le α_pos hx.1
      linarith
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
    simp only [F2]
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hinv_ne : (1 / Real.sqrt 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hlog_sub : Real.log (1 / Real.sqrt 2) - Real.log α = Real.log (1 + Real.sqrt 2) / 2 := by
      rw [← Real.log_div hinv_ne α_pos.ne']
      have hpos : 0 < 1 / Real.sqrt 2 / α := div_pos (by positivity) α_pos
      have hsq : (1 / Real.sqrt 2 / α) ^ 2 = 1 + Real.sqrt 2 := by
        rw [div_pow, div_pow, one_pow, hsq2, α_sq]
        have h1 : (Real.sqrt 2 - 1) ≠ 0 := by
          have : (1 : ℝ) < Real.sqrt 2 := by
            rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
            exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
          linarith
        field_simp [h1]
        nlinarith
      have heq : 1 / Real.sqrt 2 / α = Real.sqrt (1 + Real.sqrt 2) := by
        rw [← hsq, Real.sqrt_sq hpos.le]
      rw [heq, Real.log_sqrt (by positivity)]
    have hpow : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
      rw [div_pow, one_pow, hsq2]
    rw [hpow]
    linarith
  rw [hI1, hI2]
  ring

private lemma riemann_sum_g_bound (X : ℕ) (hX : 1 ≤ X) :
    |(1 / Real.sqrt X) * ∑ k ∈ Finset.Icc 1 (Nat.sqrt (X / 2)), g ((k : ℝ) / Real.sqrt X) -
      Real.log (1 + Real.sqrt 2) / 2| ≤ 2 / Real.sqrt X := by
  set h : ℝ := 1 / Real.sqrt X
  set K : ℕ := Nat.sqrt (X / 2)
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hsqX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  have hhpos : 0 < h := by positivity
  have hinv2 : 0 < 1 / Real.sqrt 2 := by positivity
  have hKh_le : (K : ℝ) * h ≤ 1 / Real.sqrt 2 := by
    have hK2 : K * K ≤ X / 2 := Nat.le_sqrt.mp le_rfl
    have hK2R : (2 : ℝ) * (K : ℝ) ^ 2 ≤ (X : ℝ) := by
      have : 2 * (K * K) ≤ X := by omega
      have : ((2 * (K * K) : ℕ) : ℝ) ≤ (X : ℝ) := Nat.cast_le.mpr this
      push_cast at this; linarith
    have hsq : ((K : ℝ) * h) ^ 2 ≤ (1 / Real.sqrt 2) ^ 2 := by
      simp only [h, mul_pow, div_pow, one_pow, Real.sq_sqrt hXpos.le,
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      rw [mul_one_div, div_le_div_iff₀ hXpos (by norm_num)]
      linarith
    have hKh_nn : 0 ≤ (K : ℝ) * h := by positivity
    nlinarith [hinv2, hKh_nn]
  have hKh_gap : 1 / Real.sqrt 2 - (K : ℝ) * h ≤ h := by
    have hK1 : X / 2 < (K + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt (X / 2)
      nlinarith
    have hXlt : (X : ℝ) < 2 * ((K : ℝ) + 1) ^ 2 := by
      have : X < 2 * (K + 1) ^ 2 := by omega
      have : (X : ℝ) < ((2 * (K + 1) ^ 2 : ℕ) : ℝ) := Nat.cast_lt.mpr this
      push_cast at this; linarith
    have hsq : (1 / Real.sqrt 2) ^ 2 < (((K : ℝ) + 1) * h) ^ 2 := by
      simp only [h, mul_pow, div_pow, one_pow, Real.sq_sqrt hXpos.le,
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      rw [mul_one_div, div_lt_div_iff₀ (by norm_num) hXpos]
      linarith
    have hK1_nn : 0 ≤ ((K : ℝ) + 1) * h := by positivity
    have hlt : 1 / Real.sqrt 2 < ((K : ℝ) + 1) * h := by nlinarith [hinv2, hK1_nn]
    linarith
  have hint_sub : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 / Real.sqrt 2 →
      IntervalIntegrable g MeasureTheory.volume a b := fun a b ha hab hb =>
    (g_continuousOn.mono (Set.Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  have hsum_int : ∑ k ∈ Finset.Icc 1 K, ∫ t in (((k - 1 : ℕ) : ℝ) * h)..((k : ℝ) * h), g t =
      ∫ t in (0 : ℝ)..((K : ℝ) * h), g t := by
    have hrew : ∑ k ∈ Finset.Icc 1 K, ∫ t in (((k - 1 : ℕ) : ℝ) * h)..((k : ℝ) * h), g t =
        ∑ j ∈ Finset.range K, ∫ t in ((j : ℝ) * h)..(((j + 1 : ℕ) : ℝ) * h), g t := by
      refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
      · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
      · intro k1 hk1 k2 hk2 heq; rw [Finset.mem_Icc] at hk1 hk2; omega
      · intro j hj; rw [Finset.mem_range] at hj
        exact ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk; rw [Finset.mem_Icc] at hk
        have hkk : k - 1 + 1 = k := by omega
        rw [hkk]
    rw [hrew]
    have hadj := intervalIntegral.sum_integral_adjacent_intervals
      (f := g) (a := fun j : ℕ => (j : ℝ) * h) (n := K)
      (fun j hj => hint_sub ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h) (by positivity)
        (by push_cast; nlinarith)
        (le_trans (by
          have : ((j + 1 : ℕ) : ℝ) ≤ (K : ℝ) := Nat.cast_le.mpr (Nat.succ_le_of_lt hj)
          nlinarith) hKh_le))
    simpa using hadj
  have hlower : h * ∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) / Real.sqrt X) ≤
      Real.log (1 + Real.sqrt 2) / 2 := by
    rw [← integral_g]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hint_sub 0 ((K : ℝ) * h) le_rfl (by positivity) hKh_le)
      (hint_sub ((K : ℝ) * h) (1 / Real.sqrt 2) (by positivity) hKh_le le_rfl)
    rw [← hsplit]
    have htail_nonneg : 0 ≤ ∫ t in ((K : ℝ) * h)..(1 / Real.sqrt 2), g t := by
      refine intervalIntegral.integral_nonneg hKh_le fun t ht => ?_
      exact g_nonneg ⟨le_trans (by positivity) ht.1, ht.2⟩
    have hmain_le : h * ∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) / Real.sqrt X) ≤
        ∫ t in (0 : ℝ)..((K : ℝ) * h), g t := by
      rw [← hsum_int, Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      have hlen : ((k : ℝ) * h) - (((k - 1 : ℕ) : ℝ) * h) = h := by
        have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub hk.1, Nat.cast_one]
        rw [hk1]; ring
      have hle_ab : ((k - 1 : ℕ) : ℝ) * h ≤ (k : ℝ) * h := by
        have : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr (Nat.sub_le k 1)
        nlinarith
      have hkb : (k : ℝ) * h ≤ 1 / Real.sqrt 2 :=
        le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk.2) hhpos.le) hKh_le
      have hconst : h * g ((k : ℝ) / Real.sqrt X) =
          ∫ _ in (((k - 1 : ℕ) : ℝ) * h)..((k : ℝ) * h), g ((k : ℝ) * h) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, hlen]
        simp [h, div_eq_mul_inv]
      rw [hconst]
      refine intervalIntegral.integral_mono_on hle_ab intervalIntegrable_const
        (hint_sub _ _ (by positivity) hle_ab hkb) fun t ht => ?_
      exact g_antitoneOn ⟨le_trans (by positivity) ht.1, le_trans ht.2 hkb⟩
        ⟨by positivity, hkb⟩ ht.2
    linarith
  have hupper : Real.log (1 + Real.sqrt 2) / 2 ≤
      h * ∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) / Real.sqrt X) + 2 * h := by
    rw [← integral_g]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hint_sub 0 ((K : ℝ) * h) le_rfl (by positivity) hKh_le)
      (hint_sub ((K : ℝ) * h) (1 / Real.sqrt 2) (by positivity) hKh_le le_rfl)
    rw [← hsplit]
    have htail_le : ∫ t in ((K : ℝ) * h)..(1 / Real.sqrt 2), g t ≤ h := by
      calc ∫ t in ((K : ℝ) * h)..(1 / Real.sqrt 2), g t
          ≤ ∫ _ in ((K : ℝ) * h)..(1 / Real.sqrt 2), (1 : ℝ) :=
            intervalIntegral.integral_mono_on hKh_le
              (hint_sub _ _ (by positivity) hKh_le le_rfl) intervalIntegrable_const
              fun t ht => g_le_one ⟨le_trans (by positivity) ht.1, ht.2⟩
        _ = 1 / Real.sqrt 2 - (K : ℝ) * h := by simp
        _ ≤ h := hKh_gap
    have hmain_le : ∫ t in (0 : ℝ)..((K : ℝ) * h), g t ≤
        h * ∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) / Real.sqrt X) + h := by
      rw [← hsum_int]
      have hterm : ∀ k ∈ Finset.Icc 1 K,
          ∫ t in (((k - 1 : ℕ) : ℝ) * h)..((k : ℝ) * h), g t ≤ h * g (((k - 1 : ℕ) : ℝ) * h) := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        have hlen : ((k : ℝ) * h) - (((k - 1 : ℕ) : ℝ) * h) = h := by
          have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
            rw [Nat.cast_sub hk.1, Nat.cast_one]
          rw [hk1]; ring
        have hle_ab : ((k - 1 : ℕ) : ℝ) * h ≤ (k : ℝ) * h := by
          have : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr (Nat.sub_le k 1)
          nlinarith
        have hkb : (k : ℝ) * h ≤ 1 / Real.sqrt 2 :=
          le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk.2) hhpos.le) hKh_le
        calc ∫ t in (((k - 1 : ℕ) : ℝ) * h)..((k : ℝ) * h), g t
            ≤ ∫ _ in (((k - 1 : ℕ) : ℝ) * h)..((k : ℝ) * h), g (((k - 1 : ℕ) : ℝ) * h) :=
              intervalIntegral.integral_mono_on hle_ab
                (hint_sub _ _ (by positivity) hle_ab hkb) intervalIntegrable_const
                fun t ht => g_antitoneOn ⟨by positivity, le_trans hle_ab hkb⟩
                  ⟨le_trans (by positivity) ht.1, le_trans ht.2 hkb⟩ ht.1
          _ = h * g (((k - 1 : ℕ) : ℝ) * h) := by
              rw [intervalIntegral.integral_const, smul_eq_mul, hlen]
      have hsum_le : ∑ k ∈ Finset.Icc 1 K, ∫ t in (((k - 1 : ℕ) : ℝ) * h)..((k : ℝ) * h), g t ≤
          h * ∑ k ∈ Finset.Icc 1 K, g (((k - 1 : ℕ) : ℝ) * h) := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum hterm
      have hshift : ∑ k ∈ Finset.Icc 1 K, g (((k - 1 : ℕ) : ℝ) * h) ≤
          1 + ∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) / Real.sqrt X) := by
        rcases Nat.eq_zero_or_pos K with hK0 | hKpos
        · simp [hK0]
        · have hset1 : Finset.Icc 1 K = insert 1 (Finset.Icc 2 K) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          have h1 : ∑ k ∈ Finset.Icc 1 K, g (((k - 1 : ℕ) : ℝ) * h) =
              g 0 + ∑ k ∈ Finset.Icc 1 (K - 1), g ((k : ℝ) * h) := by
            rw [hset1, Finset.sum_insert (by simp)]
            simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_right_inj]
            refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
            · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
            · intro k1 hk1 k2 hk2 heq; rw [Finset.mem_Icc] at hk1 hk2; omega
            · intro j hj; rw [Finset.mem_Icc] at hj
              exact ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
            · intro _ _; rfl
          have hset2 : Finset.Icc 1 K = insert K (Finset.Icc 1 (K - 1)) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          have h2 : ∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) / Real.sqrt X) =
              g ((K : ℝ) * h) + ∑ k ∈ Finset.Icc 1 (K - 1), g ((k : ℝ) * h) := by
            rw [hset2, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
            congr 1
            · simp [h, div_eq_mul_inv]
            · refine Finset.sum_congr rfl fun k _ => ?_; simp [h, div_eq_mul_inv]
          have hlast : 0 ≤ g ((K : ℝ) * h) := g_nonneg ⟨by positivity, hKh_le⟩
          rw [h1, h2, g_zero]
          linarith
      nlinarith
    linarith
  rw [abs_le]
  have h2h : 2 * h = 2 / Real.sqrt X := by dsimp only [h]; ring
  constructor <;> linarith

private lemma G_asymp_bound (X : ℕ) :
    |(G X : ℝ) - (Real.log (1 + Real.sqrt 2) / 4) * (X : ℝ)| ≤ 2 * Real.sqrt X := by
  by_cases hX0 : X = 0
  · subst hX0
    have hG0 : G 0 = 0 := by simp [G_eq_sum_rows]
    simp [hG0]
  have hX1 : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr hX0
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hsqX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  set K := Nat.sqrt (X / 2)
  have hrow_err : |(G X : ℝ) - (Real.sqrt X / 2) *
      ∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) / Real.sqrt X)| ≤ (K : ℝ) / 2 := by
    rw [G_eq_sum_rows X, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc |∑ k ∈ Finset.Icc 1 K,
            ((((rowUpper X k - k + 1) / 2 : ℕ) : ℝ) - (Real.sqrt X / 2) * g ((k : ℝ) / Real.sqrt X))|
        ≤ ∑ k ∈ Finset.Icc 1 K,
            |(((rowUpper X k - k + 1) / 2 : ℕ) : ℝ) - (Real.sqrt X / 2) * g ((k : ℝ) / Real.sqrt X)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.Icc 1 K, (1 / 2 : ℝ) := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [Finset.mem_Icc] at hk
          have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
          have hg_k : Real.sqrt X * g ((k : ℝ) / Real.sqrt X) =
              min (Real.sqrt ((X : ℝ) + (k : ℝ) ^ 2)) ((X : ℝ) / (2 * (k : ℝ))) - (k : ℝ) := by
            rw [g_eq_min (by positivity), mul_sub, mul_min_of_nonneg _ _ hsqX.le]
            congr 1
            · congr 1
              · rw [← Real.sqrt_mul hXpos.le]
                congr 1
                field_simp [hsqX.ne']
                rw [Real.sq_sqrt hXpos.le]
              · field_simp [hsqX.ne', hkpos.ne']
                rw [Real.sq_sqrt hXpos.le]
            · field_simp [hsqX.ne']
          set U := min (Real.sqrt ((X : ℝ) + (k : ℝ) ^ 2)) ((X : ℝ) / (2 * (k : ℝ)))
          have hu_le : (rowUpper X k : ℝ) ≤ U := by
            unfold rowUpper
            rw [Nat.cast_min]
            refine min_le_min ?_ ?_
            · have h1 : (Nat.sqrt (X + k ^ 2) : ℝ) ^ 2 ≤ (X : ℝ) + (k : ℝ) ^ 2 := by
                have := Nat.sqrt_le (X + k ^ 2)
                have : ((Nat.sqrt (X + k ^ 2) * Nat.sqrt (X + k ^ 2) : ℕ) : ℝ) ≤
                    ((X + k ^ 2 : ℕ) : ℝ) := Nat.cast_le.mpr this
                push_cast at this; linarith
              calc (Nat.sqrt (X + k ^ 2) : ℝ) = Real.sqrt ((Nat.sqrt (X + k ^ 2) : ℝ) ^ 2) :=
                    (Real.sqrt_sq (by positivity)).symm
                _ ≤ Real.sqrt ((X : ℝ) + (k : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
            · rw [le_div_iff₀ (by positivity)]
              have := Nat.div_mul_le_self X (2 * k)
              have : ((X / (2 * k) * (2 * k) : ℕ) : ℝ) ≤ (X : ℝ) := Nat.cast_le.mpr this
              push_cast at this; linarith
          have hu_ge : U - 1 ≤ (rowUpper X k : ℝ) := by
            unfold rowUpper
            rw [Nat.cast_min, sub_le_iff_le_add, min_add]
            refine min_le_min ?_ ?_
            · have h1 : (X : ℝ) + (k : ℝ) ^ 2 < ((Nat.sqrt (X + k ^ 2) : ℝ) + 1) ^ 2 := by
                have := Nat.lt_succ_sqrt (X + k ^ 2)
                have : ((X + k ^ 2 : ℕ) : ℝ) < (((Nat.sqrt (X + k ^ 2) + 1) * (Nat.sqrt (X + k ^ 2) + 1) : ℕ) : ℝ) :=
                  Nat.cast_lt.mpr this
                push_cast at this; linarith
              calc Real.sqrt ((X : ℝ) + (k : ℝ) ^ 2)
                  ≤ Real.sqrt (((Nat.sqrt (X + k ^ 2) : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt h1.le
                _ = (Nat.sqrt (X + k ^ 2) : ℝ) + 1 := Real.sqrt_sq (by positivity)
            · rw [div_le_iff₀ (by positivity)]
              have hlt : X < (X / (2 * k) + 1) * (2 * k) := by
                have hdiv := Nat.div_add_mod X (2 * k)
                have hmod := Nat.mod_lt X (show 0 < 2 * k by omega)
                nlinarith
              have : (X : ℝ) < (((X / (2 * k) + 1) * (2 * k) : ℕ) : ℝ) := Nat.cast_lt.mpr hlt
              push_cast at this; linarith
          have hk_le_u : k ≤ rowUpper X k := by
            unfold rowUpper
            refine le_min (Nat.le_sqrt.mpr (by nlinarith)) ?_
            rw [Nat.le_div_iff_mul_le (by omega)]
            have : k * k ≤ X / 2 := Nat.le_sqrt.mp hk.2
            have hmul2 : k * (2 * k) = 2 * (k * k) := by ring
            omega
          have hdiv_le : (((rowUpper X k - k + 1) / 2 : ℕ) : ℝ) ≤
              ((rowUpper X k : ℝ) - (k : ℝ) + 1) / 2 := by
            have h1 : 2 * ((rowUpper X k - k + 1) / 2) ≤ rowUpper X k - k + 1 :=
              Nat.mul_div_le _ 2
            have h2 : ((2 * ((rowUpper X k - k + 1) / 2) : ℕ) : ℝ) ≤
                ((rowUpper X k - k + 1 : ℕ) : ℝ) := Nat.cast_le.mpr h1
            rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hk_le_u] at h2
            push_cast at h2; linarith
          have hdiv_ge : ((rowUpper X k : ℝ) - (k : ℝ)) / 2 ≤
              (((rowUpper X k - k + 1) / 2 : ℕ) : ℝ) := by
            have h1 : rowUpper X k - k ≤ 2 * ((rowUpper X k - k + 1) / 2) := by omega
            have h2 : ((rowUpper X k - k : ℕ) : ℝ) ≤
                ((2 * ((rowUpper X k - k + 1) / 2) : ℕ) : ℝ) := Nat.cast_le.mpr h1
            rw [Nat.cast_sub hk_le_u, Nat.cast_mul] at h2
            push_cast at h2; linarith
          have htarget : (Real.sqrt X / 2) * g ((k : ℝ) / Real.sqrt X) = (U - (k : ℝ)) / 2 := by
            rw [div_mul_eq_mul_div, hg_k]
          rw [htarget, abs_le]
          constructor <;> linarith
      _ = (K : ℝ) / 2 := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring
  have hriem := riemann_sum_g_bound X hX1
  have hriem' : |(Real.sqrt X / 2) * ∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) / Real.sqrt X) -
      (Real.log (1 + Real.sqrt 2) / 4) * (X : ℝ)| ≤ Real.sqrt X := by
    have hXhalf : (0 : ℝ) ≤ (X : ℝ) / 2 := by positivity
    have hmul : |(X : ℝ) / 2 *
        ((1 / Real.sqrt X) * ∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) / Real.sqrt X) -
          Real.log (1 + Real.sqrt 2) / 2)| ≤ (X : ℝ) / 2 * (2 / Real.sqrt X) := by
      rw [abs_mul, abs_of_nonneg hXhalf]
      exact mul_le_mul_of_nonneg_left hriem hXhalf
    have hlhs : (X : ℝ) / 2 *
        ((1 / Real.sqrt X) * ∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) / Real.sqrt X) -
          Real.log (1 + Real.sqrt 2) / 2) =
        (Real.sqrt X / 2) * ∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) / Real.sqrt X) -
          (Real.log (1 + Real.sqrt 2) / 4) * (X : ℝ) := by
      set S := ∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) / Real.sqrt X)
      have h1 : (X : ℝ) / 2 * (1 / Real.sqrt X) = Real.sqrt X / 2 := by
        field_simp [hsqX.ne']
        exact (Real.sq_sqrt hXpos.le).symm
      calc (X : ℝ) / 2 * ((1 / Real.sqrt X) * S - Real.log (1 + Real.sqrt 2) / 2)
          = ((X : ℝ) / 2 * (1 / Real.sqrt X)) * S - (X : ℝ) / 2 * (Real.log (1 + Real.sqrt 2) / 2) := by ring
        _ = (Real.sqrt X / 2) * S - (Real.log (1 + Real.sqrt 2) / 4) * (X : ℝ) := by rw [h1]; ring
    have hrhs : (X : ℝ) / 2 * (2 / Real.sqrt X) = Real.sqrt X := by
      field_simp [hsqX.ne']
      exact (Real.sq_sqrt hXpos.le).symm
    rwa [hlhs, hrhs] at hmul
  have hK_le : (K : ℝ) ≤ Real.sqrt X := by
    have h1 : K * K ≤ X := by
      have hsq : K * K ≤ X / 2 := Nat.sqrt_le (X / 2)
      omega
    have h2 : (K : ℝ) ^ 2 ≤ (X : ℝ) := by
      have : ((K * K : ℕ) : ℝ) ≤ (X : ℝ) := Nat.cast_le.mpr h1
      push_cast at this; linarith
    calc (K : ℝ) = Real.sqrt ((K : ℝ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt X := Real.sqrt_le_sqrt h2
  set S_g := (Real.sqrt X / 2) * ∑ k ∈ Finset.Icc 1 K, g ((k : ℝ) / Real.sqrt X)
  have hsplit_eq : (G X : ℝ) - (Real.log (1 + Real.sqrt 2) / 4) * (X : ℝ) =
      ((G X : ℝ) - S_g) + (S_g - (Real.log (1 + Real.sqrt 2) / 4) * (X : ℝ)) := by ring
  calc |(G X : ℝ) - (Real.log (1 + Real.sqrt 2) / 4) * (X : ℝ)|
      = |((G X : ℝ) - S_g) + (S_g - (Real.log (1 + Real.sqrt 2) / 4) * (X : ℝ))| := by
        rw [hsplit_eq]
    _ ≤ |(G X : ℝ) - S_g| + |S_g - (Real.log (1 + Real.sqrt 2) / 4) * (X : ℝ)| := abs_add_le _ _
    _ ≤ (K : ℝ) / 2 + Real.sqrt X := add_le_add hrow_err hriem'
    _ ≤ 2 * Real.sqrt X := by linarith

/-! ### Part 4: Odd Möbius Series `∑_{d odd} μ(d)/d² = 8/π²` -/

section MoebiusSeries

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

private noncomputable def moebiusTerm (d : ℕ) : ℝ :=
  (μ d : ℝ) / (d : ℝ) ^ 2

private noncomputable def moebiusOddTerm (d : ℕ) : ℝ :=
  if d % 2 = 1 then moebiusTerm d else 0

private noncomputable def moebiusEvenTerm (d : ℕ) : ℝ :=
  if d % 2 = 0 then moebiusTerm d else 0

private lemma summable_moebiusTerm : Summable moebiusTerm := by
  refine Summable.of_norm_bounded (g := fun d : ℕ => (1 : ℝ) / (d : ℝ) ^ 2)
    hasSum_zeta_two.summable fun d => ?_
  simp only [moebiusTerm, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
  have hμ : |(μ d : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := d)
    exact_mod_cast this
  exact div_le_div_of_nonneg_right hμ (by positivity)

private lemma summable_moebiusOddTerm : Summable moebiusOddTerm := by
  refine Summable.of_norm_bounded (g := fun d : ℕ => (1 : ℝ) / (d : ℝ) ^ 2)
    hasSum_zeta_two.summable fun d => ?_
  unfold moebiusOddTerm
  split_ifs
  · simp only [moebiusTerm, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    have hμ : |(μ d : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := d)
      exact_mod_cast this
    exact div_le_div_of_nonneg_right hμ (by positivity)
  · simp

private lemma summable_moebiusEvenTerm : Summable moebiusEvenTerm := by
  refine Summable.of_norm_bounded (g := fun d : ℕ => (1 : ℝ) / (d : ℝ) ^ 2)
    hasSum_zeta_two.summable fun d => ?_
  unfold moebiusEvenTerm
  split_ifs
  · simp only [moebiusTerm, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    have hμ : |(μ d : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := d)
      exact_mod_cast this
    exact div_le_div_of_nonneg_right hμ (by positivity)
  · simp

private lemma tsum_moebiusTerm : ∑' d : ℕ, moebiusTerm d = 6 / Real.pi ^ 2 := by
  have hL := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (s := (2 : ℂ)) (by norm_num)
  have hLz : LSeries (fun n : ℕ => (ζ n : ℂ)) (2 : ℂ) = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
    have hz : HasSum (fun n : ℕ => (((1 : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ))
        ((Real.pi ^ 2 / 6 : ℝ) : ℂ) :=
      hasSum_zeta_two.map Complex.ofRealCLM Complex.continuous_ofReal
    have hterm : ∀ n : ℕ, LSeries.term (fun n : ℕ => (ζ n : ℂ)) (2 : ℂ) n =
        (((1 : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
      intro n
      by_cases hn : n = 0
      · subst hn; simp [LSeries.term]
      · simp [LSeries.term, hn, ArithmeticFunction.zeta_apply]
    rw [LSeries, tsum_congr hterm]
    exact hz.tsum_eq
  have hLμ : LSeries (fun n : ℕ => (μ n : ℂ)) (2 : ℂ) = ((∑' d : ℕ, moebiusTerm d : ℝ) : ℂ) := by
    have hterm : ∀ n : ℕ, LSeries.term (fun n : ℕ => (μ n : ℂ)) (2 : ℂ) n =
        ((moebiusTerm n : ℝ) : ℂ) := by
      intro n
      by_cases hn : n = 0
      · subst hn; simp [LSeries.term, moebiusTerm]
      · simp [LSeries.term, hn, moebiusTerm]
    rw [LSeries, tsum_congr hterm, Complex.ofReal_tsum]
  rw [hLz, hLμ, ← Complex.ofReal_mul, ← Complex.ofReal_one] at hL
  have hR : (Real.pi ^ 2 / 6) * (∑' d : ℕ, moebiusTerm d) = 1 := Complex.ofReal_inj.mp hL
  have hpi : Real.pi ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  field_simp [hpi] at hR ⊢
  linarith

private lemma tsum_moebiusEvenTerm :
    ∑' d : ℕ, moebiusEvenTerm d = -(1 / 4 : ℝ) * ∑' m : ℕ, moebiusOddTerm m := by
  have h1 : ∑' d : ℕ, moebiusEvenTerm d = ∑' m : ℕ, moebiusEvenTerm (2 * m) := by
    symm
    have hmul2 : Function.Injective (fun m : ℕ => 2 * m) := fun _ _ h => by dsimp only at h; omega
    refine hmul2.tsum_eq ?_
    intro d hd
    have hev : d % 2 = 0 := by
      by_contra h
      exact hd (by simp [moebiusEvenTerm, h])
    exact ⟨d / 2, by dsimp only; omega⟩
  rw [h1, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  unfold moebiusEvenTerm moebiusOddTerm moebiusTerm
  rw [if_pos (by omega : 2 * m % 2 = 0)]
  by_cases hm : m % 2 = 1
  · rw [if_pos hm]
    have hcop : Nat.Coprime 2 m := by
      rw [Nat.coprime_two_left]; exact Nat.odd_iff.mpr hm
    have hμ2m : μ (2 * m) = -μ m := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        ArithmeticFunction.moebius_apply_prime Nat.prime_two]
      ring
    rw [hμ2m]
    push_cast
    ring
  · rw [if_neg hm, mul_zero]
    by_cases hm0 : m = 0
    · subst hm0; simp
    · have hnot_sf : ¬ Squarefree (2 * m) := by
        intro hsf
        have h4 : 2 * 2 ∣ 2 * m := by
          have : 2 ∣ m := by omega
          rcases this with ⟨k, rfl⟩
          exact ⟨k, by ring⟩
        have hunit := Nat.isUnit_iff.mp (hsf 2 h4)
        omega
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot_sf]
      simp

private lemma hasSum_moebiusOddTerm : HasSum moebiusOddTerm (8 / Real.pi ^ 2) := by
  have hsplit : ∑' d : ℕ, moebiusTerm d =
      (∑' d : ℕ, moebiusOddTerm d) + (∑' d : ℕ, moebiusEvenTerm d) := by
    rw [← summable_moebiusOddTerm.tsum_add summable_moebiusEvenTerm]
    refine tsum_congr fun d => ?_
    unfold moebiusOddTerm moebiusEvenTerm
    rcases Nat.mod_two_eq_zero_or_one d with h | h <;> simp [h]
  rw [tsum_moebiusTerm, tsum_moebiusEvenTerm] at hsplit
  have hval : ∑' d : ℕ, moebiusOddTerm d = 8 / Real.pi ^ 2 := by
    calc ∑' d : ℕ, moebiusOddTerm d
        = (4 / 3 : ℝ) * (6 / Real.pi ^ 2) := by linarith
      _ = 8 / Real.pi ^ 2 := by ring
  rw [← hval]
  exact summable_moebiusOddTerm.hasSum

private lemma tendsto_partial_moebiusOdd :
    Tendsto (fun M : ℕ => ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d % 2 = 1),
      (μ d : ℝ) / (d : ℝ) ^ 2) atTop (𝓝 (8 / Real.pi ^ 2)) := by
  have hrange : Tendsto (fun N : ℕ => ∑ d ∈ Finset.range N, moebiusOddTerm d)
      atTop (𝓝 (8 / Real.pi ^ 2)) :=
    hasSum_moebiusOddTerm.tendsto_sum_nat
  have hsqrt : Tendsto (fun M : ℕ => Nat.sqrt M + 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b ^ 2, fun M hM => ?_⟩
    have : b ≤ Nat.sqrt M := Nat.le_sqrt.mpr (by nlinarith)
    omega
  have hcomp := hrange.comp hsqrt
  refine hcomp.congr fun M => ?_
  dsimp only [Function.comp_apply]
  have h0 : moebiusOddTerm 0 = 0 := by simp [moebiusOddTerm]
  rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos _), h0, zero_add]
  have hIco : Finset.Ico 1 (Nat.sqrt M + 1) = Finset.Icc 1 (Nat.sqrt M) := rfl
  rw [hIco]
  simp only [moebiusOddTerm, moebiusTerm, ← Finset.sum_filter]

end MoebiusSeries

/-! ### Part 5: Final Limit Assembly -/

private lemma harmonic_le_two_sqrt (S : ℕ) :
    ∑ d ∈ Finset.Icc 1 S, (1 : ℝ) / (d : ℝ) ≤ 2 * Real.sqrt S := by
  induction S with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_pos m)]
    have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 2 * (Real.sqrt (m + 1 : ℕ) - Real.sqrt m) := by
      have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hsr1 : 0 < Real.sqrt (m + 1 : ℕ) := Real.sqrt_pos.mpr hm1
      have hsr_le : Real.sqrt m ≤ Real.sqrt (m + 1 : ℕ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ m)
      have hsum_pos : 0 < Real.sqrt (m + 1 : ℕ) + Real.sqrt m := by positivity
      have hdiff : (Real.sqrt (m + 1 : ℕ) - Real.sqrt m) *
          (Real.sqrt (m + 1 : ℕ) + Real.sqrt m) = 1 := by
        have h1 : Real.sqrt (m + 1 : ℕ) ^ 2 = ((m + 1 : ℕ) : ℝ) := Real.sq_sqrt hm1.le
        have h2 : Real.sqrt m ^ 2 = (m : ℝ) := Real.sq_sqrt (by positivity)
        push_cast at h1 ⊢
        nlinarith
      have hsr_le_self : Real.sqrt (m + 1 : ℕ) ≤ ((m + 1 : ℕ) : ℝ) := by
        have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
        have hsq : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
        calc Real.sqrt (m + 1 : ℕ) ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
          _ = ((m + 1 : ℕ) : ℝ) := Real.sqrt_sq hm1.le
      rw [div_le_iff₀ hm1]
      have : Real.sqrt (m + 1 : ℕ) + Real.sqrt m ≤ 2 * ((m + 1 : ℕ) : ℝ) := by linarith
      nlinarith
    linarith

private lemma tendsto_a_succ_div :
    Tendsto (fun M : ℕ => (OMA.S_oeis_a156684.a (M + 1) : ℝ) / (M : ℝ)) atTop
      (𝓝 (2 / Real.pi ^ 2 * Real.log (1 + Real.sqrt 2))) := by
  set c : ℝ := Real.log (1 + Real.sqrt 2) / 4
  have hc_pos : 0 ≤ c := by
    refine div_nonneg (Real.log_nonneg ?_) (by norm_num)
    have : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    linarith
  have hmain_lim : Tendsto (fun M : ℕ =>
      c * ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d % 2 = 1),
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) atTop
      (𝓝 (2 / Real.pi ^ 2 * Real.log (1 + Real.sqrt 2))) := by
    have h := tendsto_partial_moebiusOdd.const_mul c
    convert h using 2
    simp only [c]; ring
  have herr : Tendsto (fun M : ℕ =>
      (OMA.S_oeis_a156684.a (M + 1) : ℝ) / (M : ℝ) -
      c * ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d % 2 = 1),
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) atTop (𝓝 0) := by
    have hbound_lim : Tendsto (fun M : ℕ =>
        4 / Real.sqrt (Real.sqrt (M : ℝ)) + c / Real.sqrt (M : ℝ)) atTop (𝓝 0) := by
      have hsq : Tendsto (fun M : ℕ => Real.sqrt (M : ℝ)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      have hsq2 : Tendsto (fun M : ℕ => Real.sqrt (Real.sqrt (M : ℝ))) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp hsq
      have h1 : Tendsto (fun M : ℕ => 4 / Real.sqrt (Real.sqrt (M : ℝ))) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hsq2
      have h2 : Tendsto (fun M : ℕ => c / Real.sqrt (M : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hsq
      simpa using h1.add h2
    refine squeeze_zero_norm' ?_ hbound_lim
    filter_upwards [eventually_ge_atTop 1] with M hM
    rw [Real.norm_eq_abs, a_succ_eq_moebius_sum_real M, Finset.sum_div, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
    have hsqM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMpos
    set D := (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d % 2 = 1)
    calc |∑ d ∈ D, ((ArithmeticFunction.moebius d : ℝ) * (G (M / d ^ 2) : ℝ) / (M : ℝ) -
            c * ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2))|
        ≤ ∑ d ∈ D, |(ArithmeticFunction.moebius d : ℝ) * (G (M / d ^ 2) : ℝ) / (M : ℝ) -
            c * ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ D, (2 / (Real.sqrt (M : ℝ) * (d : ℝ)) + c / (M : ℝ)) := by
          refine Finset.sum_le_sum fun d hd => ?_
          simp only [D, Finset.mem_filter, Finset.mem_Icc] at hd
          have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
          have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
            have := ArithmeticFunction.abs_moebius_le_one (n := d)
            exact_mod_cast this
          have hrew : (ArithmeticFunction.moebius d : ℝ) * (G (M / d ^ 2) : ℝ) / (M : ℝ) -
              c * ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) =
              (ArithmeticFunction.moebius d : ℝ) *
                ((G (M / d ^ 2) : ℝ) / (M : ℝ) - c / (d : ℝ) ^ 2) := by ring
          rw [hrew, abs_mul]
          have h1 : |(G (M / d ^ 2) : ℝ) - c * (M / d ^ 2 : ℕ)| ≤
              2 * Real.sqrt (M / d ^ 2 : ℕ) := G_asymp_bound (M / d ^ 2)
          have hdiv_le : ((M / d ^ 2 : ℕ) : ℝ) ≤ (M : ℝ) / (d : ℝ) ^ 2 := by
            rw [le_div_iff₀ (by positivity)]
            have := Nat.div_mul_le_self M (d ^ 2)
            have : ((M / d ^ 2 * d ^ 2 : ℕ) : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr this
            push_cast at this; linarith
          have hdiv_ge : (M : ℝ) / (d : ℝ) ^ 2 - 1 ≤ ((M / d ^ 2 : ℕ) : ℝ) := by
            rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
            have hd_nat : 0 < d := by omega
            have hlt : M < (M / d ^ 2 + 1) * d ^ 2 := by
              have hdiv := Nat.div_add_mod M (d ^ 2)
              have hmod := Nat.mod_lt M (show 0 < d ^ 2 by positivity)
              nlinarith
            have : (M : ℝ) < (((M / d ^ 2 + 1) * d ^ 2 : ℕ) : ℝ) := Nat.cast_lt.mpr hlt
            push_cast at this; linarith
          have hsq_le : Real.sqrt (M / d ^ 2 : ℕ) ≤ Real.sqrt (M : ℝ) / (d : ℝ) := by
            calc Real.sqrt (M / d ^ 2 : ℕ)
                ≤ Real.sqrt ((M : ℝ) / (d : ℝ) ^ 2) := Real.sqrt_le_sqrt hdiv_le
              _ = Real.sqrt (M : ℝ) / Real.sqrt ((d : ℝ) ^ 2) := Real.sqrt_div hMpos.le _
              _ = Real.sqrt (M : ℝ) / (d : ℝ) := by rw [Real.sqrt_sq hdpos.le]
          have h2 : |(G (M / d ^ 2) : ℝ) - c * ((M : ℝ) / (d : ℝ) ^ 2)| ≤
              2 * (Real.sqrt (M : ℝ) / (d : ℝ)) + c := by
            have hdiff : |(c * ((M / d ^ 2 : ℕ) : ℝ)) - c * ((M : ℝ) / (d : ℝ) ^ 2)| ≤ c := by
              rw [← mul_sub, abs_mul, abs_of_nonneg hc_pos]
              have : |((M / d ^ 2 : ℕ) : ℝ) - (M : ℝ) / (d : ℝ) ^ 2| ≤ 1 := by
                rw [abs_le]; constructor <;> linarith
              nlinarith
            have hsp : (G (M / d ^ 2) : ℝ) - c * ((M : ℝ) / (d : ℝ) ^ 2) =
                ((G (M / d ^ 2) : ℝ) - c * ((M / d ^ 2 : ℕ) : ℝ)) +
                (c * ((M / d ^ 2 : ℕ) : ℝ) - c * ((M : ℝ) / (d : ℝ) ^ 2)) := by ring
            calc |(G (M / d ^ 2) : ℝ) - c * ((M : ℝ) / (d : ℝ) ^ 2)|
                = |((G (M / d ^ 2) : ℝ) - c * ((M / d ^ 2 : ℕ) : ℝ)) +
                   (c * ((M / d ^ 2 : ℕ) : ℝ) - c * ((M : ℝ) / (d : ℝ) ^ 2))| := by rw [hsp]
              _ ≤ |(G (M / d ^ 2) : ℝ) - c * ((M / d ^ 2 : ℕ) : ℝ)| +
                  |c * ((M / d ^ 2 : ℕ) : ℝ) - c * ((M : ℝ) / (d : ℝ) ^ 2)| := abs_add_le _ _
              _ ≤ 2 * Real.sqrt (M / d ^ 2 : ℕ) + c := add_le_add h1 hdiff
              _ ≤ 2 * (Real.sqrt (M : ℝ) / (d : ℝ)) + c := by linarith
          have h3 : |(G (M / d ^ 2) : ℝ) / (M : ℝ) - c / (d : ℝ) ^ 2| ≤
              2 / (Real.sqrt (M : ℝ) * (d : ℝ)) + c / (M : ℝ) := by
            have heq : (G (M / d ^ 2) : ℝ) / (M : ℝ) - c / (d : ℝ) ^ 2 =
                ((G (M / d ^ 2) : ℝ) - c * ((M : ℝ) / (d : ℝ) ^ 2)) / (M : ℝ) := by
              field_simp [hMpos.ne', hdpos.ne']
            rw [heq, abs_div, abs_of_pos hMpos]
            calc |(G (M / d ^ 2) : ℝ) - c * ((M : ℝ) / (d : ℝ) ^ 2)| / (M : ℝ)
                ≤ (2 * (Real.sqrt (M : ℝ) / (d : ℝ)) + c) / (M : ℝ) :=
                  div_le_div_of_nonneg_right h2 hMpos.le
              _ = 2 / (Real.sqrt (M : ℝ) * (d : ℝ)) + c / (M : ℝ) := by
                  field_simp [hMpos.ne', hsqM.ne', hdpos.ne']
                  nlinarith [Real.sq_sqrt hMpos.le]
          calc |(ArithmeticFunction.moebius d : ℝ)| *
                |(G (M / d ^ 2) : ℝ) / (M : ℝ) - c / (d : ℝ) ^ 2|
              ≤ 1 * (2 / (Real.sqrt (M : ℝ) * (d : ℝ)) + c / (M : ℝ)) :=
                mul_le_mul hμ h3 (abs_nonneg _) zero_le_one
            _ = 2 / (Real.sqrt (M : ℝ) * (d : ℝ)) + c / (M : ℝ) := one_mul _
      _ ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt M), (2 / (Real.sqrt (M : ℝ) * (d : ℝ)) + c / (M : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro d _ _; positivity
      _ = (2 / Real.sqrt (M : ℝ)) * (∑ d ∈ Finset.Icc 1 (Nat.sqrt M), (1 : ℝ) / (d : ℝ)) +
          (Nat.sqrt M : ℝ) * (c / (M : ℝ)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
          simp only [Nat.card_Icc, Nat.add_sub_cancel]
          congr 1
          refine Finset.sum_congr rfl fun d _ => ?_
          ring
      _ ≤ (2 / Real.sqrt (M : ℝ)) * (2 * Real.sqrt (Nat.sqrt M)) +
          Real.sqrt (M : ℝ) * (c / (M : ℝ)) := by
          have hS : (Nat.sqrt M : ℝ) ≤ Real.sqrt (M : ℝ) := by
            have h1 : (Nat.sqrt M : ℝ) ^ 2 ≤ (M : ℝ) := by
              have := Nat.sqrt_le M
              have : ((Nat.sqrt M * Nat.sqrt M : ℕ) : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr this
              push_cast at this; linarith
            calc (Nat.sqrt M : ℝ) = Real.sqrt ((Nat.sqrt M : ℝ) ^ 2) :=
                  (Real.sqrt_sq (by positivity)).symm
              _ ≤ Real.sqrt (M : ℝ) := Real.sqrt_le_sqrt h1
          exact add_le_add
            (mul_le_mul_of_nonneg_left (harmonic_le_two_sqrt (Nat.sqrt M)) (by positivity))
            (mul_le_mul_of_nonneg_right hS (by positivity))
      _ ≤ 4 / Real.sqrt (Real.sqrt (M : ℝ)) + c / Real.sqrt (M : ℝ) := by
          have hS : (Nat.sqrt M : ℝ) ≤ Real.sqrt (M : ℝ) := by
            have h1 : (Nat.sqrt M : ℝ) ^ 2 ≤ (M : ℝ) := by
              have := Nat.sqrt_le M
              have : ((Nat.sqrt M * Nat.sqrt M : ℕ) : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr this
              push_cast at this; linarith
            calc (Nat.sqrt M : ℝ) = Real.sqrt ((Nat.sqrt M : ℝ) ^ 2) :=
                  (Real.sqrt_sq (by positivity)).symm
              _ ≤ Real.sqrt (M : ℝ) := Real.sqrt_le_sqrt h1
          have hS_sq : Real.sqrt (Nat.sqrt M) ≤ Real.sqrt (Real.sqrt (M : ℝ)) :=
            Real.sqrt_le_sqrt hS
          have h1 : (2 / Real.sqrt (M : ℝ)) * (2 * Real.sqrt (Nat.sqrt M)) ≤
              4 / Real.sqrt (Real.sqrt (M : ℝ)) := by
            have hsq4 : 0 < Real.sqrt (Real.sqrt (M : ℝ)) := Real.sqrt_pos.mpr hsqM
            calc (2 / Real.sqrt (M : ℝ)) * (2 * Real.sqrt (Nat.sqrt M))
                ≤ (2 / Real.sqrt (M : ℝ)) * (2 * Real.sqrt (Real.sqrt (M : ℝ))) :=
                  mul_le_mul_of_nonneg_left (by linarith) (by positivity)
              _ = 4 / Real.sqrt (Real.sqrt (M : ℝ)) := by
                  field_simp [hsqM.ne', hsq4.ne']
                  rw [Real.sq_sqrt hsqM.le]
                  ring
          have h2 : Real.sqrt (M : ℝ) * (c / (M : ℝ)) = c / Real.sqrt (M : ℝ) := by
            field_simp [hMpos.ne', hsqM.ne']
            rw [Real.sq_sqrt hMpos.le]
            ring
          linarith
  have hcomb := herr.add hmain_lim
  simpa using hcomb

end OeisA156684Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a156684.main := by
  have h1 : Tendsto (fun n : ℕ => (OMA.S_oeis_a156684.a n : ℝ) / ((n - 1 : ℕ) : ℝ)) atTop
      (𝓝 (2 / Real.pi ^ 2 * Real.log (1 + Real.sqrt 2))) := by
    have hshift := OeisA156684Proof.tendsto_a_succ_div.comp (tendsto_sub_atTop_nat 1)
    refine hshift.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp_apply, Nat.sub_add_cancel hn]
  have h2 : Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ => 1 - (1 : ℝ) / (n : ℝ)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    rw [sub_zero] at hinv
    refine hinv.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_sub hn, Nat.cast_one]
    field_simp [hn0]
  have h3 := h1.mul h2
  rw [mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnm : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
    have : 1 ≤ n - 1 := by omega
    positivity
  field_simp [hnm]
