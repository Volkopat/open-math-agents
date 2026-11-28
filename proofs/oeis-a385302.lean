import OMAStatements.S_oeis_a385302

-- Problem: A385302: Least common multiple of {n^n-1, n^(n-1)-1, ..., n-1}.
-- Upstream: formal-conjectures statements/oeis-a385302.lean:0 (declaration OMA.S_oeis_a385302.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: For n >= 2, both sides are positive integers. For every prime p not dividing n, let d
-- be the least positive integer with p | n^d - 1. If d <= n and J is maximal with d * p^J <= n,
-- the geometric-sum factorization of n^k - 1 shows both sides have p-adic valuation v_p(n^(d*p^J) - 1);
-- if p | n or d > n, both valuations are 0. The second equality follows from sInf {r | tri n - 1 <= tri r} = n.

open OMA.S_oeis_a385302 in
theorem OMA.solution : type_of% @OMA.S_oeis_a385302.main := by
  have hmain1 : ∀ n : ℕ, (a n : ℤ) =
      ∏ k ∈ Finset.Icc 1 n, (Polynomial.cyclotomic k ℤ).eval (n : ℤ) := by
    intro n
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · interval_cases n
      · unfold a
        simp
      · unfold a
        simp [Polynomial.cyclotomic_one]
    · let phi : ℕ → ℤ := fun k => (Polynomial.cyclotomic k ℤ).eval (n : ℤ)
      have hprod_int : ∀ k : ℕ, 0 < k → ∏ d ∈ k.divisors, phi d = (n : ℤ) ^ k - 1 := by
        intro k hk
        have h := congr_arg (Polynomial.evalRingHom (n : ℤ))
          (Polynomial.prod_cyclotomic_eq_X_pow_sub_one hk ℤ)
        simp only [map_prod, map_sub, map_pow, map_one, Polynomial.coe_evalRingHom,
          Polynomial.eval_X] at h
        exact h
      have hpow_gt : ∀ k : ℕ, 1 ≤ k → 1 < n ^ k := by
        intro k hk
        calc 1 < 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
          _ ≤ n ^ k := Nat.pow_le_pow_left hn2 k
      have hphi_pos : ∀ k : ℕ, 1 ≤ k → 0 < phi k := by
        intro k
        induction k using Nat.strong_induction_on with
        | h k ih =>
          intro hk
          have hk0 : k ≠ 0 := by omega
          have hmem : k ∈ k.divisors := Nat.mem_divisors.mpr ⟨dvd_refl k, hk0⟩
          have hmul : phi k * ∏ d ∈ k.divisors.erase k, phi d = (n : ℤ) ^ k - 1 := by
            rw [Finset.mul_prod_erase _ _ hmem]
            exact hprod_int k (by omega)
          have herase_pos : 0 < ∏ d ∈ k.divisors.erase k, phi d := by
            apply Finset.prod_pos
            intro d hd
            rw [Finset.mem_erase, Nat.mem_divisors] at hd
            have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd.2.1 (by omega)
            have hdlt : d < k := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hd.2.1) hd.1
            exact ih d hdlt hd1
          have hrhs_pos : (0 : ℤ) < (n : ℤ) ^ k - 1 := by
            have h1 := hpow_gt k hk
            have h1z : (1 : ℤ) < (n : ℤ) ^ k := by exact_mod_cast h1
            linarith
          exact pos_of_mul_pos_left (by linarith) (le_of_lt herase_pos)
      let phiNat : ℕ → ℕ := fun k => (phi k).toNat
      have hphiNat_cast : ∀ k : ℕ, 1 ≤ k → (phiNat k : ℤ) = phi k := by
        intro k hk
        exact Int.toNat_of_nonneg (le_of_lt (hphi_pos k hk))
      have hphiNat_pos : ∀ k : ℕ, 1 ≤ k → 0 < phiNat k := by
        intro k hk
        have h1 := hphi_pos k hk
        have h2 := hphiNat_cast k hk
        omega
      have hprod_nat : ∀ k : ℕ, 1 ≤ k → ∏ d ∈ k.divisors, phiNat d = n ^ k - 1 := by
        intro k hk
        have h1 : ((∏ d ∈ k.divisors, phiNat d : ℕ) : ℤ) = ((n ^ k - 1 : ℕ) : ℤ) := by
          rw [Nat.cast_prod]
          have hcongr : ∏ d ∈ k.divisors, (phiNat d : ℤ) = ∏ d ∈ k.divisors, phi d := by
            refine Finset.prod_congr rfl fun d hd => ?_
            have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 (by omega)
            exact hphiNat_cast d hd1
          rw [hcongr, hprod_int k (by omega)]
          have hge : 1 ≤ n ^ k := le_of_lt (hpow_gt k hk)
          rw [Nat.cast_sub hge, Nat.cast_pow, Nat.cast_one]
        exact_mod_cast h1
      have hphi_dvd : ∀ k : ℕ, 1 ≤ k → phiNat k ∣ n ^ k - 1 := by
        intro k hk
        rw [← hprod_nat k hk]
        exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors.mpr ⟨dvd_refl k, by omega⟩)
      have hP_cast : ((∏ k ∈ Finset.Icc 1 n, phiNat k : ℕ) : ℤ) =
          ∏ k ∈ Finset.Icc 1 n, phi k := by
        rw [Nat.cast_prod]
        refine Finset.prod_congr rfl fun k hk => hphiNat_cast k (Finset.mem_Icc.mp hk).1
      rw [← hP_cast]
      apply congr_arg (Nat.cast : ℕ → ℤ)
      have hL_ne : a n ≠ 0 := by
        unfold a
        have haux : ∀ s : Finset ℕ, (∀ k ∈ s, 1 ≤ k) → s.lcm (fun k => n ^ k - 1) ≠ 0 := by
          intro s
          induction s using Finset.induction_on with
          | empty =>
            intro _
            simp
          | insert x s hxs ih =>
            intro hs
            rw [Finset.lcm_insert]
            have hx1 : 1 ≤ x := hs x (Finset.mem_insert_self x s)
            have hx0 : n ^ x - 1 ≠ 0 := by
              have := hpow_gt x hx1
              omega
            have hs0 : s.lcm (fun k => n ^ k - 1) ≠ 0 :=
              ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))
            exact Nat.lcm_ne_zero hx0 hs0
        exact haux (Finset.Icc 1 n) (fun k hk => (Finset.mem_Icc.mp hk).1)
      have hP_ne : ∏ k ∈ Finset.Icc 1 n, phiNat k ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro k hk
        exact (hphiNat_pos k (Finset.mem_Icc.mp hk).1).ne'
      apply Nat.eq_of_factorization_eq hL_ne hP_ne
      intro p
      by_cases hp : p.Prime
      · have hlcm_fac_le : ∀ (s : Finset ℕ) (M : ℕ), (∀ k ∈ s, 1 ≤ k) →
            (∀ k ∈ s, (n ^ k - 1).factorization p ≤ M) →
            (s.lcm (fun k => n ^ k - 1)).factorization p ≤ M := by
          intro s M
          induction s using Finset.induction_on with
          | empty =>
            intro _ _
            simp
          | insert x s hxs ih =>
            intro hs1 hsM
            rw [Finset.lcm_insert]
            have hx1 : 1 ≤ x := hs1 x (Finset.mem_insert_self x s)
            have hx0 : n ^ x - 1 ≠ 0 := by
              have := hpow_gt x hx1
              omega
            have hs0 : s.lcm (fun k => n ^ k - 1) ≠ 0 := by
              have haux : ∀ t : Finset ℕ, (∀ k ∈ t, 1 ≤ k) → t.lcm (fun k => n ^ k - 1) ≠ 0 := by
                intro t
                induction t using Finset.induction_on with
                | empty => intro _; simp
                | insert y t hyt iht =>
                  intro ht1
                  rw [Finset.lcm_insert]
                  have hy0 : n ^ y - 1 ≠ 0 := by
                    have := hpow_gt y (ht1 y (Finset.mem_insert_self y t))
                    omega
                  exact Nat.lcm_ne_zero hy0 (iht (fun k hk => ht1 k (Finset.mem_insert_of_mem hk)))
              exact haux s (fun k hk => hs1 k (Finset.mem_insert_of_mem hk))
            change (Nat.lcm (n ^ x - 1) (s.lcm (fun k => n ^ k - 1))).factorization p ≤ M
            rw [Nat.factorization_lcm hx0 hs0]
            simp only [Finsupp.sup_apply, sup_le_iff]
            exact ⟨hsM x (Finset.mem_insert_self x s),
              ih (fun k hk => hs1 k (Finset.mem_insert_of_mem hk))
                (fun k hk => hsM k (Finset.mem_insert_of_mem hk))⟩
        have hP_fac : (∏ k ∈ Finset.Icc 1 n, phiNat k).factorization p =
            ∑ k ∈ Finset.Icc 1 n, (phiNat k).factorization p := by
          rw [Nat.factorization_prod (fun k hk => (hphiNat_pos k (Finset.mem_Icc.mp hk).1).ne')]
          simp
        by_cases hpn : p ∣ n
        · have hnot_dvd : ∀ k : ℕ, 1 ≤ k → ¬ (p ∣ n ^ k - 1) := by
            intro k hk hdiv
            have hp_pow : p ∣ n ^ k := dvd_pow hpn (by omega)
            have hge : 1 ≤ n ^ k := le_of_lt (hpow_gt k hk)
            have h1 : p ∣ 1 := by
              have hadd : n ^ k - 1 + 1 = n ^ k := Nat.sub_add_cancel hge
              exact (Nat.dvd_add_right hdiv).mp (hadd.symm ▸ hp_pow)
            exact hp.not_dvd_one h1
          have hL0 : (a n).factorization p = 0 := by
            apply Nat.eq_zero_of_le_zero
            unfold a
            apply hlcm_fac_le _ 0 (fun k hk => (Finset.mem_Icc.mp hk).1)
            intro k hk
            rw [Nat.factorization_eq_zero_of_not_dvd (hnot_dvd k (Finset.mem_Icc.mp hk).1)]
          have hP0 : (∏ k ∈ Finset.Icc 1 n, phiNat k).factorization p = 0 := by
            rw [hP_fac]
            apply Finset.sum_eq_zero
            intro k hk
            have hk1 := (Finset.mem_Icc.mp hk).1
            have hnd : ¬ (p ∣ phiNat k) := fun h => hnot_dvd k hk1 (dvd_trans h (hphi_dvd k hk1))
            exact Nat.factorization_eq_zero_of_not_dvd hnd
          rw [hL0, hP0]
        · have hex_ord : ∃ k : ℕ, 1 ≤ k ∧ p ∣ n ^ k - 1 := by
            refine ⟨p - 1, by have := hp.two_le; omega, ?_⟩
            have : Fact p.Prime := ⟨hp⟩
            have hnz : (n : ZMod p) ≠ 0 := by
              intro h
              exact hpn ((ZMod.natCast_eq_zero_iff n p).mp h)
            have hferm : (n : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hnz
            have hge : 1 ≤ n ^ (p - 1) := le_of_lt (hpow_gt (p - 1) (by have := hp.two_le; omega))
            rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hge, Nat.cast_pow, Nat.cast_one, hferm,
              sub_self]
          let d := Nat.find hex_ord
          have hd_spec : 1 ≤ d ∧ p ∣ n ^ d - 1 := Nat.find_spec hex_ord
          have hd_min : ∀ m : ℕ, m < d → ¬ (1 ≤ m ∧ p ∣ n ^ m - 1) :=
            fun m hm => Nat.find_min hex_ord hm
          have hpow_dvd : ∀ a b : ℕ, 1 ≤ a → a ∣ b → n ^ a - 1 ∣ n ^ b - 1 := by
            intro x y hx hxy
            rcases hxy with ⟨q, rfl⟩
            have hz : ((n : ℤ) ^ x - 1) ∣ ((n : ℤ) ^ (x * q) - 1) := by
              refine ⟨∑ i ∈ Finset.range q, ((n : ℤ) ^ x) ^ i, ?_⟩
              rw [pow_mul]
              exact (geom_sum_mul ((n : ℤ) ^ x) q).symm.trans (mul_comm _ _)
            rcases Nat.eq_zero_or_pos q with rfl | hq
            · simp
            · have hxge : 1 ≤ n ^ x := le_of_lt (hpow_gt x hx)
              have hxyge : 1 ≤ n ^ (x * q) := le_of_lt (hpow_gt (x * q) (Nat.mul_pos hx hq))
              rw [← Int.natCast_dvd_natCast, Nat.cast_sub hxge, Nat.cast_sub hxyge,
                Nat.cast_pow, Nat.cast_pow, Nat.cast_one]
              exact hz
          have hord_iff : ∀ k : ℕ, 1 ≤ k → (p ∣ n ^ k - 1 ↔ d ∣ k) := by
            intro k hk
            constructor
            · intro hpk
              by_contra hnd
              have hr_pos : 1 ≤ k % d := by
                have hne : k % d ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
                omega
              have hr_lt : k % d < d := Nat.mod_lt k (by omega)
              have hdiv_eq : d * (k / d) + k % d = k := Nat.div_add_mod k d
              have hpkz : (p : ℤ) ∣ (n : ℤ) ^ k - 1 := by
                have hge := le_of_lt (hpow_gt k hk)
                have := Int.natCast_dvd_natCast.mpr hpk
                rwa [Nat.cast_sub hge, Nat.cast_pow, Nat.cast_one] at this
              have hpdq : (p : ℤ) ∣ (n : ℤ) ^ (d * (k / d)) - 1 := by
                rcases Nat.eq_zero_or_pos (k / d) with hq0 | hq0
                · rw [hq0, mul_zero, pow_zero, sub_self]
                  exact dvd_zero _
                · have hdvd1 := dvd_trans hd_spec.2 (hpow_dvd d (d * (k / d)) hd_spec.1 (dvd_mul_right d _))
                  have hge := le_of_lt (hpow_gt (d * (k / d)) (Nat.mul_pos hd_spec.1 hq0))
                  have := Int.natCast_dvd_natCast.mpr hdvd1
                  rwa [Nat.cast_sub hge, Nat.cast_pow, Nat.cast_one] at this
              have hid : (n : ℤ) ^ k - 1 =
                  (n : ℤ) ^ (d * (k / d)) * ((n : ℤ) ^ (k % d) - 1) +
                  ((n : ℤ) ^ (d * (k / d)) - 1) := by
                have hk' : (n : ℤ) ^ k = (n : ℤ) ^ (d * (k / d)) * (n : ℤ) ^ (k % d) := by
                  rw [← pow_add, hdiv_eq]
                rw [hk']
                ring
              have hpmul : (p : ℤ) ∣ (n : ℤ) ^ (d * (k / d)) * ((n : ℤ) ^ (k % d) - 1) := by
                have hsub : (n : ℤ) ^ (d * (k / d)) * ((n : ℤ) ^ (k % d) - 1) =
                    ((n : ℤ) ^ k - 1) - ((n : ℤ) ^ (d * (k / d)) - 1) := by linarith
                rw [hsub]
                exact dvd_sub hpkz hpdq
              have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
              have hpr : (p : ℤ) ∣ (n : ℤ) ^ (k % d) - 1 := by
                rcases hpZ.dvd_or_dvd hpmul with h1 | h1
                · exfalso
                  have h2 : (p : ℤ) ∣ (n : ℤ) := hpZ.dvd_of_dvd_pow h1
                  exact hpn (Int.natCast_dvd_natCast.mp h2)
                · exact h1
              have hpr_nat : p ∣ n ^ (k % d) - 1 := by
                have hge := le_of_lt (hpow_gt (k % d) hr_pos)
                rw [← Int.natCast_dvd_natCast, Nat.cast_sub hge, Nat.cast_pow, Nat.cast_one]
                exact hpr
              exact hd_min (k % d) hr_lt ⟨hr_pos, hpr_nat⟩
            · intro hdk
              exact dvd_trans hd_spec.2 (hpow_dvd d k hd_spec.1 hdk)
          have hgeom : ∀ a m : ℕ, 1 ≤ a → d ∣ a → 1 ≤ m → ¬ (p ∣ m) →
              (n ^ (a * m) - 1).factorization p = (n ^ a - 1).factorization p ∧
              (1 < m → (phiNat (a * m)).factorization p = 0) := by
            intro x m hx hdx hm hpm
            let G : ℕ := ∑ i ∈ Finset.range m, (n ^ x) ^ i
            have hG_mul : (n ^ x - 1) * G = n ^ (x * m) - 1 := by
              have hz : ((n ^ x - 1 : ℕ) : ℤ) * (G : ℤ) = ((n ^ (x * m) - 1 : ℕ) : ℤ) := by
                have hxge : 1 ≤ n ^ x := le_of_lt (hpow_gt x hx)
                have hxmge : 1 ≤ n ^ (x * m) := le_of_lt (hpow_gt (x * m) (Nat.mul_pos hx hm))
                rw [Nat.cast_sub hxge, Nat.cast_sub hxmge, Nat.cast_pow, Nat.cast_pow,
                  Nat.cast_one]
                dsimp only [G]
                rw [Nat.cast_sum]
                have hgs := geom_sum_mul ((n : ℤ) ^ x) m
                rw [mul_comm, pow_mul]
                simpa [Nat.cast_pow] using hgs
              exact_mod_cast hz
            have hG_not_dvd : ¬ (p ∣ G) := by
              have hu_mod : n ^ x ≡ 1 [MOD p] := by
                have hpx : p ∣ n ^ x - 1 := (hord_iff x hx).mpr hdx
                rcases hpx with ⟨t, ht⟩
                have hxge : 1 ≤ n ^ x := le_of_lt (hpow_gt x hx)
                have hadd : n ^ x = 1 + p * t := by omega
                rw [Nat.ModEq, hadd, Nat.add_mul_mod_self_left]
              have hG_mod : G ≡ m [MOD p] := by
                dsimp only [G]
                have hsum_mod : ∑ i ∈ Finset.range m, (n ^ x) ^ i ≡
                    ∑ _i ∈ Finset.range m, 1 [MOD p] := by
                  have haux : ∀ r : ℕ, ∑ i ∈ Finset.range r, (n ^ x) ^ i ≡
                      ∑ _i ∈ Finset.range r, 1 [MOD p] := by
                    intro r
                    induction r with
                    | zero => simp [Nat.ModEq.refl]
                    | succ r ihr =>
                      rw [Finset.sum_range_succ, Finset.sum_range_succ]
                      have hpow1 : (n ^ x) ^ r ≡ 1 [MOD p] := by
                        simpa using hu_mod.pow r
                      exact ihr.add hpow1
                  exact haux m
                simpa using hsum_mod
              intro hpG
              have hm0 : m % p = 0 := by
                have := hG_mod.symm
                rw [Nat.ModEq] at this
                rw [this]
                exact Nat.mod_eq_zero_of_dvd hpG
              exact hpm (Nat.dvd_of_mod_eq_zero hm0)
            have hx0 : n ^ x - 1 ≠ 0 := by
              have := hpow_gt x hx
              omega
            have hG0 : G ≠ 0 := fun h => hG_not_dvd (h ▸ dvd_zero p)
            constructor
            · rw [← hG_mul, Nat.factorization_mul hx0 hG0, Finsupp.add_apply,
                Nat.factorization_eq_zero_of_not_dvd hG_not_dvd, add_zero]
            · intro hm1
              have hsub : x.divisors ⊆ (x * m).divisors := by
                intro r hr
                rw [Nat.mem_divisors] at hr ⊢
                exact ⟨dvd_trans hr.1 (dvd_mul_right x m), (Nat.mul_pos hx hm).ne'⟩
              have hprod_split : ∏ r ∈ (x * m).divisors, phiNat r =
                  (∏ r ∈ x.divisors, phiNat r) *
                  (∏ r ∈ (x * m).divisors \ x.divisors, phiNat r) := by
                exact (Finset.prod_sdiff hsub).symm.trans (mul_comm _ _)
              rw [hprod_nat (x * m) (Nat.mul_pos hx hm), hprod_nat x hx] at hprod_split
              have hG_eq : G = ∏ r ∈ (x * m).divisors \ x.divisors, phiNat r :=
                Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hx0) (hG_mul.trans hprod_split)
              have hmem_sdiff : x * m ∈ (x * m).divisors \ x.divisors := by
                rw [Finset.mem_sdiff, Nat.mem_divisors, Nat.mem_divisors]
                refine ⟨⟨dvd_refl _, (Nat.mul_pos hx hm).ne'⟩, ?_⟩
                intro h
                have hle : x * m ≤ x := Nat.le_of_dvd (by omega) h.1
                nlinarith
              have hdivG : phiNat (x * m) ∣ G := by
                rw [hG_eq]
                exact Finset.dvd_prod_of_mem _ hmem_sdiff
              exact Nat.factorization_eq_zero_of_not_dvd (fun h => hG_not_dvd (dvd_trans h hdivG))
          by_cases hdn : n < d
          · have hL0 : (a n).factorization p = 0 := by
              apply Nat.eq_zero_of_le_zero
              unfold a
              apply hlcm_fac_le _ 0 (fun k hk => (Finset.mem_Icc.mp hk).1)
              intro k hk
              have hk1 := (Finset.mem_Icc.mp hk).1
              have hkn := (Finset.mem_Icc.mp hk).2
              have hnd : ¬ (d ∣ k) := fun h => by
                have := Nat.le_of_dvd (by omega) h
                omega
              have hnp : ¬ (p ∣ n ^ k - 1) := fun h => hnd ((hord_iff k hk1).mp h)
              rw [Nat.factorization_eq_zero_of_not_dvd hnp]
            have hP0 : (∏ k ∈ Finset.Icc 1 n, phiNat k).factorization p = 0 := by
              rw [hP_fac]
              apply Finset.sum_eq_zero
              intro k hk
              have hk1 := (Finset.mem_Icc.mp hk).1
              have hkn := (Finset.mem_Icc.mp hk).2
              have hnd : ¬ (d ∣ k) := fun h => by
                have := Nat.le_of_dvd (by omega) h
                omega
              have hnp : ¬ (p ∣ phiNat k) := fun h =>
                hnd ((hord_iff k hk1).mp (dvd_trans h (hphi_dvd k hk1)))
              exact Nat.factorization_eq_zero_of_not_dvd hnp
            rw [hL0, hP0]
          · have hdn' : d ≤ n := by omega
            have hexJ : ∃ j : ℕ, n < d * p ^ (j + 1) := by
              refine ⟨n, ?_⟩
              have h2p : 2 ≤ p := hp.two_le
              have hlt : n < 2 ^ (n + 1) := lt_trans (Nat.lt_two_pow_self) (by
                exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self n))
              have hle : 2 ^ (n + 1) ≤ p ^ (n + 1) := Nat.pow_le_pow_left h2p (n + 1)
              have hd1 : 1 * p ^ (n + 1) ≤ d * p ^ (n + 1) := Nat.mul_le_mul_right _ hd_spec.1
              linarith
            let J := Nat.find hexJ
            have hJ_gt : n < d * p ^ (J + 1) := Nat.find_spec hexJ
            have hJ_le : d * p ^ J ≤ n := by
              rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
              · rw [hJ0, pow_zero, mul_one]
                exact hdn'
              · have hlt : J - 1 < J := by omega
                have hnot := Nat.find_min hexJ hlt
                rw [show J - 1 + 1 = J by omega] at hnot
                omega
            let K := d * p ^ J
            have hK1 : 1 ≤ K := Nat.mul_pos hd_spec.1 (pow_pos hp.pos J)
            have hK0 : n ^ K - 1 ≠ 0 := by
              have := hpow_gt K hK1
              omega
            have hL_eq : (a n).factorization p = (n ^ K - 1).factorization p := by
              apply le_antisymm
              · unfold a
                apply hlcm_fac_le _ ((n ^ K - 1).factorization p)
                  (fun k hk => (Finset.mem_Icc.mp hk).1)
                intro k hk
                have hk1 := (Finset.mem_Icc.mp hk).1
                have hkn := (Finset.mem_Icc.mp hk).2
                by_cases hdk : d ∣ k
                · rcases hdk with ⟨q, rfl⟩
                  have hq0 : q ≠ 0 := by
                    intro hq0
                    rw [hq0, mul_zero] at hk1
                    omega
                  obtain ⟨j, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hq0 p hp.ne_one
                  have hm1 : 1 ≤ m := by
                    rcases Nat.eq_zero_or_pos m with rfl | hm
                    · simp at hk1
                    · exact hm
                  rw [← mul_assoc]
                  rw [(hgeom (d * p ^ j) m (Nat.mul_pos hd_spec.1 (pow_pos hp.pos j))
                    (dvd_mul_right d _) hm1 hpm).1]
                  have hj_le : j ≤ J := by
                    by_contra hj
                    have hj1 : J + 1 ≤ j := by omega
                    have h1 : d * p ^ (J + 1) ≤ d * p ^ j :=
                      Nat.mul_le_mul_left d (Nat.pow_le_pow_right hp.pos hj1)
                    have h2 : d * p ^ j ≤ d * (p ^ j * m) :=
                      Nat.mul_le_mul_left d (Nat.le_mul_of_pos_right _ hm1)
                    omega
                  have hdvdK : d * p ^ j ∣ K :=
                    Nat.mul_dvd_mul_left d (pow_dvd_pow p hj_le)
                  have hndvd := hpow_dvd (d * p ^ j) K (Nat.mul_pos hd_spec.1 (pow_pos hp.pos j))
                    hdvdK
                  exact (Nat.factorization_le_iff_dvd (by
                    have := hpow_gt (d * p ^ j) (Nat.mul_pos hd_spec.1 (pow_pos hp.pos j))
                    omega) hK0).mpr hndvd p
                · have hnp : ¬ (p ∣ n ^ k - 1) := fun h => hdk ((hord_iff k hk1).mp h)
                  rw [Nat.factorization_eq_zero_of_not_dvd hnp]
                  exact Nat.zero_le _
              · have hKmem : K ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hK1, hJ_le⟩
                have hdvdL : n ^ K - 1 ∣ a n := Finset.dvd_lcm hKmem
                exact (Nat.factorization_le_iff_dvd hK0 hL_ne).mpr hdvdL p
            let S : Finset ℕ := (Finset.range (J + 1)).image (fun j => d * p ^ j)
            have hS_sub_Icc : S ⊆ Finset.Icc 1 n := by
              intro r hr
              rcases Finset.mem_image.mp hr with ⟨j, hj, rfl⟩
              have hjle : j ≤ J := by
                have := Finset.mem_range.mp hj
                omega
              refine Finset.mem_Icc.mpr ⟨Nat.mul_pos hd_spec.1 (pow_pos hp.pos j), ?_⟩
              exact le_trans (Nat.mul_le_mul_left d (Nat.pow_le_pow_right hp.pos hjle)) hJ_le
            have hS_sub_div : S ⊆ K.divisors := by
              intro r hr
              rcases Finset.mem_image.mp hr with ⟨j, hj, rfl⟩
              have hjle : j ≤ J := by
                have := Finset.mem_range.mp hj
                omega
              exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left d (pow_dvd_pow p hjle), by omega⟩
            have hP_eq_S : (∏ k ∈ Finset.Icc 1 n, phiNat k).factorization p =
                ∑ k ∈ S, (phiNat k).factorization p := by
              rw [hP_fac]
              symm
              apply Finset.sum_subset hS_sub_Icc
              intro k hk hkS
              have hk1 := (Finset.mem_Icc.mp hk).1
              have hkn := (Finset.mem_Icc.mp hk).2
              by_cases hdk : d ∣ k
              · rcases hdk with ⟨q, rfl⟩
                have hq0 : q ≠ 0 := by
                  intro hq0
                  rw [hq0, mul_zero] at hk1
                  omega
                obtain ⟨j, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hq0 p hp.ne_one
                have hm1 : 1 ≤ m := by
                  rcases Nat.eq_zero_or_pos m with rfl | hm
                  · simp at hk1
                  · exact hm
                have hj_le : j ≤ J := by
                  by_contra hj
                  have hj1 : J + 1 ≤ j := by omega
                  have h1 : d * p ^ (J + 1) ≤ d * p ^ j :=
                    Nat.mul_le_mul_left d (Nat.pow_le_pow_right hp.pos hj1)
                  have h2 : d * p ^ j ≤ d * (p ^ j * m) :=
                    Nat.mul_le_mul_left d (Nat.le_mul_of_pos_right _ hm1)
                  omega
                have hm_gt : 1 < m := by
                  by_contra hle
                  have hm_eq : m = 1 := by omega
                  apply hkS
                  rw [hm_eq, mul_one]
                  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
                rw [← mul_assoc]
                exact (hgeom (d * p ^ j) m (Nat.mul_pos hd_spec.1 (pow_pos hp.pos j))
                  (dvd_mul_right d _) hm1 hpm).2 hm_gt
              · have hnp : ¬ (p ∣ phiNat k) := fun h =>
                  hdk ((hord_iff k hk1).mp (dvd_trans h (hphi_dvd k hk1)))
                exact Nat.factorization_eq_zero_of_not_dvd hnp
            have hK_eq_S : (n ^ K - 1).factorization p =
                ∑ r ∈ S, (phiNat r).factorization p := by
              rw [← hprod_nat K hK1, Nat.factorization_prod (fun r hr =>
                (hphiNat_pos r (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hr).1 (by omega))).ne')]
              simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
              symm
              apply Finset.sum_subset hS_sub_div
              intro r hr hrS
              have hr1 : 1 ≤ r := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hr).1 (by omega)
              by_cases hdr : d ∣ r
              · exfalso
                rcases hdr with ⟨q, rfl⟩
                have hq_dvd : q ∣ p ^ J := by
                  have h1 : d * q ∣ d * p ^ J := (Nat.mem_divisors.mp hr).1
                  exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < d)).mp h1
                obtain ⟨j, hjle, rfl⟩ := (Nat.dvd_prime_pow hp).mp hq_dvd
                exact hrS (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩)
              · have hnp : ¬ (p ∣ phiNat r) := fun h =>
                  hdr ((hord_iff r hr1).mp (dvd_trans h (hphi_dvd r hr1)))
                exact Nat.factorization_eq_zero_of_not_dvd hnp
            rw [hL_eq, hP_eq_S, hK_eq_S]
      · have hnp_fac : ∀ x : ℕ, x.factorization p = 0 := by
          intro x
          by_contra h
          have hm : p ∈ x.factorization.support := Finsupp.mem_support_iff.mpr h
          rw [Nat.support_factorization] at hm
          exact hp (Nat.prime_of_mem_primeFactors hm)
        rw [hnp_fac, hnp_fac]
  refine ⟨hmain1, ?_⟩
  intro n hn
  rw [hmain1 n]
  have htri2 : ∀ k : ℕ, 2 * tri k = k * (k + 1) := by
    intro k
    unfold tri
    have hev : 2 ∣ k * (k + 1) := by
      rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact ⟨m * (m + m + 1), by ring⟩
      · exact ⟨(2 * m + 1) * (m + 1), by ring⟩
    exact Nat.mul_div_cancel' hev
  have htri_ge : 3 ≤ tri n := by
    have h1 := htri2 n
    nlinarith
  have htri_step : tri (n - 1) + n = tri n := by
    have h1 := htri2 n
    have h2 := htri2 (n - 1)
    have h3 : n - 1 + 1 = n := by omega
    rw [h3] at h2
    have h4 : (n - 1) * n + 2 * n = n * (n + 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega
  have hleast : IsLeast {r : ℕ | tri n - 1 ≤ tri r} n := by
    refine ⟨by show tri n - 1 ≤ tri n; omega, ?_⟩
    intro r hr
    show n ≤ r
    by_contra hlt
    have hrle : r ≤ n - 1 := by omega
    have hr1 := htri2 r
    have hn1 := htri2 (n - 1)
    have h3 : n - 1 + 1 = n := by omega
    rw [h3] at hn1
    have hmul : r * (r + 1) ≤ (n - 1) * n := by
      calc r * (r + 1) ≤ (n - 1) * (r + 1) := Nat.mul_le_mul_right _ hrle
        _ ≤ (n - 1) * n := Nat.mul_le_mul_left _ (by omega)
    have htrir : tri r ≤ tri (n - 1) := by omega
    have hhr : tri n - 1 ≤ tri r := hr
    omega
  unfold A156291
  rw [if_pos (by omega : 1 ≤ tri n - 1)]
  dsimp only
  rw [hleast.csInf_eq]
  have hm_eq : tri n - 1 - tri (n - 1) + 1 = n := by omega
  rw [hm_eq]
