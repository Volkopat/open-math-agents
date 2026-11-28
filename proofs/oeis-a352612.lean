import OMAStatements.S_oeis_a352612
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic

namespace OMA.P_oeis_a352612

open OMA.S_oeis_a352612

/-- In any finite abelian group, the square of the product of all elements is `1`. -/
private lemma prod_univ_sq_eq_one {G : Type*} [CommGroup G] [Fintype G] :
    (∏ x : G, x) ^ 2 = 1 := by
  rw [sq]
  have hinv : ∏ x : G, x = ∏ x : G, x⁻¹ :=
    (Fintype.prod_equiv (Equiv.inv G) _ _ (fun _ => rfl)).symm
  conv_rhs => rw [← Finset.prod_const_one (s := (Finset.univ : Finset G))]
  conv_lhs => arg 2; rw [hinv]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun x _ => mul_inv_cancel x)

/-- Product of all elements in a product of two finite abelian groups of even order is `1`. -/
private lemma prod_univ_prod_eq_one {G H : Type*} [CommGroup G] [CommGroup H] [Fintype G] [Fintype H]
    (hG : Even (Fintype.card G)) (hH : Even (Fintype.card H)) :
    ∏ p : G × H, p = 1 := by
  ext
  · simp only [Prod.fst_prod, Prod.fst_one, Fintype.prod_prod_type]
    simp only [Finset.prod_const, Finset.card_univ]
    rw [Finset.prod_pow]
    obtain ⟨k, hk⟩ := hH
    rw [hk, show k + k = 2 * k by omega, pow_mul, prod_univ_sq_eq_one, one_pow]
  · simp only [Prod.snd_prod, Prod.snd_one, Fintype.prod_prod_type]
    simp only [Finset.prod_const, Finset.card_univ]
    obtain ⟨k, hk⟩ := hG
    rw [hk, show k + k = 2 * k by omega, pow_mul, prod_univ_sq_eq_one, one_pow]

/-- If `1 < n`, `Odd n`, and `¬ IsPrimePow n`, then `∏ u : (ZMod n)ˣ, u = 1`. -/
private lemma prod_units_zmod_eq_one {n : ℕ} [NeZero n] (hn : 1 < n) (hodd : Odd n) (hnpp : ¬ IsPrimePow n) :
    ∏ u : (ZMod n)ˣ, (u : ZMod n) = 1 := by
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  set e := n.factorization p
  have he : 1 ≤ e := (hp.dvd_iff_one_le_factorization (by omega)).mp hpn
  set u := p ^ e
  have hun : u ∣ n := Nat.ordProj_dvd n p
  set v := n / u
  have huv : u * v = n := Nat.mul_div_cancel' hun
  have hu_gt2 : 2 < u := by
    have hp3 : 3 ≤ p := by
      have hp2 := hp.two_le
      have hpne2 : p ≠ 2 := by
        intro hp2eq
        rw [hp2eq] at hpn
        obtain ⟨t, ht⟩ := hodd
        obtain ⟨s, hs⟩ := hpn
        omega
      omega
    have hpe : p ≤ u := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he
    omega
  have hv_ne1 : v ≠ 1 := by
    intro hv1
    rw [hv1, mul_one] at huv
    apply hnpp
    rw [← huv]
    exact hp.isPrimePow.pow (by omega)
  have hv_ne0 : v ≠ 0 := by
    intro hv0; rw [hv0] at huv; simp at huv; omega
  have hv_gt2 : 2 < v := by
    have hv_odd : Odd v := by
      have h2nd : ¬ 2 ∣ n := by obtain ⟨t, ht⟩ := hodd; omega
      have h2nv : ¬ 2 ∣ v := fun h => h2nd (dvd_trans h ⟨u, by linarith⟩)
      exact Nat.odd_iff.mpr (by omega)
    obtain ⟨t, ht⟩ := hv_odd
    omega
  have hp_ndvd_v : ¬ p ∣ v := by
    intro hpv
    have h1 : p ^ (e + 1) ∣ n := by
      rw [← huv, pow_succ]
      obtain ⟨t, ht⟩ := hpv
      exact ⟨t, by rw [ht]; ring⟩
    have h2 := (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)).mp h1
    omega
  have hcop : Nat.Coprime u v := (hp.coprime_iff_not_dvd.mpr hp_ndvd_v).pow_left e
  have : NeZero u := ⟨by omega⟩
  have : NeZero v := ⟨by omega⟩
  let eRing : ZMod n ≃+* ZMod u × ZMod v :=
    (ZMod.ringEquivCongr huv.symm).trans (ZMod.chineseRemainder hcop)
  let eUnits : (ZMod n)ˣ ≃* (ZMod u)ˣ × (ZMod v)ˣ :=
    (Units.mapEquiv eRing.toMulEquiv).trans MulEquiv.prodUnits
  have hprod_u : ∏ x : (ZMod n)ˣ, x = 1 := by
    apply eUnits.injective
    rw [map_prod, map_one]
    have hbij : ∏ x : (ZMod n)ˣ, eUnits x = ∏ y : (ZMod u)ˣ × (ZMod v)ˣ, y :=
      Fintype.prod_equiv eUnits.toEquiv _ _ (fun _ => rfl)
    rw [hbij]
    refine prod_univ_prod_eq_one ?_ ?_
    · rw [ZMod.card_units_eq_totient]; exact Nat.totient_even hu_gt2
    · rw [ZMod.card_units_eq_totient]; exact Nat.totient_even hv_gt2
  have hcoe : (∏ x : (ZMod n)ˣ, (x : ZMod n)) = ((∏ x : (ZMod n)ˣ, x : (ZMod n)ˣ) : ZMod n) :=
    (map_prod (Units.coeHom (ZMod n)) _ _).symm
  rw [hcoe, hprod_u, Units.val_one]

/-- Product over `{1 ≤ k ≤ n - 1 | gcd(k, n) = 1}` equals `∏ u : (ZMod n)ˣ, (u : ZMod n)`. -/
private lemma prod_coprime_Icc_eq_prod_units {n : ℕ} [NeZero n] (hn : 1 < n) :
    ∏ k ∈ (Finset.Icc 1 (n - 1)).filter (fun k => Nat.Coprime k n), (k : ZMod n) =
      ∏ u : (ZMod n)ˣ, (u : ZMod n) := by
  refine Finset.prod_bij (fun k hk => ZMod.unitOfCoprime k (Finset.mem_filter.mp hk).2) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro k1 h1 k2 h2 heq
    have h1' := Finset.mem_filter.mp h1
    have h2' := Finset.mem_filter.mp h2
    have h1b := Finset.mem_Icc.mp h1'.1
    have h2b := Finset.mem_Icc.mp h2'.1
    have hval : (k1 : ZMod n) = (k2 : ZMod n) := by
      have := congr_arg Units.val heq
      simpa [ZMod.coe_unitOfCoprime] using this
    have hmod := (ZMod.natCast_eq_natCast_iff' k1 k2 n).mp hval
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    exact hmod
  · intro u _
    have hval_lt : u.val.val < n := u.val.val_lt
    have hcop : Nat.Coprime u.val.val n := by
      have hunit : IsUnit (u.val.val : ZMod n) := by
        simp [u.isUnit]
      exact (ZMod.isUnit_iff_coprime u.val.val n).mp hunit
    have hpos : 1 ≤ u.val.val := by
      rcases Nat.eq_zero_or_pos u.val.val with h0 | hpos
      · rw [h0, Nat.coprime_zero_left] at hcop; omega
      · exact hpos
    refine ⟨u.val.val, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, by omega⟩, hcop⟩, ?_⟩
    apply Units.ext
    simp [ZMod.coe_unitOfCoprime]
  · intro k hk
    simp [ZMod.coe_unitOfCoprime]

private lemma coprime_sub_iff {n k : ℕ} (hk : k ≤ n) : Nat.Coprime (n - k) n ↔ Nat.Coprime k n := by
  have h1 : ∀ a b : ℕ, a ≤ b → Nat.Coprime a b → Nat.Coprime (b - a) b := by
    intro a b hab hc
    rw [Nat.coprime_iff_gcd_eq_one] at hc ⊢
    refine Nat.dvd_one.mp ?_
    rw [← hc]
    refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
    have hsub := Nat.dvd_sub (Nat.gcd_dvd_right (b - a) b) (Nat.gcd_dvd_left (b - a) b)
    rwa [Nat.sub_sub_self hab] at hsub
  exact ⟨fun h => by simpa [Nat.sub_sub_self hk] using h1 (n - k) n (Nat.sub_le n k) h, h1 k n hk⟩

private lemma prove_a352612 (n : ℕ) (hn : 1 < n) (hodd : Odd n)
    (hcong : a n ≡ -1 [ZMOD (n : ℤ)]) : IsPrimePow n := by
  by_contra hnpp
  have hn_ge9 : 9 ≤ n := by
    by_contra hlt
    push Not at hlt
    interval_cases n
    · obtain ⟨t, ht⟩ := hodd; omega
    · exact hnpp (by norm_num : Nat.Prime 3).isPrimePow
    · obtain ⟨t, ht⟩ := hodd; omega
    · exact hnpp (by norm_num : Nat.Prime 5).isPrimePow
    · obtain ⟨t, ht⟩ := hodd; omega
    · exact hnpp (by norm_num : Nat.Prime 7).isPrimePow
    · obtain ⟨t, ht⟩ := hodd; omega
  have : NeZero n := ⟨by omega⟩
  have ha_mod : (a n : ZMod n) = -1 := by
    have h := (ZMod.intCast_eq_intCast_iff (a n) (-1) n).mpr hcong
    simpa using h
  -- Partition `Icc 1 (n - 1)` coprime to `n`!
  let U := (Finset.Icc 1 (n - 1)).filter (fun k => Nat.Coprime k n)
  let M := (Finset.Icc 2 (n - 2)).filter (fun k => Nat.Coprime k n)
  let P_only := M.filter (fun k => k.Prime ∧ ¬ (n - k).Prime)
  let P_part := M.filter (fun k => ¬ k.Prime ∧ (n - k).Prime)
  let P_both := M.filter (fun k => k.Prime ∧ (n - k).Prime)
  let C_both := M.filter (fun k => ¬ k.Prime ∧ ¬ (n - k).Prime)
  let P_all := (Finset.Icc 2 (n - 2)).filter (fun p => p.Prime ∧ Nat.Coprime p n)
  let C_all := (Finset.Icc 2 (n - 2)).filter (fun k => ¬ k.Prime ∧ ¬ (n - k).Prime ∧ Nat.Coprime k n)
  have hU_eq : U = insert 1 (insert (n - 1) M) := by
    ext k
    simp only [U, M, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hk1, hkn⟩, hcop⟩
      by_cases h1 : k = 1
      · exact Or.inl h1
      · by_cases h2 : k = n - 1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨⟨by omega, by omega⟩, hcop⟩)
    · rintro (rfl | rfl | ⟨⟨hk1, hkn⟩, hcop⟩)
      · exact ⟨⟨by omega, by omega⟩, Nat.coprime_one_left n⟩
      · exact ⟨⟨by omega, by omega⟩, (coprime_sub_iff (by omega : 1 ≤ n)).mpr (Nat.coprime_one_left n)⟩
      · exact ⟨⟨by omega, by omega⟩, hcop⟩
  have hU_prod : ∏ k ∈ U, (k : ZMod n) = (-1 : ZMod n) * ∏ k ∈ M, (k : ZMod n) := by
    rw [hU_eq, Finset.prod_insert, Finset.prod_insert]
    · have hnm1 : ((n - 1 : ℕ) : ZMod n) = -1 := by
        have h1 : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
          rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by norm_num, ← Nat.cast_add, Nat.sub_add_cancel (by omega), ZMod.natCast_self]
        linear_combination h1
      rw [Nat.cast_one, one_mul, hnm1]
    · simp [M]; omega
    · simp [M]; omega
  -- Split `M` into 4 disjoint parts `P_only ∪ P_part ∪ P_both ∪ C_both`!
  have hM_split : ∏ k ∈ M, (k : ZMod n) =
      (∏ k ∈ P_only, (k : ZMod n)) * (∏ k ∈ P_part, (k : ZMod n)) *
      (∏ k ∈ P_both, (k : ZMod n)) * (∏ k ∈ C_both, (k : ZMod n)) := by
    have hdisj1 : Disjoint P_only P_part := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2.1 h1.1)
    have hdisj2 : Disjoint (P_only ∪ P_part) P_both := by
      rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h1.2 h2.2),
             Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h1.1 h2.1)⟩
    have hdisj3 : Disjoint (P_only ∪ P_part ∪ P_both) C_both := by
      rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
      exact ⟨⟨Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2.1 h1.1),
              Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2.2 h1.2)⟩,
             Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2.1 h1.1)⟩
    have hunion : M = P_only ∪ P_part ∪ P_both ∪ C_both := by
      ext k
      simp only [Finset.mem_union, P_only, P_part, P_both, C_both, Finset.mem_filter]
      by_cases h1 : k.Prime <;> by_cases h2 : (n - k).Prime <;> tauto
    rw [hunion, Finset.prod_union hdisj3, Finset.prod_union hdisj2, Finset.prod_union hdisj1]
  -- Pair `P_part` with `P_only` via `k ↦ n - k`!
  have hpart_eq : ∏ k ∈ P_part, (k : ZMod n) = ∏ k ∈ P_only, (-(k : ZMod n)) := by
    refine (Finset.prod_bij (fun k _ => n - k) ?_ ?_ ?_ ?_).symm
    · intro k hk
      simp only [P_only, P_part, M, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      refine ⟨⟨⟨by omega, by omega⟩, (coprime_sub_iff (by omega)).mpr hk.1.2⟩,
        hk.2.2, by have hkp := hk.2.1; rwa [Nat.sub_sub_self (by omega)]⟩
    · intro k1 h1 k2 h2 heq
      simp only [P_only, M, Finset.mem_filter, Finset.mem_Icc] at h1 h2; omega
    · intro k hk
      simp only [P_part, P_only, M, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      refine ⟨n - k, ⟨⟨⟨by omega, by omega⟩, (coprime_sub_iff (by omega)).mpr hk.1.2⟩,
        hk.2.2, by have hkp := hk.2.1; rwa [Nat.sub_sub_self (by omega)]⟩, Nat.sub_sub_self (by omega)⟩
    · intro k hk
      simp only [P_only, M, Finset.mem_filter, Finset.mem_Icc] at hk
      have hsum : ((n - k : ℕ) : ZMod n) + (k : ZMod n) = 0 := by
        rw [← Nat.cast_add, Nat.sub_add_cancel (by omega), ZMod.natCast_self]
      linear_combination -hsum
  have hpair_prod : (∏ k ∈ P_only, (k : ZMod n)) * (∏ k ∈ P_part, (k : ZMod n)) =
      ∏ k ∈ P_only, (-(k : ZMod n) ^ 2) := by
    rw [hpart_eq, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun k _ => by ring)
  -- Express `(a n : ZMod n)` in terms of `P_only`, `P_both`, `C_both`!
  have hP_all_eq : P_all = P_only ∪ P_both := by
    ext k
    simp only [P_all, P_only, P_both, M, Finset.mem_union, Finset.mem_filter]
    by_cases h : (n - k).Prime <;> tauto
  have hP_disj : Disjoint P_only P_both := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h1.2 h2.2)
  have hC_eq : C_all = C_both := by
    ext k; simp only [C_all, C_both, M, Finset.mem_filter]; tauto
  have ha_expr : (a n : ZMod n) =
      (-1 : ZMod n) * (∏ p ∈ P_only, (-(p : ZMod n) ^ 2)) *
      (∏ p ∈ P_both, (-(p : ZMod n) ^ 2)) * (∏ k ∈ C_both, (k : ZMod n)) := by
    dsimp [a]
    push_cast
    change ((n : ZMod n) - 1) * (∏ p ∈ P_all, (-(p : ZMod n) ^ 2)) * (∏ k ∈ C_all, (k : ZMod n)) = _
    rw [ZMod.natCast_self, zero_sub, hP_all_eq, Finset.prod_union hP_disj, hC_eq]
    ring
  -- `∏ k ∈ U, (k : ZMod n) = 1`!
  have hU_one : ∏ k ∈ U, (k : ZMod n) = 1 := by
    rw [prod_coprime_Icc_eq_prod_units hn, prod_units_zmod_eq_one hn hodd hnpp]
  -- Analyze `P_both`: for odd `n`, every element of `P_both` is `2` or `n - 2`!
  by_cases hnm2 : (n - 2).Prime
  · have hPboth_eq : P_both = {2, n - 2} := by
      ext k
      simp only [P_both, M, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨hk2, hkn2⟩, _⟩, hkp, hnkp⟩
        rcases hkp.eq_two_or_odd with rfl | hkodd
        · exact Or.inl rfl
        · rcases hnkp.eq_two_or_odd with h2 | hnkodd
          · exact Or.inr (by omega)
          · obtain ⟨t, ht⟩ := hodd; omega
      · rintro (rfl | rfl)
        · have hcop2 : Nat.Coprime 2 n := Nat.prime_two.coprime_iff_not_dvd.mpr (by
            obtain ⟨t, ht⟩ := hodd; omega)
          exact ⟨⟨⟨by omega, by omega⟩, hcop2⟩, Nat.prime_two, hnm2⟩
        · have hcop2 : Nat.Coprime 2 n := Nat.prime_two.coprime_iff_not_dvd.mpr (by
            obtain ⟨t, ht⟩ := hodd; omega)
          exact ⟨⟨⟨by omega, by omega⟩, (coprime_sub_iff (by omega)).mpr hcop2⟩,
            hnm2, by rw [Nat.sub_sub_self (by omega)]; exact Nat.prime_two⟩
    have h2ne : (2 : ℕ) ≠ n - 2 := by omega
    have hnm2_cast : ((n - 2 : ℕ) : ZMod n) = -2 := by
      have h : ((n - 2 : ℕ) : ZMod n) + 2 = 0 := by
        rw [show (2 : ZMod n) = ((2 : ℕ) : ZMod n) by norm_num, ← Nat.cast_add,
          Nat.sub_add_cancel (by omega), ZMod.natCast_self]
      linear_combination h
    have hpb1 : ∏ p ∈ P_both, (p : ZMod n) = -4 := by
      rw [hPboth_eq, Finset.prod_pair h2ne, hnm2_cast]; norm_num
    have hpb2 : ∏ p ∈ P_both, (-(p : ZMod n) ^ 2) = (-4 : ZMod n) * (-4 : ZMod n) := by
      rw [hPboth_eq, Finset.prod_pair h2ne, hnm2_cast]; norm_num
    have ha_val : (a n : ZMod n) = -4 := by
      rw [ha_expr, hpb2, ← hpair_prod]
      have h1 : (-1 : ZMod n) * ((∏ k ∈ P_only, (k : ZMod n)) * (∏ k ∈ P_part, (k : ZMod n))) *
          (-4 * -4) * ∏ k ∈ C_both, (k : ZMod n) =
          (-4 : ZMod n) * ((-1 : ZMod n) * ((∏ k ∈ P_only, (k : ZMod n)) * (∏ k ∈ P_part, (k : ZMod n)) *
            (-4 : ZMod n) * (∏ k ∈ C_both, (k : ZMod n)))) := by ring
      rw [h1, ← hpb1, ← hM_split, ← hU_prod, hU_one, mul_one]
    rw [ha_val] at ha_mod
    have h30 : ((3 : ℕ) : ZMod n) = 0 := by
      have : (3 : ZMod n) = 0 := by linear_combination -ha_mod
      simpa using this
    have hdvd3 : n ∣ 3 := (ZMod.natCast_eq_zero_iff 3 n).mp h30
    have := Nat.le_of_dvd (by norm_num) hdvd3
    omega
  · have hPboth_eq : P_both = ∅ := by
      ext k
      simp only [P_both, M, Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and]
      rintro ⟨⟨hk2, hkn2⟩, _⟩ hkp hnkp
      rcases hkp.eq_two_or_odd with rfl | hkodd
      · exact hnm2 hnkp
      · rcases hnkp.eq_two_or_odd with h2 | hnkodd
        · have : k = n - 2 := by omega
          subst this; exact hnm2 hkp
        · obtain ⟨t, ht⟩ := hodd; omega
    have ha_val : (a n : ZMod n) = 1 := by
      rw [ha_expr, hPboth_eq, Finset.prod_empty, mul_one, ← hpair_prod]
      have h1 : (-1 : ZMod n) * ((∏ k ∈ P_only, (k : ZMod n)) * (∏ k ∈ P_part, (k : ZMod n))) *
          ∏ k ∈ C_both, (k : ZMod n) =
          (-1 : ZMod n) * ((∏ k ∈ P_only, (k : ZMod n)) * (∏ k ∈ P_part, (k : ZMod n)) *
            (∏ k ∈ (∅ : Finset ℕ), (k : ZMod n)) * (∏ k ∈ C_both, (k : ZMod n))) := by simp
      rw [h1, ← hPboth_eq, ← hM_split, ← hU_prod, hU_one]
    rw [ha_val] at ha_mod
    have h20 : ((2 : ℕ) : ZMod n) = 0 := by
      have : (2 : ZMod n) = 0 := by linear_combination ha_mod
      simpa using this
    have hdvd2 : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp h20
    have := Nat.le_of_dvd (by norm_num) hdvd2
    omega

end OMA.P_oeis_a352612

theorem OMA.solution : type_of% @OMA.S_oeis_a352612.main :=
  OMA.P_oeis_a352612.prove_a352612
