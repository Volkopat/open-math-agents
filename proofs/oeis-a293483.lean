import OMAStatements.S_oeis_a293483
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a293483

open OMA.S_oeis_a293483

private lemma card_range_pow_cyclic {G : Type*} [CommGroup G] [Fintype G] [IsCyclic G] (k : ℕ) :
    Nat.card (Set.range (fun u : G => u ^ k)) = Fintype.card G / Nat.gcd (Fintype.card G) k := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have hrange : Set.range (fun u : G => u ^ k) = (Subgroup.zpowers (g ^ k) : Set G) := by
    ext y
    simp only [Set.mem_range, SetLike.mem_coe, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
      exact ⟨m, by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]⟩
    · rintro ⟨m, rfl⟩
      exact ⟨g ^ m, by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]⟩
  rw [hrange]
  change Nat.card (Subgroup.zpowers (g ^ k)) = _
  rw [Nat.card_zpowers, orderOf_pow, hord]

private lemma pow_surjective_of_coprime {G : Type*} [Group G] [Fintype G] (k : ℕ)
    (hcop : Nat.Coprime (Fintype.card G) k) :
    Function.Surjective (fun u : G => u ^ k) := by
  intro y
  have hbez : (Nat.gcd (Fintype.card G) k : ℤ) =
      (Fintype.card G : ℤ) * Nat.gcdA (Fintype.card G) k + (k : ℤ) * Nat.gcdB (Fintype.card G) k :=
    Nat.gcd_eq_gcd_ab (Fintype.card G) k
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  refine ⟨y ^ Nat.gcdB (Fintype.card G) k, ?_⟩
  dsimp only
  have hpow : (y ^ Nat.gcdB (Fintype.card G) k) ^ k = y ^ ((k : ℤ) * Nat.gcdB (Fintype.card G) k) := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  rw [hpow]
  have hexp : (k : ℤ) * Nat.gcdB (Fintype.card G) k =
      1 - (Fintype.card G : ℤ) * Nat.gcdA (Fintype.card G) k := by linarith
  rw [hexp, zpow_sub, zpow_one, zpow_mul, zpow_natCast, pow_card_eq_one, one_zpow, inv_one, mul_one]

/-- For `e ≥ 3`, the square-root-of-1 solutions in `(ZMod (2^e))ˣ` have cardinality 4. -/
private lemma card_ker_sq_two_pow (e : ℕ) (he : 3 ≤ e) :
    Nat.card (powMonoidHom (α := (ZMod (2 ^ e))ˣ) 2).ker = 4 := by
  have : NeZero (2 ^ e) := ⟨pow_ne_zero e (by decide)⟩
  set M := 2 ^ e
  have hM_gt1 : 1 < M := one_lt_pow₀ (by decide) (by omega)
  have : Fact (1 < M) := ⟨hM_gt1⟩
  set H := 2 ^ (e - 1)
  have hM : M = 2 * H := by
    change 2 ^ e = 2 * 2 ^ (e - 1)
    rw [← pow_succ', show e - 1 + 1 = e by omega]
  have hH_ge4 : 4 ≤ H := by
    change 4 ≤ 2 ^ (e - 1)
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ (e - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  -- The 4 residues in Finset ℕ: {1, H - 1, H + 1, M - 1}
  set S : Finset ℕ := {1, H - 1, H + 1, M - 1}
  have hScard : S.card = 4 := by
    simp only [S]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton] <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] <;> omega
  -- Bijection between ker(sq) and S via u ↦ (u : ZMod M).val
  have heq : (powMonoidHom (α := (ZMod (2 ^ e))ˣ) 2).ker ≃ {x : ℕ // x ∈ S} := by
    refine Equiv.ofBijective
      (fun u => ⟨((u.1 : (ZMod M)ˣ) : ZMod M).val, ?_⟩) ⟨?_, ?_⟩
    · -- val ∈ S
      have hsq : ((u.1 : (ZMod M)ˣ) : ZMod M) ^ 2 = 1 := by
        have hmem := u.2
        rw [MonoidHom.mem_ker, powMonoidHom_apply] at hmem
        simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hmem
      set x := ((u.1 : (ZMod M)ˣ) : ZMod M).val
      have hxlt : x < M := ZMod.val_lt _
      have hx_zmod : (x : ZMod M) ^ 2 = 1 := by simpa [x] using hsq
      have hx_pos : 1 ≤ x := by
        by_contra h0
        have hx0 : x = 0 := by omega
        rw [hx0] at hx_zmod; simp at hx_zmod
      have hpos_sq : 1 ≤ x ^ 2 := by nlinarith
      have hdvd : M ∣ x ^ 2 - 1 := by
        have h0 : ((x ^ 2 : ℕ) : ZMod M) = (1 : ZMod M) := by simpa [Nat.cast_pow] using hx_zmod
        have hsub0 : ((x ^ 2 - 1 : ℕ) : ZMod M) = 0 := by
          rw [Nat.cast_sub hpos_sq, h0, Nat.cast_one, sub_self]
        exact (ZMod.natCast_eq_zero_iff _ M).mp hsub0
      have hfac : x ^ 2 - 1 = (x - 1) * (x + 1) := by zify [hpos_sq, hx_pos]; ring
      rw [hfac] at hdvd
      have hx_odd : x % 2 = 1 := by
        have h2dvd : 2 ∣ (x - 1) * (x + 1) := dvd_trans ⟨H, hM⟩ hdvd
        rcases Nat.Prime.dvd_mul Nat.prime_two |>.mp h2dvd with h1 | h1 <;> omega
      -- Since gcd(x-1, x+1) = 2, one of them is not divisible by 4, hence the other is divisible by H = 2^(e-1)
      have hdiv_or : H ∣ (x - 1) ∨ H ∣ (x + 1) := by
        by_cases h4 : 4 ∣ (x - 1)
        · left
          have h2not : ¬ 4 ∣ (x + 1) := by omega
          have h2dvd_p : 2 ∣ (x + 1) := by omega
          rcases h2dvd_p with ⟨q, hq⟩
          have hq_odd : Odd q := by
            rw [Nat.odd_iff]; omega
          have hcopq : Nat.Coprime H q :=
            (Nat.coprime_two_left.mpr hq_odd).pow_left (e - 1)
          have hH_dvd : H ∣ (x - 1) * q := by
            rw [hM, hq, show (x - 1) * (2 * q) = 2 * ((x - 1) * q) by ring] at hdvd
            exact (mul_dvd_mul_iff_left (by decide : 2 ≠ 0)).mp hdvd
          exact hcopq.dvd_of_dvd_mul_right hH_dvd
        · right
          have h2dvd_m : 2 ∣ (x - 1) := by omega
          rcases h2dvd_m with ⟨q, hq⟩
          have hq_odd : Odd q := by
            rw [Nat.odd_iff]; omega
          have hcopq : Nat.Coprime H q :=
            (Nat.coprime_two_left.mpr hq_odd).pow_left (e - 1)
          have hH_dvd : H ∣ q * (x + 1) := by
            rw [hM, hq, show 2 * q * (x + 1) = 2 * (q * (x + 1)) by ring] at hdvd
            exact (mul_dvd_mul_iff_left (by decide : 2 ≠ 0)).mp hdvd
          exact hcopq.dvd_of_dvd_mul_left hH_dvd
      simp only [S, Finset.mem_insert, Finset.mem_singleton]
      rcases hdiv_or with ⟨t, ht⟩ | ⟨t, ht⟩
      · have hxm1 : x - 1 < 2 * H := by omega
        have ht_lt : t < 2 := by nlinarith
        have hcases : t = 0 ∨ t = 1 := by omega
        rcases hcases with rfl | rfl
        · left; omega
        · right; right; left; omega
      · have hxp1 : x + 1 ≤ 2 * H := by omega
        have ht_le : t ≤ 2 := by nlinarith
        have hcases : t = 0 ∨ t = 1 ∨ t = 2 := by omega
        rcases hcases with rfl | rfl | rfl
        · omega
        · right; left; omega
        · right; right; right; omega
    · -- injective
      intro u1 u2 hval
      ext1
      apply Units.ext
      apply ZMod.val_injective M
      exact congrArg Subtype.val hval
    · -- surjective
      rintro ⟨x, hx⟩
      have hxlt : x < M := by
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
        omega
      have hxsq : (x : ZMod M) ^ 2 = 1 := by
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
        have hM_z : (M : ZMod M) = 0 := ZMod.natCast_self M
        have h2H_z : (2 : ZMod M) * (H : ZMod M) = 0 := by
          change ((2 : ℕ) : ZMod M) * (H : ZMod M) = 0
          rw [← Nat.cast_mul, ← hM, hM_z]
        have hH2_z : (H : ZMod M) ^ 2 = 0 := by
          have hdvd : M ∣ H ^ 2 := by
            rw [hM]
            refine ⟨2 ^ (e - 2), ?_⟩
            change (2 ^ (e - 1)) ^ 2 = 2 * 2 ^ (e - 1) * 2 ^ (e - 2)
            rw [sq, show 2 * 2 ^ (e - 1) * 2 ^ (e - 2) = 2 ^ (e - 1) * (2 * 2 ^ (e - 2)) by ring]
            congr 1
            rw [← pow_succ', show e - 2 + 1 = e - 1 by omega]
          have h0 : ((H ^ 2 : ℕ) : ZMod M) = 0 := (ZMod.natCast_eq_zero_iff (H ^ 2) M).mpr hdvd
          simpa [Nat.cast_pow] using h0
        rcases hx with rfl | rfl | rfl | rfl
        · simp
        · rw [Nat.cast_sub (by omega : 1 ≤ H), Nat.cast_one]
          calc ((H : ZMod M) - 1) ^ 2 = (H : ZMod M) ^ 2 - (2 * (H : ZMod M)) + 1 := by ring
            _ = 1 := by rw [hH2_z, h2H_z]; ring
        · rw [Nat.cast_add, Nat.cast_one]
          calc ((H : ZMod M) + 1) ^ 2 = (H : ZMod M) ^ 2 + (2 * (H : ZMod M)) + 1 := by ring
            _ = 1 := by rw [hH2_z, h2H_z]; ring
        · rw [Nat.cast_sub (by omega : 1 ≤ M), hM_z, Nat.cast_one]; ring
      let u : (ZMod M)ˣ := ⟨(x : ZMod M), (x : ZMod M), by simpa [sq] using hxsq, by simpa [sq] using hxsq⟩
      have hu_mem : u ∈ (powMonoidHom (α := (ZMod M)ˣ) 2).ker := by
        rw [MonoidHom.mem_ker, powMonoidHom_apply]
        apply Units.ext
        simpa [u] using hxsq
      refine ⟨⟨u, hu_mem⟩, ?_⟩
      ext1
      change (x : ZMod M).val = x
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hxlt]
  rw [Nat.card_congr heq, Nat.card_eq_fintype_card, Fintype.card_coe, hScard]

private lemma a293483_two_pow_ge3 (e : ℕ) (he : 3 ≤ e) :
    a293483 (2 ^ e) = 2 ^ (e - 3) := by
  have : NeZero (2 ^ e) := ⟨pow_ne_zero e (by decide)⟩
  have hcard : Fintype.card (ZMod (2 ^ e))ˣ = 2 ^ (e - 1) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega)]
    ring
  have hcop3 : Nat.Coprime (Fintype.card (ZMod (2 ^ e))ˣ) 3 := by
    rw [hcard]; exact (by decide : Nat.Coprime 2 3).pow_left (e - 1)
  have hsurj3 := pow_surjective_of_coprime 3 hcop3
  have hrange : Set.range (fun u : (ZMod (2 ^ e))ˣ => u ^ 6) =
      ((powMonoidHom (α := (ZMod (2 ^ e))ˣ) 2).range : Set (ZMod (2 ^ e))ˣ) := by
    ext y
    simp only [Set.mem_range, SetLike.mem_coe, MonoidHom.mem_range, powMonoidHom_apply]
    constructor
    · rintro ⟨u, rfl⟩; exact ⟨u ^ 3, by rw [← pow_mul]⟩
    · rintro ⟨v, rfl⟩
      rcases hsurj3 v with ⟨u, rfl⟩
      exact ⟨u, by rw [← pow_mul]⟩
  unfold a293483
  rw [hrange]
  change Nat.card (powMonoidHom (α := (ZMod (2 ^ e))ˣ) 2).range = 2 ^ (e - 3)
  have hfirst := QuotientGroup.quotientKerEquivRange (powMonoidHom (α := (ZMod (2 ^ e))ˣ) 2)
  have hmul : Nat.card (powMonoidHom (α := (ZMod (2 ^ e))ˣ) 2).ker *
      Nat.card (powMonoidHom (α := (ZMod (2 ^ e))ˣ) 2).range = Fintype.card (ZMod (2 ^ e))ˣ := by
    rw [← Nat.card_congr hfirst.toEquiv]
    have hl := Subgroup.card_mul_index (powMonoidHom (α := (ZMod (2 ^ e))ˣ) 2).ker
    rw [← Subgroup.index_eq_card] at *
    simpa [Nat.card_eq_fintype_card] using hl
  rw [card_ker_sq_two_pow e he, hcard] at hmul
  have hexp : 2 ^ (e - 1) = 4 * 2 ^ (e - 3) := by
    calc 2 ^ (e - 1) = 2 ^ (2 + (e - 3)) := by congr 1; omega
      _ = 4 * 2 ^ (e - 3) := by rw [pow_add]; norm_num
  omega

private lemma a293483_odd_prime_pow (p e : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) :
    a293483 (p ^ e) = ((p - 1) * p ^ (e - 1)) / Nat.gcd ((p - 1) * p ^ (e - 1)) 6 := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have : IsCyclic (ZMod (p ^ e))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  unfold a293483
  rw [card_range_pow_cyclic 6, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp (by omega)]
  rw [mul_comm]

private lemma a293483_one : a293483 1 = 1 := by
  have : NeZero (1 : ℕ) := ⟨by decide⟩
  have hsurj : Function.Surjective (fun u : (ZMod 1)ˣ => u ^ 6) :=
    pow_surjective_of_coprime 6 (by rw [ZMod.card_units_eq_totient]; decide)
  unfold a293483
  rw [hsurj.range_eq, Nat.card_univ, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]; decide

private lemma a293483_two_pow_le3 (e : ℕ) (he : e ≤ 3) : a293483 (2 ^ e) = 1 := by
  have hcases : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · simpa using a293483_one
  · have : NeZero (2 : ℕ) := ⟨by decide⟩
    have hsurj : Function.Surjective (fun u : (ZMod 2)ˣ => u ^ 6) :=
      pow_surjective_of_coprime 6 (by rw [ZMod.card_units_eq_totient]; decide)
    unfold a293483
    rw [pow_one, hsurj.range_eq, Nat.card_univ, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]; decide
  · have : NeZero (4 : ℕ) := ⟨by decide⟩
    have hconst : Set.range (fun u : (ZMod 4)ˣ => u ^ 6) = {1} := by
      ext y; simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨u, rfl⟩
        have hu2 : u ^ 2 = 1 := by
          have := pow_card_eq_one (x := u)
          rwa [ZMod.card_units_eq_totient, (by decide : Nat.totient 4 = 2)] at this
        rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, hu2, one_pow]
      · rintro rfl; exact ⟨1, one_pow 6⟩
    unfold a293483
    rw [show (2 ^ 2 : ℕ) = 4 by decide, hconst, Nat.card_unique]
  · simpa using a293483_two_pow_ge3 3 le_rfl

private lemma prove_main :
    (∀ e : ℕ, e ≤ 3 → a293483 (2 ^ e) = 1) ∧
    (∀ e : ℕ, 3 ≤ e → a293483 (2 ^ e) = 2 ^ (e - 3)) ∧
    (∀ e : ℕ, e ≤ 2 → a293483 (3 ^ e) = 1) ∧
    (∀ e : ℕ, 2 ≤ e → a293483 (3 ^ e) = 3 ^ (e - 2)) ∧
    (∀ p e : ℕ, p.Prime → 1 ≤ e → p % 6 = 5 →
      a293483 (p ^ e) = (p - 1) * p ^ (e - 1) / 2) ∧
    (∀ p e : ℕ, p.Prime → 1 ≤ e → p % 6 = 1 →
      a293483 (p ^ e) = (p - 1) * p ^ (e - 1) / 6) := by
  refine ⟨a293483_two_pow_le3, a293483_two_pow_ge3, ?_, ?_, ?_, ?_⟩
  · intro e he
    have hcases : e = 0 ∨ e = 1 ∨ e = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simpa using a293483_one
    · have h3 := a293483_odd_prime_pow 3 1 (by decide) (by decide) le_rfl
      simpa using h3
    · have h9 := a293483_odd_prime_pow 3 2 (by decide) (by decide) (by decide)
      simpa using h9
  · intro e he
    rw [a293483_odd_prime_pow 3 e (by decide) (by decide) (by omega)]
    have hexp : 3 ^ (e - 1) = 3 * 3 ^ (e - 2) := by
      rw [← pow_succ', show e - 2 + 1 = e - 1 by omega]
    have hgcd : Nat.gcd ((3 - 1) * 3 ^ (e - 1)) 6 = 6 := by
      rw [hexp, show (3 - 1) * (3 * 3 ^ (e - 2)) = 6 * 3 ^ (e - 2) by ring]
      exact Nat.gcd_eq_right (dvd_mul_right 6 _)
    rw [hgcd, hexp, show (3 - 1) * (3 * 3 ^ (e - 2)) = 6 * 3 ^ (e - 2) by ring,
        Nat.mul_div_cancel_left _ (by decide)]
  · intro p e hp he hmod
    have hp2 : p ≠ 2 := by omega
    rw [a293483_odd_prime_pow p e hp hp2 he]
    have h3 : Nat.Prime 3 := by decide
    have hnd3a : ¬ (3 ∣ p - 1) := by omega
    have hnd3b : ¬ (3 ∣ p) := by omega
    have hcop3 : Nat.Coprime ((p - 1) * p ^ (e - 1)) 3 :=
      ((h3.coprime_iff_not_dvd.mpr hnd3a).symm).mul_left
        (((h3.coprime_iff_not_dvd.mpr hnd3b).symm).pow_left (e - 1))
    have h2dvd : 2 ∣ (p - 1) * p ^ (e - 1) := dvd_mul_of_dvd_left (by omega) _
    have hgcd : Nat.gcd ((p - 1) * p ^ (e - 1)) 6 = 2 := by
      apply Nat.dvd_antisymm
      · have hd1 : Nat.gcd ((p - 1) * p ^ (e - 1)) 6 ∣ 6 := Nat.gcd_dvd_right _ _
        have hcop_g3 : Nat.Coprime (Nat.gcd ((p - 1) * p ^ (e - 1)) 6) 3 :=
          hcop3.coprime_dvd_left (Nat.gcd_dvd_left _ _)
        exact hcop_g3.dvd_of_dvd_mul_right (by simpa [show (6 : ℕ) = 2 * 3 by decide] using hd1)
      · exact Nat.dvd_gcd h2dvd (by decide)
    rw [hgcd]
  · intro p e hp he hmod
    have hp2 : p ≠ 2 := by omega
    rw [a293483_odd_prime_pow p e hp hp2 he]
    have hdvd : 6 ∣ (p - 1) * p ^ (e - 1) := dvd_mul_of_dvd_left (by omega) _
    rw [Nat.gcd_eq_right hdvd]

end OMA.P_oeis_a293483

theorem OMA.solution : type_of% @OMA.S_oeis_a293483.main :=
  OMA.P_oeis_a293483.prove_main
