import OMAStatements.S_oeis_a052275
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a052275

open OMA.S_oeis_a052275

/-- Number of 6th powers in `(ZMod n)ˣ`. -/
private noncomputable def unitPow6 (n : ℕ) : ℕ :=
  Nat.card (Set.range (fun u : (ZMod n)ˣ => u ^ 6))

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
  set S : Finset ℕ := {1, H - 1, H + 1, M - 1}
  have hScard : S.card = 4 := by
    simp only [S]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton] <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] <;> omega
  have heq : (powMonoidHom (α := (ZMod (2 ^ e))ˣ) 2).ker ≃ {x : ℕ // x ∈ S} := by
    refine Equiv.ofBijective
      (fun u => ⟨((u.1 : (ZMod M)ˣ) : ZMod M).val, ?_⟩) ⟨?_, ?_⟩
    · have hsq : ((u.1 : (ZMod M)ˣ) : ZMod M) ^ 2 = 1 := by
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
      have hpos_sq : 1 ≤ x ^ 2 := Nat.one_le_pow 2 x (by omega)
      have hdvd : M ∣ x ^ 2 - 1 := by
        have h0 : ((x ^ 2 : ℕ) : ZMod M) = (1 : ZMod M) := by simpa [Nat.cast_pow] using hx_zmod
        have hsub0 : ((x ^ 2 - 1 : ℕ) : ZMod M) = 0 := by
          rw [Nat.cast_sub hpos_sq, h0, Nat.cast_one, sub_self]
        exact (ZMod.natCast_eq_zero_iff _ M).mp hsub0
      have hfac : x ^ 2 - 1 = (x - 1) * (x + 1) := by zify [hpos_sq, hx_pos]; ring
      rw [hfac] at hdvd
      have hx_odd : x % 2 = 1 := by
        have h2dvd : 2 ∣ (x - 1) * (x + 1) := dvd_trans ⟨H, hM⟩ hdvd
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2dvd with h1 | h1 <;> omega
      have hdiv_or : H ∣ (x - 1) ∨ H ∣ (x + 1) := by
        by_cases h4 : 4 ∣ (x - 1)
        · left
          have h2dvd_p : 2 ∣ (x + 1) := by omega
          rcases h2dvd_p with ⟨q, hq⟩
          have hq_odd : Odd q := by rw [Nat.odd_iff]; omega
          have hcopq : Nat.Coprime H q := (Nat.coprime_two_left.mpr hq_odd).pow_left (e - 1)
          have hH_dvd : H ∣ (x - 1) * q := by
            rw [hM, hq, show (x - 1) * (2 * q) = 2 * ((x - 1) * q) by ring] at hdvd
            exact (mul_dvd_mul_iff_left (by decide : 2 ≠ 0)).mp hdvd
          exact hcopq.dvd_of_dvd_mul_right hH_dvd
        · right
          have h2dvd_m : 2 ∣ (x - 1) := by omega
          rcases h2dvd_m with ⟨q, hq⟩
          have hq_odd : Odd q := by rw [Nat.odd_iff]; omega
          have hcopq : Nat.Coprime H q := (Nat.coprime_two_left.mpr hq_odd).pow_left (e - 1)
          have hH_dvd : H ∣ q * (x + 1) := by
            rw [hM, hq, show 2 * q * (x + 1) = 2 * (q * (x + 1)) by ring] at hdvd
            exact (mul_dvd_mul_iff_left (by decide : 2 ≠ 0)).mp hdvd
          exact hcopq.dvd_of_dvd_mul_left hH_dvd
      simp only [S, Finset.mem_insert, Finset.mem_singleton]
      rcases hdiv_or with ⟨t, ht⟩ | ⟨t, ht⟩
      · have hxm1 : x - 1 < 2 * H := by omega
        have ht_lt : t < 2 := by nlinarith
        have hcases : t = 0 ∨ t = 1 := by omega
        rcases hcases with rfl | rfl <;> omega
      · have hxp1 : x + 1 ≤ 2 * H := by omega
        have ht_le : t ≤ 2 := by nlinarith
        have hcases : t = 0 ∨ t = 1 ∨ t = 2 := by omega
        rcases hcases with rfl | rfl | rfl <;> omega
    · intro u1 u2 hval
      ext1; apply Units.ext; apply ZMod.val_injective M
      exact congrArg Subtype.val hval
    · rintro ⟨x, hx⟩
      have hxlt : x < M := by
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx; omega
      have hxsq : (x : ZMod M) ^ 2 = 1 := by
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
        have hM_z : (M : ZMod M) = 0 := ZMod.natCast_self M
        have h2H_z : (2 : ZMod M) * (H : ZMod M) = 0 := by
          change ((2 : ℕ) : ZMod M) * (H : ZMod M) = 0
          rw [← Nat.cast_mul, ← hM, hM_z]
        have hH2_z : (H : ZMod M) ^ 2 = 0 := by
          have hdvd : M ∣ H ^ 2 := by
            rw [hM]; refine ⟨2 ^ (e - 2), ?_⟩
            change (2 ^ (e - 1)) ^ 2 = 2 * 2 ^ (e - 1) * 2 ^ (e - 2)
            rw [sq, show 2 * 2 ^ (e - 1) * 2 ^ (e - 2) = 2 ^ (e - 1) * (2 * 2 ^ (e - 2)) by ring]
            congr 1; rw [← pow_succ', show e - 2 + 1 = e - 1 by omega]
          simpa [Nat.cast_pow] using (ZMod.natCast_eq_zero_iff (H ^ 2) M).mpr hdvd
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
        rw [MonoidHom.mem_ker, powMonoidHom_apply]; apply Units.ext; simpa [u] using hxsq
      refine ⟨⟨u, hu_mem⟩, ?_⟩
      ext1; change (x : ZMod M).val = x
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hxlt]
  rw [Nat.card_congr heq, Nat.card_eq_fintype_card, Fintype.card_coe, hScard]

private lemma unitPow6_two_pow_ge3 (e : ℕ) (he : 3 ≤ e) :
    unitPow6 (2 ^ e) = 2 ^ (e - 3) := by
  have : NeZero (2 ^ e) := ⟨pow_ne_zero e (by decide)⟩
  have hcard : Fintype.card (ZMod (2 ^ e))ˣ = 2 ^ (e - 1) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega)]; ring
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
  unfold unitPow6
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

private lemma unitPow6_three_pow_ge2 (e : ℕ) (he : 2 ≤ e) :
    unitPow6 (3 ^ e) = 3 ^ (e - 2) := by
  have : NeZero (3 ^ e) := ⟨pow_ne_zero e (by decide)⟩
  have : IsCyclic (ZMod (3 ^ e))ˣ := ZMod.isCyclic_units_of_prime_pow 3 (by decide) (by decide) e
  unfold unitPow6
  rw [card_range_pow_cyclic 6, ZMod.card_units_eq_totient, Nat.totient_prime_pow (by decide) (by omega), mul_comm]
  have hexp : 3 ^ (e - 1) = 3 * 3 ^ (e - 2) := by
    rw [← pow_succ', show e - 2 + 1 = e - 1 by omega]
  rw [hexp, show (3 - 1) * (3 * 3 ^ (e - 2)) = 6 * 3 ^ (e - 2) by ring]
  rw [Nat.gcd_eq_right (dvd_mul_right 6 _), Nat.mul_div_cancel_left _ (by decide)]

private lemma isUnit_zmod_prime_pow_iff (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) (x : ZMod (p ^ e)) :
    IsUnit x ↔ ¬ p ∣ x.val := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have h1 : IsUnit (x.val : ZMod (p ^ e)) ↔ Nat.Coprime x.val (p ^ e) :=
    ZMod.isUnit_iff_coprime x.val (p ^ e)
  rw [ZMod.natCast_zmod_val] at h1
  rw [h1]
  have hcop_iff : Nat.Coprime x.val (p ^ e) ↔ Nat.Coprime x.val p := by
    constructor
    · intro h; exact h.coprime_dvd_right (dvd_pow_self p (by omega))
    · intro h; exact h.pow_right e
  rw [hcop_iff, hp.coprime_iff_not_dvd.symm]
  exact Nat.coprime_comm

private lemma a052275_base (p e : ℕ) (hp : p.Prime) (he1 : 1 ≤ e) (he6 : e ≤ 6) :
    a052275 (p ^ e) = 1 + unitPow6 (p ^ e) := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have hpe_gt1 : 1 < p ^ e := one_lt_pow₀ hp.one_lt (by omega)
  have : Fact (1 < p ^ e) := ⟨hpe_gt1⟩
  set U : Set (ZMod (p ^ e)) := Set.range (fun u : (ZMod (p ^ e))ˣ => (u : ZMod (p ^ e)) ^ 6)
  have hU_card : Nat.card U = unitPow6 (p ^ e) := by
    unfold unitPow6 U
    have heq : Set.range (fun u : (ZMod (p ^ e))ˣ => u ^ 6) ≃
        Set.range (fun u : (ZMod (p ^ e))ˣ => (u : ZMod (p ^ e)) ^ 6) :=
      Equiv.ofBijective
        (fun ⟨y, hy⟩ => ⟨(y : ZMod (p ^ e)), by rcases hy with ⟨u, rfl⟩; exact ⟨u, by simp⟩⟩)
        ⟨fun a b hab => by ext1; apply Units.ext; exact congrArg Subtype.val hab,
         fun ⟨y, hy⟩ => by rcases hy with ⟨u, rfl⟩; exact ⟨⟨u ^ 6, ⟨u, rfl⟩⟩, by ext; simp⟩⟩
    exact (Nat.card_congr heq).symm
  have h0_not_U : (0 : ZMod (p ^ e)) ∉ U := by
    rintro ⟨u, hu⟩
    have hunit : IsUnit ((0 : ZMod (p ^ e))) := hu ▸ (u ^ 6).isUnit
    have h01 : (0 : ZMod (p ^ e)) = 1 := by
      rcases hunit with ⟨v, hv⟩
      have := v.mul_inv; rw [hv, zero_mul] at this; exact this
    have := congrArg ZMod.val h01
    rw [ZMod.val_zero, ZMod.val_one] at this; omega
  have hrange : Set.range (fun x : ZMod (p ^ e) => x ^ 6) = insert 0 U := by
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, U]
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hpdiv : p ∣ x.val
      · left
        have hp6 : p ^ 6 ∣ x.val ^ 6 := pow_dvd_pow_of_dvd hpdiv 6
        have hpe : p ^ e ∣ x.val ^ 6 := dvd_trans (Nat.pow_dvd_pow p he6) hp6
        have hx : (x.val : ZMod (p ^ e)) = x := ZMod.natCast_zmod_val x
        rw [← hx, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
        exact hpe
      · right
        rcases (isUnit_zmod_prime_pow_iff p e hp he1 x).mpr hpdiv with ⟨u, rfl⟩
        exact ⟨u, rfl⟩
    · rintro (rfl | ⟨u, rfl⟩)
      · exact ⟨0, zero_pow (by decide)⟩
      · exact ⟨(u : ZMod (p ^ e)), rfl⟩
  unfold a052275
  rw [hrange, ← hU_card]
  have hfin : U.Finite := Set.toFinite U
  rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem h0_not_U hfin, Nat.card_coe_set_eq, add_comm]

private lemma a052275_step (p e : ℕ) (hp : p.Prime) :
    a052275 (p ^ (e + 6)) = unitPow6 (p ^ (e + 6)) + a052275 (p ^ e) := by
  have : NeZero (p ^ (e + 6)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set U : Set (ZMod (p ^ (e + 6))) := Set.range (fun u : (ZMod (p ^ (e + 6)))ˣ => (u : ZMod (p ^ (e + 6))) ^ 6)
  set V : Set (ZMod (p ^ (e + 6))) :=
    Set.range (fun y : ZMod (p ^ e) => ((p ^ 6 * y.val ^ 6 : ℕ) : ZMod (p ^ (e + 6))))
  have hU_card : Nat.card U = unitPow6 (p ^ (e + 6)) := by
    unfold unitPow6 U
    have heq : Set.range (fun u : (ZMod (p ^ (e + 6)))ˣ => u ^ 6) ≃
        Set.range (fun u : (ZMod (p ^ (e + 6)))ˣ => (u : ZMod (p ^ (e + 6))) ^ 6) :=
      Equiv.ofBijective
        (fun ⟨y, hy⟩ => ⟨(y : ZMod (p ^ (e + 6))), by rcases hy with ⟨u, rfl⟩; exact ⟨u, by simp⟩⟩)
        ⟨fun a b hab => by ext1; apply Units.ext; exact congrArg Subtype.val hab,
         fun ⟨y, hy⟩ => by rcases hy with ⟨u, rfl⟩; exact ⟨⟨u ^ 6, ⟨u, rfl⟩⟩, by ext; simp⟩⟩
    exact (Nat.card_congr heq).symm
  have hV_card : Nat.card V = a052275 (p ^ e) := by
    unfold a052275
    have hVeq : V = Set.range (fun z : Set.range (fun y : ZMod (p ^ e) => y ^ 6) =>
        ((p ^ 6 * z.1.val : ℕ) : ZMod (p ^ (e + 6)))) := by
      ext w
      simp only [V, Set.mem_range, Subtype.exists]
      constructor
      · rintro ⟨y, rfl⟩
        refine ⟨y ^ 6, ⟨y, rfl⟩, ?_⟩
        have hmod : y.val ^ 6 % p ^ e = (y ^ 6).val := by
          rw [← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]
        rw [ZMod.natCast_eq_natCast_iff']
        rw [show p ^ (e + 6) = p ^ 6 * p ^ e by rw [pow_add, mul_comm],
            Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hmod, Nat.mod_eq_of_lt (ZMod.val_lt _)]
      · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
        refine ⟨y, ?_⟩
        have hmod : y.val ^ 6 % p ^ e = (y ^ 6).val := by
          rw [← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]
        rw [ZMod.natCast_eq_natCast_iff']
        rw [show p ^ (e + 6) = p ^ 6 * p ^ e by rw [pow_add, mul_comm],
            Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hmod, Nat.mod_eq_of_lt (ZMod.val_lt _)]
    have hinj : Function.Injective (fun z : Set.range (fun y : ZMod (p ^ e) => y ^ 6) =>
        ((p ^ 6 * z.1.val : ℕ) : ZMod (p ^ (e + 6)))) := by
      intro z1 z2 hz
      rw [ZMod.natCast_eq_natCast_iff'] at hz
      rw [show p ^ (e + 6) = p ^ 6 * p ^ e by rw [pow_add, mul_comm],
          Nat.mul_mod_mul_left, Nat.mul_mod_mul_left,
          Nat.mod_eq_of_lt (ZMod.val_lt z1.1), Nat.mod_eq_of_lt (ZMod.val_lt z2.1)] at hz
      have hval : z1.1.val = z2.1.val := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 6) hz
      exact Subtype.ext (ZMod.val_injective (p ^ e) hval)
    rw [hVeq, Nat.card_range_of_injective hinj]
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    rintro w ⟨u, rfl⟩ ⟨y, hy⟩
    have hu : IsUnit ((u : ZMod (p ^ (e + 6))) ^ 6) := (u ^ 6).isUnit
    have hnd : ¬ p ∣ ((u : ZMod (p ^ (e + 6))) ^ 6).val :=
      (isUnit_zmod_prime_pow_iff p (e + 6) hp (by omega) _).mp hu
    dsimp only at hy
    rw [← hy] at hnd
    apply hnd
    rw [ZMod.val_natCast]
    exact (Nat.dvd_mod_iff (dvd_pow_self p (by omega))).mpr (dvd_mul_of_dvd_left (dvd_pow_self p (by decide)) _)
  have hrange : Set.range (fun x : ZMod (p ^ (e + 6)) => x ^ 6) = U ∪ V := by
    ext w
    simp only [Set.mem_range, Set.mem_union, U, V]
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hpdiv : p ∣ x.val
      · right
        rcases hpdiv with ⟨q, hq⟩
        refine ⟨(q : ZMod (p ^ e)), ?_⟩
        have hx : (x.val : ZMod (p ^ (e + 6))) = x := ZMod.natCast_zmod_val x
        rw [← hx, hq, ← Nat.cast_pow, show (p * q) ^ 6 = p ^ 6 * q ^ 6 by ring]
        rw [ZMod.natCast_eq_natCast_iff']
        rw [show p ^ (e + 6) = p ^ 6 * p ^ e by rw [pow_add, mul_comm],
            Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
        congr 1
        rw [ZMod.val_natCast, ← Nat.pow_mod]
      · left
        rcases (isUnit_zmod_prime_pow_iff p (e + 6) hp (by omega) x).mpr hpdiv with ⟨u, rfl⟩
        exact ⟨u, rfl⟩
    · rintro (⟨u, rfl⟩ | ⟨y, rfl⟩)
      · exact ⟨(u : ZMod (p ^ (e + 6))), rfl⟩
      · refine ⟨((p * y.val : ℕ) : ZMod (p ^ (e + 6))), ?_⟩
        rw [← Nat.cast_pow, show (p * y.val) ^ 6 = p ^ 6 * y.val ^ 6 by ring]
  change Nat.card (Set.range (fun x : ZMod (p ^ (e + 6)) => x ^ 6)) = unitPow6 (p ^ (e + 6)) + a052275 (p ^ e)
  rw [hrange]
  have hfinU : U.Finite := Set.toFinite U
  have hfinV : V.Finite := Set.toFinite V
  rw [Nat.card_coe_set_eq, Set.ncard_union_eq hdisj hfinU hfinV,
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hU_card, hV_card]

private lemma a052275_one (p : ℕ) : a052275 (p ^ 0) = 1 := by
  have : NeZero (1 : ℕ) := ⟨by decide⟩
  unfold a052275
  rw [pow_zero]
  have hconst : Set.range (fun x : ZMod 1 => x ^ 6) = {0} := by
    ext y; simp [Subsingleton.elim y 0]
  rw [hconst, Nat.card_unique]

private lemma unitPow6_two_small (e : ℕ) (he1 : 1 ≤ e) (he2 : e ≤ 2) : unitPow6 (2 ^ e) = 1 := by
  have : NeZero (2 ^ e) := ⟨pow_ne_zero e (by decide)⟩
  unfold unitPow6
  have hconst : Set.range (fun u : (ZMod (2 ^ e))ˣ => u ^ 6) = {1} := by
    ext y; simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl⟩
      have hcard : Fintype.card (ZMod (2 ^ e))ˣ = 2 ^ (e - 1) := by
        rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega)]; ring
      have hdvd : 2 ^ (e - 1) ∣ 6 := by
        rcases (show e = 1 ∨ e = 2 by omega) with rfl | rfl <;> decide
      rcases hdvd with ⟨q, hq⟩
      rw [hq, pow_mul, ← hcard, pow_card_eq_one, one_pow]
    · rintro rfl; exact ⟨1, one_pow 6⟩
  rw [hconst, Nat.card_unique]

private lemma unitPow6_three_one : unitPow6 (3 ^ 1) = 1 := by
  have : NeZero (3 ^ 1) := ⟨by decide⟩
  have : IsCyclic (ZMod (3 ^ 1))ˣ := ZMod.isCyclic_units_of_prime_pow 3 (by decide) (by decide) 1
  unfold unitPow6
  rw [card_range_pow_cyclic 6, ZMod.card_units_eq_totient, Nat.totient_prime_pow (by decide) (by decide)]
  decide

private lemma coeff_C_mul_X_pow (c : ℤ) (m k : ℕ) :
    PowerSeries.coeff k (PowerSeries.C c * PowerSeries.X ^ m) = if k = m then c else 0 := by
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  split_ifs <;> simp

private lemma coeff_mul_denom (f : ℕ → ℤ) (c : ℤ) (n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.mk f) *
      (1 - PowerSeries.C c * PowerSeries.X - PowerSeries.X ^ 6 + PowerSeries.C c * PowerSeries.X ^ 7)) =
      f n - (if 1 ≤ n then c * f (n - 1) else 0) -
        (if 6 ≤ n then f (n - 6) else 0) + (if 7 ≤ n then c * f (n - 7) else 0) := by
  rw [mul_add, mul_sub, mul_sub, mul_one, map_add, map_sub, map_sub, PowerSeries.coeff_mk]
  have h1 : PowerSeries.coeff n (PowerSeries.mk f * (PowerSeries.C c * PowerSeries.X)) =
      if 1 ≤ n then c * f (n - 1) else 0 := by
    rw [show PowerSeries.mk f * (PowerSeries.C c * PowerSeries.X) =
        PowerSeries.C c * (PowerSeries.mk f * PowerSeries.X ^ 1) by ring,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
    split_ifs <;> simp
  have h6 : PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ 6) =
      if 6 ≤ n then f (n - 6) else 0 := by
    rw [PowerSeries.coeff_mul_X_pow']
    split_ifs <;> simp
  have h7 : PowerSeries.coeff n (PowerSeries.mk f * (PowerSeries.C c * PowerSeries.X ^ 7)) =
      if 7 ≤ n then c * f (n - 7) else 0 := by
    rw [show PowerSeries.mk f * (PowerSeries.C c * PowerSeries.X ^ 7) =
        PowerSeries.C c * (PowerSeries.mk f * PowerSeries.X ^ 7) by ring,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
    split_ifs <;> simp
  rw [h1, h6, h7]

private lemma prove_main :
    (PowerSeries.mk (fun n => (a052275 (2 ^ n) : ℤ))) *
        ((PowerSeries.X - 1) * (2 * PowerSeries.X - 1) * (1 + PowerSeries.X) *
          (1 + PowerSeries.X + PowerSeries.X ^ 2) * (PowerSeries.X ^ 2 - PowerSeries.X + 1)) =
      1 - 2 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4 -
        PowerSeries.X ^ 5 - 2 * PowerSeries.X ^ 6 ∧
    (PowerSeries.mk (fun n => (a052275 (3 ^ n) : ℤ))) *
        ((PowerSeries.X - 1) * (3 * PowerSeries.X - 1) * (1 + PowerSeries.X) *
          (PowerSeries.X ^ 2 - PowerSeries.X + 1) * (1 + PowerSeries.X + PowerSeries.X ^ 2)) =
      1 - PowerSeries.X - 4 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 -
        2 * PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 - 3 * PowerSeries.X ^ 6 := by
  have hd2 : ((PowerSeries.X - 1) * (2 * PowerSeries.X - 1) * (1 + PowerSeries.X) *
        (1 + PowerSeries.X + PowerSeries.X ^ 2) * (PowerSeries.X ^ 2 - PowerSeries.X + 1) : PowerSeries ℤ) =
      1 - PowerSeries.C 2 * PowerSeries.X - PowerSeries.X ^ 6 + PowerSeries.C 2 * PowerSeries.X ^ 7 := by
    simp only [map_ofNat]; ring
  have hd3 : ((PowerSeries.X - 1) * (3 * PowerSeries.X - 1) * (1 + PowerSeries.X) *
        (PowerSeries.X ^ 2 - PowerSeries.X + 1) * (1 + PowerSeries.X + PowerSeries.X ^ 2) : PowerSeries ℤ) =
      1 - PowerSeries.C 3 * PowerSeries.X - PowerSeries.X ^ 6 + PowerSeries.C 3 * PowerSeries.X ^ 7 := by
    simp only [map_ofNat]; ring
  have hr2 : (1 - 2 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4 -
        PowerSeries.X ^ 5 - 2 * PowerSeries.X ^ 6 : PowerSeries ℤ) =
      1 - PowerSeries.C 2 * PowerSeries.X ^ 2 - PowerSeries.C 2 * PowerSeries.X ^ 3 -
        PowerSeries.X ^ 4 - PowerSeries.X ^ 5 - PowerSeries.C 2 * PowerSeries.X ^ 6 := by
    simp only [map_ofNat]
  have hr3 : (1 - PowerSeries.X - 4 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 -
        2 * PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 - 3 * PowerSeries.X ^ 6 : PowerSeries ℤ) =
      1 - PowerSeries.X - PowerSeries.C 4 * PowerSeries.X ^ 2 - PowerSeries.C 2 * PowerSeries.X ^ 3 -
        PowerSeries.C 2 * PowerSeries.X ^ 4 - PowerSeries.C 2 * PowerSeries.X ^ 5 -
        PowerSeries.C 3 * PowerSeries.X ^ 6 := by
    simp only [map_ofNat]
  constructor
  · rw [hd2, hr2]
    ext n
    rw [coeff_mul_denom]
    -- Small values of a052275 (2^n) for n = 0..6
    have ha0 : a052275 1 = 1 := a052275_one 2
    have ha1 : a052275 2 = 2 := by
      have h := a052275_base 2 1 Nat.prime_two (by decide) (by decide)
      rw [unitPow6_two_small 1 (by decide) (by decide)] at h; norm_num at h; exact h
    have ha2 : a052275 4 = 2 := by
      have h := a052275_base 2 2 Nat.prime_two (by decide) (by decide)
      rw [unitPow6_two_small 2 (by decide) (by decide)] at h; norm_num at h; exact h
    have ha3 : a052275 8 = 2 := by
      have h := a052275_base 2 3 Nat.prime_two (by decide) (by decide)
      rw [unitPow6_two_pow_ge3 3 (by decide)] at h; norm_num at h; exact h
    have ha4 : a052275 16 = 3 := by
      have h := a052275_base 2 4 Nat.prime_two (by decide) (by decide)
      rw [unitPow6_two_pow_ge3 4 (by decide)] at h; norm_num at h; exact h
    have ha5 : a052275 32 = 5 := by
      have h := a052275_base 2 5 Nat.prime_two (by decide) (by decide)
      rw [unitPow6_two_pow_ge3 5 (by decide)] at h; norm_num at h; exact h
    have ha6 : a052275 64 = 9 := by
      have h := a052275_base 2 6 Nat.prime_two (by decide) (by decide)
      rw [unitPow6_two_pow_ge3 6 (by decide)] at h; norm_num at h; exact h
    match n with
    | 0 => simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow, coeff_C_mul_X_pow]; norm_num [ha0]
    | 1 => simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow, coeff_C_mul_X_pow]; norm_num [ha0, ha1]
    | 2 => simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow, coeff_C_mul_X_pow]; norm_num [ha1, ha2]
    | 3 => simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow, coeff_C_mul_X_pow]; norm_num [ha2, ha3]
    | 4 => simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow, coeff_C_mul_X_pow]; norm_num [ha3, ha4]
    | 5 => simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow, coeff_C_mul_X_pow]; norm_num [ha4, ha5]
    | 6 => simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow, coeff_C_mul_X_pow]; norm_num [ha0, ha5, ha6]
    | k + 7 =>
      have hstep1 : a052275 (2 ^ (k + 7)) = 2 ^ (k + 4) + a052275 (2 ^ (k + 1)) := by
        have := a052275_step 2 (k + 1) Nat.prime_two
        rw [unitPow6_two_pow_ge3 (k + 1 + 6) (by omega)] at this
        simpa [show k + 1 + 6 = k + 7 by omega, show k + 1 + 6 - 3 = k + 4 by omega] using this
      have hstep0 : a052275 (2 ^ (k + 6)) = 2 ^ (k + 3) + a052275 (2 ^ k) := by
        have := a052275_step 2 k Nat.prime_two
        rw [unitPow6_two_pow_ge3 (k + 6) (by omega)] at this
        simpa [show k + 6 - 3 = k + 3 by omega] using this
      have hRHS : PowerSeries.coeff (k + 7)
          ((1 - PowerSeries.C 2 * PowerSeries.X ^ 2 - PowerSeries.C 2 * PowerSeries.X ^ 3 -
            PowerSeries.X ^ 4 - PowerSeries.X ^ 5 - PowerSeries.C 2 * PowerSeries.X ^ 6 : PowerSeries ℤ)) = 0 := by
        simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow, coeff_C_mul_X_pow,
          show k + 7 ≠ 0 by omega, show k + 7 ≠ 2 by omega, show k + 7 ≠ 3 by omega,
          show k + 7 ≠ 4 by omega, show k + 7 ≠ 5 by omega, show k + 7 ≠ 6 by omega, ↓reduceIte, sub_self]
      rw [hRHS, if_pos (by omega), if_pos (by omega), if_pos (by omega),
          show k + 7 - 1 = k + 6 by omega, show k + 7 - 6 = k + 1 by omega,
          show k + 7 - 7 = k by omega, hstep1, hstep0]
      push_cast
      rw [show (2 : ℤ) ^ (k + 4) = 2 * (2 : ℤ) ^ (k + 3) by rw [← pow_succ']]
      ring
  · rw [hd3, hr3]
    ext n
    rw [coeff_mul_denom]
    have ha0 : a052275 1 = 1 := a052275_one 3
    have ha1 : a052275 3 = 2 := by
      have h := a052275_base 3 1 (by decide) (by decide) (by decide)
      rw [unitPow6_three_one] at h; norm_num at h; exact h
    have ha2 : a052275 9 = 2 := by
      have h := a052275_base 3 2 (by decide) (by decide) (by decide)
      rw [unitPow6_three_pow_ge2 2 (by decide)] at h; norm_num at h; exact h
    have ha3 : a052275 27 = 4 := by
      have h := a052275_base 3 3 (by decide) (by decide) (by decide)
      rw [unitPow6_three_pow_ge2 3 (by decide)] at h; norm_num at h; exact h
    have ha4 : a052275 81 = 10 := by
      have h := a052275_base 3 4 (by decide) (by decide) (by decide)
      rw [unitPow6_three_pow_ge2 4 (by decide)] at h; norm_num at h; exact h
    have ha5 : a052275 243 = 28 := by
      have h := a052275_base 3 5 (by decide) (by decide) (by decide)
      rw [unitPow6_three_pow_ge2 5 (by decide)] at h; norm_num at h; exact h
    have ha6 : a052275 729 = 82 := by
      have h := a052275_base 3 6 (by decide) (by decide) (by decide)
      rw [unitPow6_three_pow_ge2 6 (by decide)] at h; norm_num at h; exact h
    match n with
    | 0 => simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X, coeff_C_mul_X_pow]; norm_num [ha0]
    | 1 => simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X, coeff_C_mul_X_pow]; norm_num [ha0, ha1]
    | 2 => simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X, coeff_C_mul_X_pow]; norm_num [ha1, ha2]
    | 3 => simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X, coeff_C_mul_X_pow]; norm_num [ha2, ha3]
    | 4 => simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X, coeff_C_mul_X_pow]; norm_num [ha3, ha4]
    | 5 => simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X, coeff_C_mul_X_pow]; norm_num [ha4, ha5]
    | 6 => simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X, coeff_C_mul_X_pow]; norm_num [ha0, ha5, ha6]
    | k + 7 =>
      have hstep1 : a052275 (3 ^ (k + 7)) = 3 ^ (k + 5) + a052275 (3 ^ (k + 1)) := by
        have := a052275_step 3 (k + 1) (by decide)
        rw [unitPow6_three_pow_ge2 (k + 1 + 6) (by omega)] at this
        simpa [show k + 1 + 6 = k + 7 by omega, show k + 1 + 6 - 2 = k + 5 by omega] using this
      have hstep0 : a052275 (3 ^ (k + 6)) = 3 ^ (k + 4) + a052275 (3 ^ k) := by
        have := a052275_step 3 k (by decide)
        rw [unitPow6_three_pow_ge2 (k + 6) (by omega)] at this
        simpa [show k + 6 - 2 = k + 4 by omega] using this
      have hRHS : PowerSeries.coeff (k + 7)
          ((1 - PowerSeries.X - PowerSeries.C 4 * PowerSeries.X ^ 2 - PowerSeries.C 2 * PowerSeries.X ^ 3 -
            PowerSeries.C 2 * PowerSeries.X ^ 4 - PowerSeries.C 2 * PowerSeries.X ^ 5 -
            PowerSeries.C 3 * PowerSeries.X ^ 6 : PowerSeries ℤ)) = 0 := by
        simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X, coeff_C_mul_X_pow,
          show k + 7 ≠ 0 by omega, show k + 7 ≠ 1 by omega, show k + 7 ≠ 2 by omega,
          show k + 7 ≠ 3 by omega, show k + 7 ≠ 4 by omega, show k + 7 ≠ 5 by omega,
          show k + 7 ≠ 6 by omega, ↓reduceIte, sub_self]
      rw [hRHS, if_pos (by omega), if_pos (by omega), if_pos (by omega),
          show k + 7 - 1 = k + 6 by omega, show k + 7 - 6 = k + 1 by omega,
          show k + 7 - 7 = k by omega, hstep1, hstep0]
      push_cast
      rw [show (3 : ℤ) ^ (k + 5) = 3 * (3 : ℤ) ^ (k + 4) by rw [← pow_succ']]
      ring

end OMA.P_oeis_a052275

theorem OMA.solution : type_of% @OMA.S_oeis_a052275.main :=
  OMA.P_oeis_a052275.prove_main
