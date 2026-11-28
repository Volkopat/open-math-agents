import OMAStatements.S_oeis_a052273
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a052273

open OMA.S_oeis_a052273

/-- Number of 4th powers in `(ZMod n)ˣ`. -/
private noncomputable def unitPow4 (n : ℕ) : ℕ :=
  Nat.card (Set.range (fun u : (ZMod n)ˣ => u ^ 4))

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

private lemma unitPow4_odd_prime_pow (p e : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) :
    unitPow4 (p ^ e) = ((p - 1) * p ^ (e - 1)) / Nat.gcd (p - 1) 4 := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have : IsCyclic (ZMod (p ^ e))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  unfold unitPow4
  rw [card_range_pow_cyclic 4, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp (by omega), mul_comm]
  have hcop_p2 : Nat.Coprime p 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr (fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd).symm)).symm
  have hcop_p4 : Nat.Coprime (p ^ (e - 1)) 4 := (hcop_p2.pow_right 2).pow_left (e - 1)
  have hgcd : Nat.gcd ((p - 1) * p ^ (e - 1)) 4 = Nat.gcd (p - 1) 4 := by
    rw [mul_comm, Nat.gcd_comm, hcop_p4.gcd_mul_left_cancel_right, Nat.gcd_comm]
  rw [hgcd]

/-- Helper: elements of `S` for `2^m` (`m ≥ 4`). -/
private def kerPow4Set (m : ℕ) : Finset ℕ :=
  let Q := 2 ^ (m - 2)
  {1, Q - 1, Q + 1, 2 * Q - 1, 2 * Q + 1, 3 * Q - 1, 3 * Q + 1, 4 * Q - 1}

private lemma kerPow4Set_card (m : ℕ) (hm : 4 ≤ m) : (kerPow4Set m).card = 8 := by
  unfold kerPow4Set
  dsimp only
  set Q := 2 ^ (m - 2)
  have hQ_ge4 : 4 ≤ Q := by
    change 4 ≤ 2 ^ (m - 2)
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  repeat (rw [Finset.card_insert_of_notMem]; swap; simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
  rw [Finset.card_singleton]

private lemma mem_kerPow4Set_of_pow4_eq_one (m : ℕ) (hm : 4 ≤ m) (x : ℕ)
    (hxlt : x < 2 ^ m) (hx_zmod : (x : ZMod (2 ^ m)) ^ 4 = 1) : x ∈ kerPow4Set m := by
  set M := 2 ^ m
  have : NeZero M := ⟨pow_ne_zero m (by decide)⟩
  have hM_gt1 : 1 < M := one_lt_pow₀ (by decide) (by omega)
  have : Fact (1 < M) := ⟨hM_gt1⟩
  set Q := 2 ^ (m - 2)
  have hM4Q : M = 4 * Q := by
    change 2 ^ m = 4 * 2 ^ (m - 2)
    calc 2 ^ m = 2 ^ (2 + (m - 2)) := by congr 1; omega
      _ = 4 * 2 ^ (m - 2) := by rw [pow_add]; norm_num
  have hQ_ge4 : 4 ≤ Q := by
    change 4 ≤ 2 ^ (m - 2)
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hx_pos : 1 ≤ x := by
    by_contra h0
    have hx0 : x = 0 := by omega
    rw [hx0] at hx_zmod; simp at hx_zmod
  have hpos4 : 1 ≤ x ^ 4 := Nat.one_le_pow 4 x (by omega)
  have hpos2 : 1 ≤ x ^ 2 := Nat.one_le_pow 2 x (by omega)
  have hdvd : M ∣ x ^ 4 - 1 := by
    have h0 : ((x ^ 4 : ℕ) : ZMod M) = (1 : ZMod M) := by simpa [Nat.cast_pow] using hx_zmod
    have hsub0 : ((x ^ 4 - 1 : ℕ) : ZMod M) = 0 := by
      rw [Nat.cast_sub hpos4, h0, Nat.cast_one, sub_self]
    exact (ZMod.natCast_eq_zero_iff _ M).mp hsub0
  have hfac4 : x ^ 4 - 1 = (x ^ 2 - 1) * (x ^ 2 + 1) := by zify [hpos4, hpos2]; ring
  rw [hfac4] at hdvd
  have hx_odd : x % 2 = 1 := by
    have h2dvd : 2 ∣ (x ^ 2 - 1) * (x ^ 2 + 1) := dvd_trans ⟨2 * Q, by linarith⟩ hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2dvd with h1 | h1 <;>
    · by_contra hev
      have h2x : 2 ∣ x := by omega
      have h2x2 : 2 ∣ x ^ 2 := dvd_trans h2x (dvd_pow_self x (by decide))
      omega
  have hx2_mod4 : (x ^ 2 + 1) % 4 = 2 := by
    rcases (show x % 4 = 1 ∨ x % 4 = 3 by omega) with h1 | h3
    · have : x ^ 2 % 4 = 1 := by rw [Nat.pow_mod, h1]
      omega
    · have : x ^ 2 % 4 = 1 := by rw [Nat.pow_mod, h3]
      omega
  have h2Q_dvd : 2 * Q ∣ (x - 1) * (x + 1) := by
    have h2w : 2 ∣ x ^ 2 + 1 := by omega
    rcases h2w with ⟨w, hw⟩
    have hw_odd : Odd w := by rw [Nat.odd_iff]; omega
    have hcop_w : Nat.Coprime (2 * Q) w := by
      have : 2 * Q = 2 ^ (m - 1) := by
        change 2 * 2 ^ (m - 2) = 2 ^ (m - 1)
        rw [← pow_succ', show m - 2 + 1 = m - 1 by omega]
      rw [this]
      exact (Nat.coprime_two_left.mpr hw_odd).pow_left (m - 1)
    have h2Qdvd : 2 * Q ∣ (x ^ 2 - 1) * w := by
      rw [hM4Q, hw, show (x ^ 2 - 1) * (2 * w) = 2 * ((x ^ 2 - 1) * w) by ring,
          show 4 * Q = 2 * (2 * Q) by ring] at hdvd
      exact (mul_dvd_mul_iff_left (by decide : 2 ≠ 0)).mp hdvd
    have hres := hcop_w.dvd_of_dvd_mul_right h2Qdvd
    have hfac2 : x ^ 2 - 1 = (x - 1) * (x + 1) := by zify [hpos2, hx_pos]; ring
    rwa [hfac2] at hres
  have hdiv_or : Q ∣ (x - 1) ∨ Q ∣ (x + 1) := by
    by_cases h4m : 4 ∣ (x - 1)
    · left
      have h2p : 2 ∣ (x + 1) := by omega
      rcases h2p with ⟨q, hq⟩
      have hq_odd : Odd q := by rw [Nat.odd_iff]; omega
      have hcopq : Nat.Coprime Q q := (Nat.coprime_two_left.mpr hq_odd).pow_left (m - 2)
      have hQ_dvd : Q ∣ (x - 1) * q := by
        rw [hq, show (x - 1) * (2 * q) = 2 * ((x - 1) * q) by ring] at h2Q_dvd
        exact (mul_dvd_mul_iff_left (by decide : 2 ≠ 0)).mp h2Q_dvd
      exact hcopq.dvd_of_dvd_mul_right hQ_dvd
    · right
      have h2m : 2 ∣ (x - 1) := by omega
      rcases h2m with ⟨q, hq⟩
      have hq_odd : Odd q := by rw [Nat.odd_iff]; omega
      have hcopq : Nat.Coprime Q q := (Nat.coprime_two_left.mpr hq_odd).pow_left (m - 2)
      have hQ_dvd : Q ∣ q * (x + 1) := by
        rw [hq, show 2 * q * (x + 1) = 2 * (q * (x + 1)) by ring] at h2Q_dvd
        exact (mul_dvd_mul_iff_left (by decide : 2 ≠ 0)).mp h2Q_dvd
      exact hcopq.dvd_of_dvd_mul_left hQ_dvd
  unfold kerPow4Set
  dsimp only
  simp only [Finset.mem_insert, Finset.mem_singleton]
  change x = 1 ∨ x = Q - 1 ∨ x = Q + 1 ∨ x = 2 * Q - 1 ∨ x = 2 * Q + 1 ∨ x = 3 * Q - 1 ∨ x = 3 * Q + 1 ∨ x = 4 * Q - 1
  rcases hdiv_or with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hxm : x - 1 < 4 * Q := by omega
    have ht_lt : t < 4 := by nlinarith
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl <;> omega
  · have hxp : x + 1 ≤ 4 * Q := by omega
    have ht_le : t ≤ 4 := by nlinarith
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> omega

private lemma pow4_eq_one_of_mem_kerPow4Set (m : ℕ) (hm : 4 ≤ m) (x : ℕ)
    (hx : x ∈ kerPow4Set m) : x < 2 ^ m ∧ (x : ZMod (2 ^ m)) ^ 4 = 1 := by
  set M := 2 ^ m
  set Q := 2 ^ (m - 2)
  have hM4Q : M = 4 * Q := by
    change 2 ^ m = 4 * 2 ^ (m - 2)
    calc 2 ^ m = 2 ^ (2 + (m - 2)) := by congr 1; omega
      _ = 4 * 2 ^ (m - 2) := by rw [pow_add]; norm_num
  have hQ_ge4 : 4 ≤ Q := by
    change 4 ≤ 2 ^ (m - 2)
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  unfold kerPow4Set at hx
  dsimp only at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  change x = 1 ∨ x = Q - 1 ∨ x = Q + 1 ∨ x = 2 * Q - 1 ∨ x = 2 * Q + 1 ∨ x = 3 * Q - 1 ∨ x = 3 * Q + 1 ∨ x = 4 * Q - 1 at hx
  refine ⟨by omega, ?_⟩
  have hM_z : (M : ZMod M) = 0 := ZMod.natCast_self M
  have h4Q_z : (4 : ZMod M) * (Q : ZMod M) = 0 := by
    change ((4 : ℕ) : ZMod M) * (Q : ZMod M) = 0
    rw [← Nat.cast_mul, ← hM4Q, hM_z]
  have hQ2_z : (Q : ZMod M) ^ 2 = 0 := by
    have hdvd : M ∣ Q ^ 2 := by
      rw [hM4Q]; refine ⟨2 ^ (m - 4), ?_⟩
      change (2 ^ (m - 2)) ^ 2 = 4 * 2 ^ (m - 2) * 2 ^ (m - 4)
      rw [sq, show 4 * 2 ^ (m - 2) * 2 ^ (m - 4) = 2 ^ (m - 2) * (4 * 2 ^ (m - 4)) by ring]
      congr 1
      calc 2 ^ (m - 2) = 2 ^ (2 + (m - 4)) := by congr 1; omega
        _ = 4 * 2 ^ (m - 4) := by rw [pow_add]; norm_num
    simpa [Nat.cast_pow] using (ZMod.natCast_eq_zero_iff (Q ^ 2) M).mpr hdvd
  have hgen : ∀ c : ZMod M, (c * (Q : ZMod M) + 1) ^ 4 = 1 ∧ (c * (Q : ZMod M) - 1) ^ 4 = 1 := fun c => by
    set a := c * (Q : ZMod M)
    have ha2 : a ^ 2 = 0 := by calc a ^ 2 = c ^ 2 * (Q : ZMod M) ^ 2 := by ring
      _ = 0 := by rw [hQ2_z, mul_zero]
    have h4a : 4 * a = 0 := by calc 4 * a = c * (4 * (Q : ZMod M)) := by ring
      _ = 0 := by rw [h4Q_z, mul_zero]
    exact ⟨by calc (a + 1) ^ 4 = (a ^ 2) ^ 2 + 4 * a * a ^ 2 + 6 * a ^ 2 + 4 * a + 1 := by ring
              _ = 1 := by rw [ha2, h4a]; ring,
           by calc (a - 1) ^ 4 = (a ^ 2) ^ 2 - 4 * a * a ^ 2 + 6 * a ^ 2 - 4 * a + 1 := by ring
              _ = 1 := by rw [ha2, h4a]; ring⟩
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · rw [Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one]
    have h := (hgen 1).2; rwa [one_mul] at h
  · rw [Nat.cast_add, Nat.cast_one]
    have h := (hgen 1).1; rwa [one_mul] at h
  · rw [Nat.cast_sub (by omega : 1 ≤ 2 * Q), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    exact (hgen 2).2
  · rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    exact (hgen 2).1
  · rw [Nat.cast_sub (by omega : 1 ≤ 3 * Q), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    exact (hgen 3).2
  · rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    exact (hgen 3).1
  · rw [Nat.cast_sub (by omega : 1 ≤ 4 * Q), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    exact (hgen 4).2

/-- For `m ≥ 4`, the 4th roots of unity in `(ZMod (2^m))ˣ` have cardinality 8. -/
private lemma card_ker_pow4_two_pow (m : ℕ) (hm : 4 ≤ m) :
    Nat.card (powMonoidHom (α := (ZMod (2 ^ m))ˣ) 4).ker = 8 := by
  have : NeZero (2 ^ m) := ⟨pow_ne_zero m (by decide)⟩
  have heq : (powMonoidHom (α := (ZMod (2 ^ m))ˣ) 4).ker ≃ {x : ℕ // x ∈ kerPow4Set m} := by
    refine Equiv.ofBijective
      (fun u => ⟨((u.1 : (ZMod (2 ^ m))ˣ) : ZMod (2 ^ m)).val, ?_⟩) ⟨?_, ?_⟩
    · have h4 : ((u.1 : (ZMod (2 ^ m))ˣ) : ZMod (2 ^ m)) ^ 4 = 1 := by
        have hmem := u.2
        rw [MonoidHom.mem_ker, powMonoidHom_apply] at hmem
        simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hmem
      exact mem_kerPow4Set_of_pow4_eq_one m hm _ (ZMod.val_lt _) (by simpa using h4)
    · intro u1 u2 hval
      ext1; apply Units.ext; apply ZMod.val_injective (2 ^ m)
      exact congrArg Subtype.val hval
    · rintro ⟨x, hx⟩
      rcases pow4_eq_one_of_mem_kerPow4Set m hm x hx with ⟨hxlt, hx4⟩
      let u : (ZMod (2 ^ m))ˣ :=
        ⟨(x : ZMod (2 ^ m)), (x : ZMod (2 ^ m)) ^ 3,
         by rw [show (x : ZMod (2 ^ m)) * (x : ZMod (2 ^ m)) ^ 3 = (x : ZMod (2 ^ m)) ^ 4 by ring, hx4],
         by rw [show (x : ZMod (2 ^ m)) ^ 3 * (x : ZMod (2 ^ m)) = (x : ZMod (2 ^ m)) ^ 4 by ring, hx4]⟩
      have hu_mem : u ∈ (powMonoidHom (α := (ZMod (2 ^ m))ˣ) 4).ker := by
        rw [MonoidHom.mem_ker, powMonoidHom_apply]
        apply Units.ext
        simpa [u] using hx4
      refine ⟨⟨u, hu_mem⟩, ?_⟩
      ext1
      change (x : ZMod (2 ^ m)).val = x
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hxlt]
  rw [Nat.card_congr heq, Nat.card_eq_fintype_card, Fintype.card_coe, kerPow4Set_card m hm]

private lemma unitPow4_two_pow_ge4 (m : ℕ) (hm : 4 ≤ m) :
    unitPow4 (2 ^ m) = 2 ^ (m - 4) := by
  have : NeZero (2 ^ m) := ⟨pow_ne_zero m (by decide)⟩
  have hcard : Fintype.card (ZMod (2 ^ m))ˣ = 2 ^ (m - 1) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega)]; ring
  unfold unitPow4
  have hrange : Set.range (fun u : (ZMod (2 ^ m))ˣ => u ^ 4) =
      ((powMonoidHom (α := (ZMod (2 ^ m))ˣ) 4).range : Set (ZMod (2 ^ m))ˣ) := by
    ext y; simp [powMonoidHom_apply]
  rw [hrange]
  change Nat.card (powMonoidHom (α := (ZMod (2 ^ m))ˣ) 4).range = 2 ^ (m - 4)
  have hfirst := QuotientGroup.quotientKerEquivRange (powMonoidHom (α := (ZMod (2 ^ m))ˣ) 4)
  have hmul : Nat.card (powMonoidHom (α := (ZMod (2 ^ m))ˣ) 4).ker *
      Nat.card (powMonoidHom (α := (ZMod (2 ^ m))ˣ) 4).range = Fintype.card (ZMod (2 ^ m))ˣ := by
    rw [← Nat.card_congr hfirst.toEquiv]
    have hl := Subgroup.card_mul_index (powMonoidHom (α := (ZMod (2 ^ m))ˣ) 4).ker
    rw [← Subgroup.index_eq_card] at *
    simpa [Nat.card_eq_fintype_card] using hl
  rw [card_ker_pow4_two_pow m hm, hcard] at hmul
  have hexp : 2 ^ (m - 1) = 8 * 2 ^ (m - 4) := by
    calc 2 ^ (m - 1) = 2 ^ (3 + (m - 4)) := by congr 1; omega
      _ = 8 * 2 ^ (m - 4) := by rw [pow_add]; norm_num
  omega

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

private lemma a052273_base (p e : ℕ) (hp : p.Prime) (he1 : 1 ≤ e) (he4 : e ≤ 4) :
    a052273 (p ^ e) = 1 + unitPow4 (p ^ e) := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have hpe_gt1 : 1 < p ^ e := one_lt_pow₀ hp.one_lt (by omega)
  have : Fact (1 < p ^ e) := ⟨hpe_gt1⟩
  set U : Set (ZMod (p ^ e)) := Set.range (fun u : (ZMod (p ^ e))ˣ => (u : ZMod (p ^ e)) ^ 4)
  have hU_card : Nat.card U = unitPow4 (p ^ e) := by
    unfold unitPow4 U
    have heq : Set.range (fun u : (ZMod (p ^ e))ˣ => u ^ 4) ≃
        Set.range (fun u : (ZMod (p ^ e))ˣ => (u : ZMod (p ^ e)) ^ 4) :=
      Equiv.ofBijective
        (fun ⟨y, hy⟩ => ⟨(y : ZMod (p ^ e)), by rcases hy with ⟨u, rfl⟩; exact ⟨u, by simp⟩⟩)
        ⟨fun a b hab => by ext1; apply Units.ext; exact congrArg Subtype.val hab,
         fun ⟨y, hy⟩ => by rcases hy with ⟨u, rfl⟩; exact ⟨⟨u ^ 4, ⟨u, rfl⟩⟩, by ext; simp⟩⟩
    exact (Nat.card_congr heq).symm
  have h0_not_U : (0 : ZMod (p ^ e)) ∉ U := by
    rintro ⟨u, hu⟩
    have hunit : IsUnit ((0 : ZMod (p ^ e))) := hu ▸ (u ^ 4).isUnit
    have h01 : (0 : ZMod (p ^ e)) = 1 := by
      rcases hunit with ⟨v, hv⟩
      have := v.mul_inv; rw [hv, zero_mul] at this; exact this
    have := congrArg ZMod.val h01
    rw [ZMod.val_zero, ZMod.val_one] at this; omega
  have hrange : Set.range (fun x : ZMod (p ^ e) => x ^ 4) = insert 0 U := by
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, U]
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hpdiv : p ∣ x.val
      · left
        have hp4 : p ^ 4 ∣ x.val ^ 4 := pow_dvd_pow_of_dvd hpdiv 4
        have hpe : p ^ e ∣ x.val ^ 4 := dvd_trans (Nat.pow_dvd_pow p he4) hp4
        have hx : (x.val : ZMod (p ^ e)) = x := ZMod.natCast_zmod_val x
        rw [← hx, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
        exact hpe
      · right
        rcases (isUnit_zmod_prime_pow_iff p e hp he1 x).mpr hpdiv with ⟨u, rfl⟩
        exact ⟨u, rfl⟩
    · rintro (rfl | ⟨u, rfl⟩)
      · exact ⟨0, zero_pow (by decide)⟩
      · exact ⟨(u : ZMod (p ^ e)), rfl⟩
  unfold a052273
  rw [hrange, ← hU_card]
  have hfin : U.Finite := Set.toFinite U
  rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem h0_not_U hfin, Nat.card_coe_set_eq, add_comm]

private lemma a052273_step (p e : ℕ) (hp : p.Prime) :
    a052273 (p ^ (e + 4)) = unitPow4 (p ^ (e + 4)) + a052273 (p ^ e) := by
  have : NeZero (p ^ (e + 4)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set U : Set (ZMod (p ^ (e + 4))) := Set.range (fun u : (ZMod (p ^ (e + 4)))ˣ => (u : ZMod (p ^ (e + 4))) ^ 4)
  set V : Set (ZMod (p ^ (e + 4))) :=
    Set.range (fun y : ZMod (p ^ e) => ((p ^ 4 * y.val ^ 4 : ℕ) : ZMod (p ^ (e + 4))))
  have hU_card : Nat.card U = unitPow4 (p ^ (e + 4)) := by
    unfold unitPow4 U
    have heq : Set.range (fun u : (ZMod (p ^ (e + 4)))ˣ => u ^ 4) ≃
        Set.range (fun u : (ZMod (p ^ (e + 4)))ˣ => (u : ZMod (p ^ (e + 4))) ^ 4) :=
      Equiv.ofBijective
        (fun ⟨y, hy⟩ => ⟨(y : ZMod (p ^ (e + 4))), by rcases hy with ⟨u, rfl⟩; exact ⟨u, by simp⟩⟩)
        ⟨fun a b hab => by ext1; apply Units.ext; exact congrArg Subtype.val hab,
         fun ⟨y, hy⟩ => by rcases hy with ⟨u, rfl⟩; exact ⟨⟨u ^ 4, ⟨u, rfl⟩⟩, by ext; simp⟩⟩
    exact (Nat.card_congr heq).symm
  have hV_card : Nat.card V = a052273 (p ^ e) := by
    unfold a052273
    have hVeq : V = Set.range (fun z : Set.range (fun y : ZMod (p ^ e) => y ^ 4) =>
        ((p ^ 4 * z.1.val : ℕ) : ZMod (p ^ (e + 4)))) := by
      ext w
      simp only [V, Set.mem_range, Subtype.exists]
      constructor
      · rintro ⟨y, rfl⟩
        refine ⟨y ^ 4, ⟨y, rfl⟩, ?_⟩
        have hmod : y.val ^ 4 % p ^ e = (y ^ 4).val := by
          rw [← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]
        rw [ZMod.natCast_eq_natCast_iff']
        rw [show p ^ (e + 4) = p ^ 4 * p ^ e by rw [pow_add, mul_comm],
            Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hmod, Nat.mod_eq_of_lt (ZMod.val_lt _)]
      · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
        refine ⟨y, ?_⟩
        have hmod : y.val ^ 4 % p ^ e = (y ^ 4).val := by
          rw [← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]
        rw [ZMod.natCast_eq_natCast_iff']
        rw [show p ^ (e + 4) = p ^ 4 * p ^ e by rw [pow_add, mul_comm],
            Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hmod, Nat.mod_eq_of_lt (ZMod.val_lt _)]
    have hinj : Function.Injective (fun z : Set.range (fun y : ZMod (p ^ e) => y ^ 4) =>
        ((p ^ 4 * z.1.val : ℕ) : ZMod (p ^ (e + 4)))) := by
      intro z1 z2 hz
      rw [ZMod.natCast_eq_natCast_iff'] at hz
      rw [show p ^ (e + 4) = p ^ 4 * p ^ e by rw [pow_add, mul_comm],
          Nat.mul_mod_mul_left, Nat.mul_mod_mul_left,
          Nat.mod_eq_of_lt (ZMod.val_lt z1.1), Nat.mod_eq_of_lt (ZMod.val_lt z2.1)] at hz
      have hval : z1.1.val = z2.1.val := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 4) hz
      exact Subtype.ext (ZMod.val_injective (p ^ e) hval)
    rw [hVeq, Nat.card_range_of_injective hinj]
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    rintro w ⟨u, rfl⟩ ⟨y, hy⟩
    have hu : IsUnit ((u : ZMod (p ^ (e + 4))) ^ 4) := (u ^ 4).isUnit
    have hnd : ¬ p ∣ ((u : ZMod (p ^ (e + 4))) ^ 4).val :=
      (isUnit_zmod_prime_pow_iff p (e + 4) hp (by omega) _).mp hu
    dsimp only at hy
    rw [← hy] at hnd
    apply hnd
    rw [ZMod.val_natCast]
    exact (Nat.dvd_mod_iff (dvd_pow_self p (by omega))).mpr (dvd_mul_of_dvd_left (dvd_pow_self p (by decide)) _)
  have hrange : Set.range (fun x : ZMod (p ^ (e + 4)) => x ^ 4) = U ∪ V := by
    ext w
    simp only [Set.mem_range, Set.mem_union, U, V]
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hpdiv : p ∣ x.val
      · right
        rcases hpdiv with ⟨q, hq⟩
        refine ⟨(q : ZMod (p ^ e)), ?_⟩
        have hx : (x.val : ZMod (p ^ (e + 4))) = x := ZMod.natCast_zmod_val x
        rw [← hx, hq, ← Nat.cast_pow, show (p * q) ^ 4 = p ^ 4 * q ^ 4 by ring]
        rw [ZMod.natCast_eq_natCast_iff']
        rw [show p ^ (e + 4) = p ^ 4 * p ^ e by rw [pow_add, mul_comm],
            Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
        congr 1
        rw [ZMod.val_natCast, ← Nat.pow_mod]
      · left
        rcases (isUnit_zmod_prime_pow_iff p (e + 4) hp (by omega) x).mpr hpdiv with ⟨u, rfl⟩
        exact ⟨u, rfl⟩
    · rintro (⟨u, rfl⟩ | ⟨y, rfl⟩)
      · exact ⟨(u : ZMod (p ^ (e + 4))), rfl⟩
      · refine ⟨((p * y.val : ℕ) : ZMod (p ^ (e + 4))), ?_⟩
        rw [← Nat.cast_pow, show (p * y.val) ^ 4 = p ^ 4 * y.val ^ 4 by ring]
  change Nat.card (Set.range (fun x : ZMod (p ^ (e + 4)) => x ^ 4)) = unitPow4 (p ^ (e + 4)) + a052273 (p ^ e)
  rw [hrange]
  have hfinU : U.Finite := Set.toFinite U
  have hfinV : V.Finite := Set.toFinite V
  rw [Nat.card_coe_set_eq, Set.ncard_union_eq hdisj hfinU hfinV,
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hU_card, hV_card]

private lemma a052273_one (p : ℕ) : a052273 (p ^ 0) = 1 := by
  have : NeZero (1 : ℕ) := ⟨by decide⟩
  unfold a052273
  rw [pow_zero]
  have hconst : Set.range (fun x : ZMod 1 => x ^ 4) = {0} := by
    ext y; simp [Subsingleton.elim y 0]
  rw [hconst, Nat.card_unique]

private lemma unitPow4_two_small (e : ℕ) (he1 : 1 ≤ e) (he3 : e ≤ 3) : unitPow4 (2 ^ e) = 1 := by
  have : NeZero (2 ^ e) := ⟨pow_ne_zero e (by decide)⟩
  unfold unitPow4
  have hconst : Set.range (fun u : (ZMod (2 ^ e))ˣ => u ^ 4) = {1} := by
    ext y; simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl⟩
      have hcard : Fintype.card (ZMod (2 ^ e))ˣ = 2 ^ (e - 1) := by
        rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega)]; ring
      have hdvd : 2 ^ (e - 1) ∣ 4 := by
        have hcases : e = 1 ∨ e = 2 ∨ e = 3 := by omega
        rcases hcases with rfl | rfl | rfl <;> decide
      rcases hdvd with ⟨q, hq⟩
      rw [hq, pow_mul, ← hcard, pow_card_eq_one, one_pow]
    · rintro rfl; exact ⟨1, one_pow 4⟩
  rw [hconst, Nat.card_unique]

private lemma prove_main :
    (∀ e : ℕ, e % 4 = 0 → a052273 (2 ^ e) = 1 + 2 ^ e / (2 ^ 4 - 1)) ∧
    (∀ e : ℕ, e % 4 ≠ 0 → a052273 (2 ^ e) = 2 + 2 ^ e / (2 ^ 4 - 1)) ∧
    (∀ p e : ℕ, p.Prime → p ≠ 2 →
      a052273 (p ^ e) = 1 + ((p - 1) * p ^ (e + 3)) / (Nat.gcd (p - 1) 4 * (p ^ 4 - 1))) := by
  have htwo : ∀ e : ℕ,
      a052273 (2 ^ e) = (if e % 4 = 0 then 1 else 2) + 2 ^ e / (2 ^ 4 - 1) := by
    intro e
    induction e using Nat.strong_induction_on with
    | h e ih =>
      match e with
      | 0 => simpa using a052273_one 2
      | 1 =>
        rw [a052273_base 2 1 Nat.prime_two (by decide) (by decide), unitPow4_two_small 1 (by decide) (by decide)]
        norm_num
      | 2 =>
        rw [a052273_base 2 2 Nat.prime_two (by decide) (by decide), unitPow4_two_small 2 (by decide) (by decide)]
        norm_num
      | 3 =>
        rw [a052273_base 2 3 Nat.prime_two (by decide) (by decide), unitPow4_two_small 3 (by decide) (by decide)]
        norm_num
      | e' + 4 =>
        rw [a052273_step 2 e' Nat.prime_two, unitPow4_two_pow_ge4 (e' + 4) (by omega), ih e' (by omega)]
        rw [show e' + 4 - 4 = e' by omega, show (e' + 4) % 4 = e' % 4 by omega]
        have hnum : 2 ^ (e' + 4) = 2 ^ e' + 2 ^ e' * (2 ^ 4 - 1) := by ring
        rw [hnum, Nat.add_mul_div_right _ _ (by decide : 0 < 2 ^ 4 - 1)]
        ring
  refine ⟨fun e h => by simpa [h] using htwo e, fun e h => by simpa [h] using htwo e, ?_⟩
  intro p e hp hp2
  set g := Nat.gcd (p - 1) 4
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right (p - 1) (by decide)
  have hg_dvd : g ∣ p - 1 := Nat.gcd_dvd_left (p - 1) 4
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp4_pos : 0 < p ^ 4 - 1 := by
    have : 3 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hp3 4
    omega
  have hden_pos : 0 < g * (p ^ 4 - 1) := Nat.mul_pos hg_pos hp4_pos
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he0 : e = 0
    · subst he0
      rw [a052273_one p]
      have hlt : (p - 1) * p ^ 3 < g * (p ^ 4 - 1) := by
        have h1 : (p - 1) * p ^ 3 < p ^ 4 - 1 := by
          have hp3' : 1 < p ^ 3 := one_lt_pow₀ hp.one_lt (by decide)
          have hsub : (p - 1) * p ^ 3 + p ^ 3 = p ^ 4 := by
            zify [show 1 ≤ p by omega]; ring
          omega
        calc (p - 1) * p ^ 3 < p ^ 4 - 1 := h1
          _ = 1 * (p ^ 4 - 1) := (one_mul _).symm
          _ ≤ g * (p ^ 4 - 1) := Nat.mul_le_mul_right _ hg_pos
      rw [Nat.div_eq_of_lt hlt, add_zero]
    · by_cases he4 : e ≤ 4
      · rw [a052273_base p e hp (by omega) he4, unitPow4_odd_prime_pow p e hp hp2 (by omega)]
        rcases hg_dvd with ⟨q, hq⟩
        have hL : (p - 1) * p ^ (e - 1) / g = q * p ^ (e - 1) := by
          rw [hq, show g * q * p ^ (e - 1) = g * (q * p ^ (e - 1)) by ring,
              Nat.mul_div_cancel_left _ hg_pos]
        have hR : (p - 1) * p ^ (e + 3) / (g * (p ^ 4 - 1)) = q * p ^ (e - 1) := by
          rw [hq, show g * q * p ^ (e + 3) = g * (q * p ^ (e + 3)) by ring,
              Nat.mul_div_mul_left _ _ hg_pos]
          have hdecomp : q * p ^ (e + 3) = q * p ^ (e - 1) + (q * p ^ (e - 1)) * (p ^ 4 - 1) := by
            have h1 : 1 ≤ p ^ 4 := Nat.one_le_pow 4 p hp.pos
            have hexp : p ^ (e + 3) = p ^ (e - 1) * p ^ 4 := by rw [← pow_add]; congr 1; omega
            rw [hexp]; zify [h1]; ring
          have hrem_lt : q * p ^ (e - 1) < p ^ 4 - 1 := by
            have hqle : q ≤ p - 1 := by
              calc q = 1 * q := (one_mul q).symm
                _ ≤ g * q := Nat.mul_le_mul_right q hg_pos
                _ = p - 1 := hq.symm
            have hpe3 : p ^ (e - 1) ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by omega)
            have hmul : q * p ^ (e - 1) ≤ (p - 1) * p ^ 3 := Nat.mul_le_mul hqle hpe3
            have hlt : (p - 1) * p ^ 3 < p ^ 4 - 1 := by
              have hp3' : 1 < p ^ 3 := one_lt_pow₀ hp.one_lt (by decide)
              have hsub : (p - 1) * p ^ 3 + p ^ 3 = p ^ 4 := by
                zify [show 1 ≤ p by omega]; ring
              omega
            omega
          rw [hdecomp, Nat.add_mul_div_right _ _ hp4_pos, Nat.div_eq_of_lt hrem_lt, zero_add]
        rw [hL, hR]
      · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 4 := ⟨e - 4, by omega⟩
        rw [a052273_step p e' hp, unitPow4_odd_prime_pow p (e' + 4) hp hp2 (by omega), ih e' (by omega)]
        rcases hg_dvd with ⟨q, hq⟩
        have hunit : (p - 1) * p ^ (e' + 4 - 1) / g = q * p ^ (e' + 3) := by
          rw [show e' + 4 - 1 = e' + 3 by omega, hq,
              show g * q * p ^ (e' + 3) = g * (q * p ^ (e' + 3)) by ring,
              Nat.mul_div_cancel_left _ hg_pos]
        have hnum : (p - 1) * p ^ (e' + 4 + 3) =
            (p - 1) * p ^ (e' + 3) + (q * p ^ (e' + 3)) * (g * (p ^ 4 - 1)) := by
          have h1 : 1 ≤ p ^ 4 := Nat.one_le_pow 4 p hp.pos
          have hexp : p ^ (e' + 4 + 3) = p ^ (e' + 3) * p ^ 4 := by rw [← pow_add]
          rw [hexp, hq]; zify [h1]; ring
        rw [hunit, hnum, Nat.add_mul_div_right _ _ hden_pos]
        ring

end OMA.P_oeis_a052273

theorem OMA.solution : type_of% @OMA.S_oeis_a052273.main :=
  OMA.P_oeis_a052273.prove_main
