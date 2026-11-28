import OMAStatements.S_oeis_a113023
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

open OMA.S_oeis_a113023 Finset

namespace DecimalSuffixes

lemma two_generator (s : ℕ) :
    orderOf (2 : ZMod (5 ^ (s + 1))) = 4 * 5 ^ s := by
  let M := 5 ^ (s + 1)
  let x : ZMod M := 2
  let u := ZMod.unitOfCoprime 2 ((by decide : Nat.Coprime 2 5).pow_right (s+1))
  have hu : orderOf u = orderOf x := by
    rw [← orderOf_injective _ Units.coeHom_injective u]
    simp [u, x, M, Units.coeHom_apply, ZMod.coe_unitOfCoprime]
  have hcard : Nat.card (ZMod M)ˣ = 4 * 5 ^ s := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    simp [M, Nat.totient_prime_pow_succ (by decide : Nat.Prime 5), Nat.mul_comm]
  have hd : orderOf x ∣ 4 * 5 ^ s := by
    rw [← hcard, ← hu]
    exact orderOf_dvd_natCard u
  have hp : orderOf (x ^ 4) = 5 ^ s := by
    have h := ZMod.orderOf_one_add_mul_prime (p := 5) (by decide) (by decide)
      3 (by decide) s
    convert h using 2 <;> norm_num [x, M]
  have hpow : 5 ^ s ∣ orderOf x := hp ▸ orderOf_pow_dvd (x := x) 4
  have hf : (4 : ℕ) ∣ orderOf x := by
    have hdvd : 5 ∣ M := dvd_pow_self 5 (by omega : s + 1 ≠ 0)
    let f : ZMod M →+* ZMod 5 := ZMod.castHom hdvd _
    have hfour : orderOf (2 : ZMod 5) = 4 := by
      apply (orderOf_eq_iff (by decide)).2
      constructor
      · decide
      · intro k hk hk0
        interval_cases k <;> decide
    have h := orderOf_map_dvd f.toMonoidHom x
    rw [show f.toMonoidHom x = (2 : ZMod 5) by
      change f 2 = 2
      rw [show (2 : ZMod M) = 1 + 1 by ring, map_add, map_one]
      norm_num] at h
    rwa [hfour] at h
  exact Nat.dvd_antisymm hd (((by decide : Nat.Coprime 4 5).pow_right s).mul_dvd_of_dvd_of_dvd hf hpow)

lemma unit_power (n m : ℕ) (hn : 0 < n) (hm : ¬ 5 ∣ m) :
    ∃ j : ℕ, n ≤ j ∧ Nat.ModEq (5 ^ n) (2 ^ j) m := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let u := ZMod.unitOfCoprime 2 ((by decide : Nat.Coprime 2 5).pow_right (s+1))
  let v := ZMod.unitOfCoprime m (((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr hm).symm.pow_right (s+1))
  have horder : orderOf u = 4 * 5 ^ s := by
    rw [← orderOf_injective _ Units.coeHom_injective u]
    simpa [u, Units.coeHom_apply, ZMod.coe_unitOfCoprime] using two_generator s
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, horder, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow_succ (by decide : Nat.Prime 5)]
    simp [Nat.mul_comm]
  obtain ⟨j, hj⟩ := (mem_powers_iff_mem_zpowers.mpr
    (show v ∈ Subgroup.zpowers u by rw [htop]; trivial) : v ∈ Submonoid.powers u)
  refine ⟨j + orderOf u * (s+1), ?_, ?_⟩
  · have hp := orderOf_pos u
    nlinarith
  · have he : u ^ (j + orderOf u * (s+1)) = v := by
      rw [pow_add u, pow_mul u, pow_orderOf_eq_one, one_pow, mul_one]
      exact hj
    have h := congrArg (fun z : (ZMod (5 ^ (s+1)))ˣ => (z : ZMod (5 ^ (s+1)))) he
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Units.val_pow_eq_pow_val, u, v,
      ZMod.coe_unitOfCoprime] using h

lemma criterion (n m : ℕ) (hn : 1 < n) (hl : 10 ^ (n - 1) ≤ m) (hu : m < 10 ^ n) :
    occurs n m ↔ 2 ^ n ∣ m ∧ ¬ 5 ∣ m := by
  have hp : 10 ^ n = 2 ^ n * 5 ^ n := by rw [← mul_pow]; norm_num
  have hc := ((by decide : Nat.Coprime 2 5).pow_left n).pow_right n
  constructor
  · rintro ⟨j, hj⟩
    have hcj : Nat.ModEq (10^n) (2^j) m := by
      change 2 ^ j % 10 ^ n = m % 10 ^ n
      rwa [Nat.mod_eq_of_lt hu]
    have hjn : n ≤ j := by
      by_contra! h
      have h1 : 2 ^ j ≤ 2 ^ (n-1) := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : 2 ^ (n-1) < 10 ^ (n-1) := Nat.pow_lt_pow_left (by decide) (by omega)
      have h3 := Nat.mod_le (2^j) (10^n)
      omega
    rw [hp, ← Nat.modEq_and_modEq_iff_modEq_mul hc] at hcj
    refine ⟨Nat.modEq_zero_iff_dvd.mp (hcj.1.symm.trans
      (Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 hjn))), ?_⟩
    intro h5
    have hc5 := hcj.2.of_dvd (dvd_pow_self 5 (by omega : n ≠ 0))
    have hbad := Nat.modEq_zero_iff_dvd.mp (hc5.trans (Nat.modEq_zero_iff_dvd.mpr h5))
    exact (by decide : ¬ 5 ∣ 2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hbad)
  · rintro ⟨h2, h5⟩
    obtain ⟨j, hj, he⟩ := unit_power n m (by omega) h5
    refine ⟨j, ?_⟩
    have hcj : Nat.ModEq (10^n) (2^j) m := by
      rw [hp, ← Nat.modEq_and_modEq_iff_modEq_mul hc]
      exact ⟨(Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 hj)).trans
        (Nat.modEq_zero_iff_dvd.mpr h2).symm, he⟩
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hu] using hcj

def good (d b : ℕ) : Finset ℕ :=
  (range (b+1)).filter fun m => m ≠ 0 ∧ d ∣ m ∧ ¬ 5 ∣ m

lemma card_good (d b : ℕ) (hc : Nat.Coprime 5 d) :
    (good d b).card = b / d - b / (5*d) := by
  have he : good d b = ((range (b+1)).filter fun m => m ≠ 0 ∧ d ∣ m) \
      ((range (b+1)).filter fun m => m ≠ 0 ∧ 5*d ∣ m) := by
    ext m
    have key : 5*d ∣ m ↔ 5 ∣ m ∧ d ∣ m :=
      ⟨fun h => ⟨(dvd_mul_right 5 d).trans h, (dvd_mul_left d 5).trans h⟩,
        fun h => hc.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
    simp only [good, mem_filter, mem_sdiff, key]
    tauto
  rw [he, card_sdiff_of_subset, Nat.card_multiples', Nat.card_multiples']
  intro m hm
  simp only [mem_filter] at hm ⊢
  exact ⟨hm.1, hm.2.1, (dvd_mul_left d 5).trans hm.2.2⟩

lemma end_div (z d q : ℕ) (lo : q*d < z) (hi : z ≤ (q+1)*d) :
    (z-1)/d = q := by
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

end DecimalSuffixes

open DecimalSuffixes

theorem OMA.solution : type_of% @OMA.S_oeis_a113023.main := by
  classical
  intro n hn
  obtain ⟨t, rfl⟩ : ∃ t, n = t+2 := ⟨n-2, by omega⟩
  let D := 2 ^ (t+2)
  let L := 10 ^ (t+1)
  let U := 10 ^ (t+2)
  have hL : 0 < L := by dsimp [L]; positivity
  have hU : L ≤ U := by dsimp [L, U]; rw [pow_succ 10 (t+1)]; omega
  have he : terms (t+2) = good D (U-1) \ good D (L-1) := by
    ext m
    simp only [terms, good, mem_filter, mem_Ico, mem_sdiff, mem_range]
    change ((L ≤ m ∧ m < U) ∧ occurs (t+2) m) ↔
      (m < U-1+1 ∧ m ≠ 0 ∧ D ∣ m ∧ ¬5 ∣ m) ∧ ¬(m < L-1+1 ∧ m ≠ 0 ∧ D ∣ m ∧ ¬5 ∣ m)
    by_cases hh : L ≤ m ∧ m < U
    · rw [criterion _ _ (by omega) hh.1 hh.2]
      dsimp only [D]
      omega
    · omega
  have hsub : good D (L-1) ⊆ good D (U-1) := by
    intro m h
    simp only [good, mem_filter, mem_range] at h ⊢
    exact ⟨by omega, h.2⟩
  have hc : Nat.Coprime 5 D := (by decide : Nat.Coprime 5 2).pow_right _
  rw [he, card_sdiff_of_subset hsub, card_good _ _ hc, card_good _ _ hc]
  obtain ⟨w, hw⟩ : Odd (5 ^ t) := (by decide : Odd 5).pow
  have hR : 0 < 2 ^ t := by positivity
  have hL' : L = 10 * 2^t * (2*w+1) := by dsimp [L]; rw [pow_succ, show (10:ℕ) = 2*5 by decide, mul_pow, hw]; ring
  have hU' : U = 100 * 2^t * (2*w+1) := by dsimp [U]; rw [pow_add, show (10:ℕ) = 2*5 by decide, mul_pow, hw]; ring
  have hD : D = 4 * 2^t := by dsimp [D]; rw [pow_add]; ring
  rw [end_div U D (50*w+24) (by rw [hU', hD]; nlinarith) (by rw [hU', hD]; nlinarith),
    end_div U (5*D) (10*w+4) (by rw [hU', hD]; nlinarith) (by rw [hU', hD]; nlinarith),
    end_div L D (5*w+2) (by rw [hL', hD]; nlinarith) (by rw [hL', hD]; nlinarith),
    end_div L (5*D) w (by rw [hL', hD]; nlinarith) (by rw [hL', hD]; nlinarith)]
  simp only [Nat.add_sub_cancel, hw]
  omega
