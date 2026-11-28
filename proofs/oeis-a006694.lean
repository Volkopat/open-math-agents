import OMAStatements.S_oeis_a006694
import Mathlib

/-!
Shevelev's formula `a((3^n - 1)/2) = n`. Modulo `3^n`, every nonzero residue is `3^j * u` with
`j < n` and `u` a unit, and `j` is the 3-adic valuation of its representative. Multiplying by a
power of 2 keeps `j`, and 2 generates the units mod `3^n`: its square `4 = 1 + 3` has order
`3^(n-1)` (Mathlib's `ZMod.orderOf_one_add_prime`), and its order is even because
`2^odd = -1 mod 3`, so the order is `2 * 3^(n-1) = φ(3^n)`. Hence the cosets of 2 on nonzero
residues are exactly the `n` valuation layers.
-/

namespace A006694Proof

open OMA.S_oeis_a006694

/-- the unit 2 in `ZMod (3^n)` -/
def two (n : ℕ) : (ZMod (3 ^ n))ˣ :=
  ZMod.unitOfCoprime 2 (Nat.Coprime.pow_right n (by norm_num))

lemma two_coe (n : ℕ) : ((two n : (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n)) = 2 := by
  simp [two]

lemma orderOf_two (m : ℕ) : orderOf (two (m + 1)) = 3 ^ m * 2 := by
  have h4 := ZMod.orderOf_one_add_prime Nat.prime_three (by norm_num) m
  norm_num at h4
  have hsq : orderOf ((two (m + 1)) ^ 2) = 3 ^ m := by
    rw [← orderOf_units, Units.val_pow_eq_pow_val, two_coe]; norm_num; exact h4
  rw [orderOf_pow' _ (by norm_num)] at hsq
  have hpos : 0 < orderOf (two (m + 1)) := orderOf_pos _
  set d := orderOf (two (m + 1)) with hd
  have hg : Nat.gcd d 2 = 1 ∨ Nat.gcd d 2 = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp (Nat.gcd_dvd_right d 2)
  rcases hg with hg | hg
  · exfalso
    rw [hg, Nat.div_one] at hsq
    have h1 : (two (m + 1)) ^ (3 ^ m) = 1 := by rw [← hsq, hd]; exact pow_orderOf_eq_one _
    have h2 : ((2 : ZMod (3 ^ (m + 1)))) ^ (3 ^ m) = 1 := by
      have := congrArg (fun u : (ZMod (3 ^ (m + 1)))ˣ => (u : ZMod (3 ^ (m + 1)))) h1
      simpa [Units.val_pow_eq_pow_val, two_coe] using this
    have h3 := congrArg (ZMod.castHom (show 3 ∣ 3 ^ (m + 1) from dvd_pow_self 3 (by omega))
      (ZMod 3)) h2
    rw [map_pow, map_one, map_ofNat] at h3
    have hodd : Odd (3 ^ m) := Odd.pow (by decide)
    have e : (2 : ZMod 3) = -1 := by decide
    rw [e, hodd.neg_one_pow] at h3
    exact absurd h3 (by decide)
  · rw [hg] at hsq
    have := Nat.div_mul_cancel (show 2 ∣ d from hg ▸ Nat.gcd_dvd_left d 2)
    rw [hsq] at this; exact this.symm

lemma gen (m : ℕ) (w : (ZMod (3 ^ (m + 1)))ˣ) : ∃ k : ℕ, w = (two (m + 1)) ^ k := by
  have hcard : Fintype.card (ZMod (3 ^ (m + 1)))ˣ = 3 ^ m * 2 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ Nat.prime_three]
  set t := two (m + 1)
  have himg : (Finset.range (orderOf t)).image (fun k => t ^ k) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn, Finset.card_range, orderOf_two, hcard]
    intro a ha b hb hab
    exact pow_injOn_Iio_orderOf (by simpa using ha) (by simpa using hb) hab
  have hw : w ∈ (Finset.range (orderOf t)).image (fun k => t ^ k) := by rw [himg]; simp
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hw
  exact ⟨k, hk.symm⟩


/-- decomposition `x = 3^j * u` with `u` a unit -/
lemma decomp (n : ℕ) (x : ZMod (3 ^ n)) (hx : x ≠ 0) :
    ∃ j < n, ∃ u : (ZMod (3 ^ n))ˣ, x = 3 ^ j * u := by
  have hv : x.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
  obtain ⟨j, u', hu', he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hv 3 (by norm_num)
  have hlt : x.val < 3 ^ n := ZMod.val_lt x
  have hj : j < n := by
    by_contra h
    have : 3 ^ n ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 3 ^ j ≤ x.val := by rw [he]; exact Nat.le_mul_of_pos_right _ (by
      rcases Nat.eq_zero_or_pos u' with h0 | h0
      · exact absurd (h0 ▸ dvd_zero 3) hu'
      · exact h0)
    omega
  have hcop : Nat.Coprime u' (3 ^ n) :=
    Nat.Coprime.pow_right n ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hu'))
  refine ⟨j, hj, ZMod.unitOfCoprime u' hcop, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val x, he]
  push_cast; ring

/-- the exponent in such a decomposition is the 3-adic valuation of `x.val` -/
lemma val_of_decomp (n j : ℕ) (hj : j < n) (u : (ZMod (3 ^ n))ˣ) :
    padicValNat 3 ((3 : ZMod (3 ^ n)) ^ j * u).val = j := by
  have hc := ZMod.val_coe_unit_coprime u
  have hu3 : ¬ 3 ∣ (u : ZMod (3 ^ n)).val := by
    intro h
    have := Nat.Coprime.coprime_dvd_left h hc
    have h3 : 3 ∣ 3 ^ n := dvd_pow_self 3 (by omega)
    have := Nat.Coprime.coprime_dvd_right h3 this
    norm_num at this
  have hval3 : ((3 : ZMod (3 ^ n)) ^ j).val = 3 ^ j := by
    rw [show (3 : ZMod (3 ^ n)) ^ j = ((3 ^ j : ℕ) : ZMod (3 ^ n)) by push_cast; rfl,
      ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hj)]
  rw [ZMod.val_mul, hval3]
  generalize (u : ZMod (3 ^ n)).val = v at hu3 ⊢
  have hsplit : 3 ^ n = 3 ^ j * 3 ^ (n - j) := by rw [← pow_add]; congr 1; omega
  rw [hsplit, Nat.mul_mod_mul_left]
  have hnd : ¬ 3 ∣ v % 3 ^ (n - j) := by
    rw [Nat.dvd_mod_iff (dvd_pow_self 3 (by omega))]; exact hu3
  have hne : v % 3 ^ (n - j) ≠ 0 := fun h => hnd (h ▸ dvd_zero 3)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [padicValNat.mul (by positivity) hne, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hnd, add_zero]


lemma gen' (n : ℕ) (hn : 0 < n) (w : (ZMod (3 ^ n))ˣ) : ∃ k : ℕ, w = (two n) ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact gen m w

lemma vbound (n : ℕ) (x : {x : ZMod (3 ^ n) // x ≠ 0}) : padicValNat 3 x.1.val < n := by
  obtain ⟨j, hj, u, hu⟩ := decomp n x.1 x.2
  rw [hu, val_of_decomp n j hj u]; exact hj

lemma count (n : ℕ) :
    Nat.card (Quot (fun x y : {x : ZMod (3 ^ n) // x ≠ 0} => SameCoset (3 ^ n) x.1 y.1)) = n := by
  let v : {x : ZMod (3 ^ n) // x ≠ 0} → Fin n := fun x => ⟨padicValNat 3 x.1.val, vbound n x⟩
  have inv : ∀ x y : {x : ZMod (3 ^ n) // x ≠ 0}, SameCoset (3 ^ n) x.1 y.1 → v x = v y := by
    rintro x y ⟨k, hk⟩
    obtain ⟨j, hj, u, hu⟩ := decomp n x.1 x.2
    have hy : y.1 = 3 ^ j * ((two n ^ k * u : (ZMod (3 ^ n))ˣ) : ZMod (3 ^ n)) := by
      rw [hk, hu, Units.val_mul, Units.val_pow_eq_pow_val, two_coe]; ring
    apply Fin.ext
    simp only [v]
    rw [hy, hu, val_of_decomp n j hj, val_of_decomp n j hj]
  let F : Quot (fun x y : {x : ZMod (3 ^ n) // x ≠ 0} => SameCoset (3 ^ n) x.1 y.1) → Fin n :=
    Quot.lift v inv
  have hF : Function.Bijective F := by
    constructor
    · intro qx qy
      induction qx using Quot.ind with
      | mk x =>
      induction qy using Quot.ind with
      | mk y =>
      intro hxy
      have hv : v x = v y := hxy
      obtain ⟨j, hj, u, hu⟩ := decomp n x.1 x.2
      obtain ⟨i, hi, w, hw⟩ := decomp n y.1 y.2
      have hvx : (v x : ℕ) = j := by simp only [v]; rw [hu, val_of_decomp n j hj]
      have hvy : (v y : ℕ) = i := by simp only [v]; rw [hw, val_of_decomp n i hi]
      have hij : i = j := by rw [← hvx, ← hvy, hv]
      subst hij
      obtain ⟨k, hk⟩ := gen' n (by omega) (w * u⁻¹)
      apply Quot.sound
      refine ⟨k, ?_⟩
      have hw' : w = two n ^ k * u := by rw [← hk]; group
      rw [hw, hu, hw', Units.val_mul, Units.val_pow_eq_pow_val, two_coe]; ring
    · rintro ⟨j, hj⟩
      have hne : (3 : ZMod (3 ^ n)) ^ j ≠ 0 := by
        intro h0
        have : ((3 ^ j : ℕ) : ZMod (3 ^ n)) = 0 := by push_cast; exact h0
        rw [ZMod.natCast_eq_zero_iff] at this
        have := Nat.le_of_dvd (by positivity) this
        have := Nat.pow_lt_pow_right (show 1 < 3 by norm_num) hj
        omega
      refine ⟨Quot.mk _ ⟨3 ^ j, hne⟩, ?_⟩
      apply Fin.ext
      show padicValNat 3 ((3 : ZMod (3 ^ n)) ^ j).val = j
      have := val_of_decomp n j hj 1
      simpa using this
  rw [Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem solved : ∀ n : ℕ, a ((3 ^ n - 1) / 2) = n := by
  intro n
  have hodd : 3 ^ n % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
  have hN : 2 * ((3 ^ n - 1) / 2) + 1 = 3 ^ n := by
    have : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
    omega
  unfold a
  rw [hN]
  exact count n

end A006694Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a006694.main := A006694Proof.solved
