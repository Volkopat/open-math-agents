import OMAStatements.S_oeis_a166272
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Order

open Finset OMA.S_oeis_a166272

theorem hbundle_jacobi_dvd (m : ℕ) (hm : Odd m) : m ∣ 3 * jacobiSum m := by
  have hm0 : 0 < m := hm.pos
  by_cases hm1 : m = 1
  · subst m
    exact one_dvd _
  have hm2 : 1 < m := by omega
  have hc : Nat.Coprime m 4 := by
    simpa only [show 4 = 2 * 2 by rfl] using hm.coprime_two_right.mul_right hm.coprime_two_right
  have hzero : jacobiSym 0 m = 0 := jacobiSym.zero_left hm2
  have hb : ∀ x ∈ positiveResidues m, x < m := by
    intro x hx
    obtain ⟨hx, hJ⟩ := mem_filter.mp hx
    obtain ⟨hx1, hxm⟩ := mem_Icc.mp hx
    by_contra h
    have he : x = m := by omega
    subst x
    have hJ0 : jacobiSym (m : ℤ) m = 0 := by
      rw [jacobiSym.mod_left, Int.emod_self]
      exact hzero
    rw [hJ0] at hJ
    contradiction
  have hmap : Set.MapsTo (fun x => 4 * x % m) (positiveResidues m) (positiveResidues m) := by
    intro x hx
    have hJ := (mem_filter.mp hx).2
    have hJ' : jacobiSym ((4 * x % m : ℕ) : ℤ) m = 1 := by
      rw [Int.natCast_mod, Nat.cast_mul, Nat.cast_ofNat, ← jacobiSym.mod_left,
        jacobiSym.mul_left, jacobiSym.at_four hm, hJ, one_mul]
    have hy0 : 0 < 4 * x % m := by
      by_contra h
      have hz : 4 * x % m = 0 := by omega
      rw [hz, Nat.cast_zero, hzero] at hJ'
      contradiction
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hy0, (Nat.mod_lt _ hm0).le⟩, hJ'⟩
  have hinj : Set.InjOn (fun x => 4 * x % m) (positiveResidues m) := by
    intro x hx y hy he
    have he' : Nat.ModEq m x y := Nat.ModEq.cancel_left_of_coprime hc he
    exact he'.eq_of_lt_of_lt (hb x hx) (hb y hy)
  have hsurj := Finset.surjOn_of_injOn_of_card_le (fun x => 4 * x % m) hmap hinj (le_refl _)
  have hsumz : (4 : ZMod m) * (jacobiSum m : ZMod m) = (jacobiSum m : ZMod m) := by
    simp only [jacobiSum, Nat.cast_sum, mul_sum]
    apply Finset.sum_nbij (fun x => 4 * x % m) hmap hinj hsurj
    intro x hx
    simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat]
  apply (ZMod.natCast_eq_zero_iff (3 * jacobiSum m) m).mp
  push_cast
  calc
    (3 : ZMod m) * (jacobiSum m : ZMod m) = 4 * (jacobiSum m : ZMod m) - (jacobiSum m : ZMod m) := by ring
    _ = 0 := by rw [hsumz, sub_self]

lemma hbundle_den_three (n m : ℕ) (hm : m ≠ 0) (h : m ∣ 3 * n)
    (hne : ((n : ℚ) / (m : ℚ)).den ≠ 1) :
    ((n : ℚ) / (m : ℚ)).den = 3 := by
  obtain ⟨t, ht⟩ := h
  have heq : (n : ℚ) / (m : ℚ) = (t : ℚ) / 3 := by
    apply (div_eq_div_iff (Nat.cast_ne_zero.mpr hm) (by norm_num)).2
    exact_mod_cast (show n * 3 = t * m by simpa [Nat.mul_comm] using ht)
  have hd : ((t : ℚ) / 3).den ∣ 3 := by
    change ((t : ℚ) / ((3 : ℕ) : ℚ)).den ∣ (3 : ℕ)
    rw [Rat.natCast_div_eq_divInt]
    exact Int.natCast_dvd_natCast.mp (Rat.den_dvd (t : ℤ) 3)
  rw [heq] at hne ⊢
  exact ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left hne

theorem OMA.solution : type_of% @OMA.S_oeis_a166272.main := by
  intro k hne
  exact hbundle_den_three (jacobiSum (2 * k + 1)) (2 * k + 1) (by omega)
    (hbundle_jacobi_dvd _ ⟨k, by omega⟩) hne
