import OMAStatements.S_oeis_a131978
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a131978

open OMA.S_oeis_a131978

private lemma prime_dvd_polyProd {n p i : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    p ∣ polyProd n i := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpi : p ∣ i
  · have hp_mem : p ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hp.one_le, hpn⟩
    have hdvd_term : p ∣ i ^ p + p :=
      dvd_add (dvd_pow hpi hp.ne_zero) (dvd_refl p)
    exact dvd_trans hdvd_term (Finset.dvd_prod_of_mem (fun k => i ^ k + k) hp_mem)
  · have hp1_mem : p - 1 ∈ Finset.Icc 1 n :=
      Finset.mem_Icc.mpr ⟨by have := hp.two_le; omega, by omega⟩
    have hdvd_term : p ∣ i ^ (p - 1) + (p - 1) := by
      rw [← ZMod.natCast_eq_zero_iff]
      have hi_ne : (i : ZMod p) ≠ 0 := by
        intro hz
        exact hpi ((ZMod.natCast_eq_zero_iff i p).mp hz)
      have hflt : (i : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hi_ne
      push_cast
      rw [hflt, Nat.cast_sub hp.one_le, Nat.cast_one, ZMod.natCast_self]
      ring
    exact dvd_trans hdvd_term (Finset.dvd_prod_of_mem (fun k => i ^ k + k) hp1_mem)

private lemma primorial_dvd_polyProd (n i : ℕ) : primorial n ∣ polyProd n i := by
  unfold primorial
  refine Finset.prod_primes_dvd (polyProd n i) ?_ ?_
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.prime
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact prime_dvd_polyProd hp.2 (by omega)

private lemma primorial_dvd_factorial (n : ℕ) : primorial n ∣ Nat.factorial n := by
  unfold primorial
  refine Finset.prod_primes_dvd (Nat.factorial n) ?_ ?_
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.prime
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact Nat.dvd_factorial hp.2.pos (by omega)

private lemma primorial_pos (n : ℕ) : 0 < primorial n := by
  unfold primorial
  exact Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos

private lemma A049614_pos (n : ℕ) : 0 < A049614 n := by
  unfold A049614
  have hdvd := primorial_dvd_factorial n
  have hle : primorial n ≤ Nat.factorial n := Nat.le_of_dvd (Nat.factorial_pos n) hdvd
  exact Nat.div_pos hle (primorial_pos n)

private lemma A049614_mem (n : ℕ) :
    0 < A049614 n ∧ ∀ i : ℕ, Nat.factorial n ∣ A049614 n * polyProd n i := by
  refine ⟨A049614_pos n, fun i => ?_⟩
  have h1 : primorial n ∣ polyProd n i := primorial_dvd_polyProd n i
  have h2 : A049614 n * primorial n = Nat.factorial n :=
    Nat.div_mul_cancel (primorial_dvd_factorial n)
  rw [← h2]
  exact mul_dvd_mul_left (A049614 n) h1

private theorem prove_main : type_of% @OMA.S_oeis_a131978.main := by
  intro n _
  set S : Set ℕ := {m : ℕ | 0 < m ∧ ∀ i : ℕ, Nat.factorial n ∣ m * polyProd n i}
  have hmem : A049614 n ∈ S := A049614_mem n
  have hne : S.Nonempty := ⟨A049614 n, hmem⟩
  have hm_mem : A131685 n ∈ S := Nat.sInf_mem hne
  have hm_pos : 0 < A131685 n := hm_mem.1
  by_contra hndvd
  set r := A049614 n % A131685 n
  have hr_pos : 0 < r := by
    have : r ≠ 0 := fun h => hndvd (Nat.dvd_of_mod_eq_zero h)
    omega
  have hr_lt : r < A131685 n := Nat.mod_lt _ hm_pos
  have hr_mem : r ∈ S := by
    refine ⟨hr_pos, fun i => ?_⟩
    have hdiv_eq : A131685 n * (A049614 n / A131685 n) + r = A049614 n :=
      Nat.div_add_mod (A049614 n) (A131685 n)
    have hA : Nat.factorial n ∣ A049614 n * polyProd n i := hmem.2 i
    have hm : Nat.factorial n ∣ A131685 n * polyProd n i := hm_mem.2 i
    have hq : Nat.factorial n ∣ A131685 n * (A049614 n / A131685 n) * polyProd n i := by
      have : A131685 n * (A049614 n / A131685 n) * polyProd n i =
          (A049614 n / A131685 n) * (A131685 n * polyProd n i) := by ring
      rw [this]
      exact dvd_mul_of_dvd_right hm _
    have hsum : A131685 n * (A049614 n / A131685 n) * polyProd n i + r * polyProd n i =
        A049614 n * polyProd n i := by
      rw [← add_mul, hdiv_eq]
    rw [← hsum] at hA
    exact (Nat.dvd_add_right hq).mp hA
  have hle : A131685 n ≤ r := Nat.sInf_le hr_mem
  omega

end OMA.P_oeis_a131978

theorem OMA.solution : type_of% @OMA.S_oeis_a131978.main :=
  OMA.P_oeis_a131978.prove_main
