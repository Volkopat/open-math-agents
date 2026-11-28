import FormalConjectures.ErdosProblems.«770»

-- Problem: Erdős Problem 770 — h eq add one
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/770.lean:45 (declaration Erdos770.Nat.Prime.h_eq_add_one)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.E770

open Finset

/-- A field `ZMod q` cannot have `n + 1` distinct `n`-th roots of unity. -/
lemma roots_bound {q n : ℕ} [Fact q.Prime] (hn : 0 < n) (hq : n + 1 < q)
    (h : ∀ i ∈ Icc 1 (n + 1), ((i : ℕ) : ZMod q) ^ n = 1) : False := by
  have hinj : Set.InjOn (fun i : ℕ => (i : ZMod q)) (Icc 1 (n + 1) : Finset ℕ) := by
    intro a ha b hb hab
    simp only [coe_Icc, Set.mem_Icc] at ha hb
    have h1 := (ZMod.natCast_eq_natCast_iff' a b q).mp hab
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
  have hsub : (Icc 1 (n + 1)).image (fun i : ℕ => (i : ZMod q))
      ⊆ (Polynomial.nthRoots n (1 : ZMod q)).toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact h i hi
  have h1 := card_le_card hsub
  rw [card_image_of_injOn hinj, Nat.card_Icc] at h1
  have h2 := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots n (1 : ZMod q))
  omega

lemma dvd_all {q n k : ℕ} (h : q ∣ ((Icc 2 k).image fun i => (i ^ n - 1)).gcd id) :
    ∀ i ∈ Icc 2 k, q ∣ i ^ n - 1 := fun i hi =>
  h.trans (Finset.gcd_dvd (f := id) (mem_image_of_mem _ hi))

lemma cast_pow {q n i : ℕ} (hi : 1 ≤ i) (h : q ∣ i ^ n - 1) : ((i : ℕ) : ZMod q) ^ n = 1 := by
  have h1 := (ZMod.natCast_eq_zero_iff (i ^ n - 1) q).mpr h
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hi), sub_eq_zero] at h1
  exact_mod_cast h1

lemma prime_gt {q n k : ℕ} (hq : q.Prime) (hn : 0 < n) (h : ∀ i ∈ Icc 2 k, q ∣ i ^ n - 1) :
    k < q := by
  by_contra hc
  refine hq.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (h q (mem_Icc.mpr ⟨hq.two_le,
    by omega⟩))).mp ?_))
  rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hq.pos)]
  exact dvd_pow_self q hn.ne'

lemma gcd_top {n : ℕ} (hn : 0 < n) :
    ((Icc 2 (n + 1)).image fun i => (i ^ n - 1)).gcd id = 1 := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro q hq hd
  have hall := dvd_all hd
  have hlt := prime_gt hq hn hall
  haveI := Fact.mk hq
  refine roots_bound hn hlt ?_
  intro i hi
  rw [mem_Icc] at hi
  rcases Nat.eq_or_lt_of_le hi.1 with h1 | h1
  · rw [← h1]; simp
  · exact cast_pow (by omega) (hall i (mem_Icc.mpr ⟨by omega, hi.2⟩))

lemma gcd_n {n : ℕ} (hn : 2 < n) (hnp : ¬ (n + 1).Prime) :
    ((Icc 2 n).image fun i => (i ^ n - 1)).gcd id = 1 := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro q hq hd
  have hall := dvd_all hd
  have hlt := prime_gt hq (by omega) hall
  have hne : q ≠ n + 1 := fun h => hnp (h ▸ hq)
  haveI := Fact.mk hq
  refine roots_bound (q := q) (by omega : 0 < n) (by omega : n + 1 < q) ?_
  intro i hi
  rw [mem_Icc] at hi
  rcases Nat.eq_or_lt_of_le hi.1 with h1 | h1
  · rw [← h1]; simp
  rcases Nat.eq_or_lt_of_le hi.2 with h2 | h2
  · obtain ⟨a, ⟨b, hab⟩, ha2, halt⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hnp
    have hb2 : 2 ≤ b := by rcases b with _ | _ | b <;> simp at hab ⊢ <;> omega
    have hbn : b ≤ n := by nlinarith
    have han : a ≤ n := by omega
    rw [h2, hab, Nat.cast_mul, mul_pow,
      cast_pow (by omega) (hall a (mem_Icc.mpr ⟨ha2, han⟩)),
      cast_pow (by omega) (hall b (mem_Icc.mpr ⟨hb2, hbn⟩)), one_mul]
  · exact cast_pow (by omega) (hall i (mem_Icc.mpr ⟨by omega, by omega⟩))

lemma fermat {n i : ℕ} (hp : (n + 1).Prime) (hi : 2 ≤ i) (hin : i ≤ n) :
    n + 1 ∣ i ^ n - 1 := by
  haveI := Fact.mk hp
  have hi0 : ((i : ℕ) : ZMod (n + 1)) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (by omega) h
    omega
  have h1 := ZMod.pow_card_sub_one_eq_one hi0
  rw [Nat.add_sub_cancel] at h1
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), sub_eq_zero]
  exact_mod_cast h1

end OMA.E770

open OMA.E770 in
theorem OMA.solution : type_of% @Erdos770.Nat.Prime.h_eq_add_one := by
  intro n hn
  have hn0 : 0 < n := by omega
  unfold Erdos770.h
  constructor
  · intro h
    by_contra hnp
    have := h.symm.le.trans (sInf_le ⟨(by exact_mod_cast hn : (2 : ℕ∞) < n), by
      rw [ENat.toNat_natCast]; exact gcd_n hn hnp⟩)
    have h3 : n + 1 ≤ n := by exact_mod_cast this
    omega
  · intro hp
    apply le_antisymm
    · exact sInf_le ⟨(by exact_mod_cast (by omega : 2 < n + 1) : (2 : ℕ∞) < (n + 1 : ℕ)), by
        exact_mod_cast gcd_top hn0⟩
    · apply le_sInf
      rintro m ⟨hm2, hmg⟩
      cases m with
      | top => exact le_top
      | coe k =>
        rw [ENat.toNat_natCast] at hmg
        have hk2 : 2 < k := by exact_mod_cast hm2
        by_contra hc
        have hkn : k ≤ n := by
          by_contra h4
          exact hc (by exact_mod_cast (by omega : n + 1 ≤ k))
        have hd : n + 1 ∣ ((Finset.Icc 2 k).image fun i => (i ^ n - 1)).gcd id := by
          apply Finset.dvd_gcd
          intro b hb
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
          rw [Finset.mem_Icc] at hi
          exact fermat hp hi.1 (by omega)
        rw [hmg] at hd
        have := Nat.dvd_one.mp hd
        omega
