import OMAReductions.R_oeis_a387947_R1

/-! The square-residue pigeonhole criterion applies without any hypothesis on
prime pairs. At twice an odd prime, the collision is exactly a distinct
Goldbach representation of the modulus plus two. -/

namespace OMA.R_oeis_a387947_R1_H2_R1

open Finset
open scoped Classical

private theorem collision_iff {n r s : ℕ} (hs : 1 ≤ s) (hlt : s < r) :
    ((r - 1)^2 ≡ (s - 1)^2 [MOD n]) ↔ n ∣ (r - s) * (r + s - 2) := by
  have hle : (s - 1)^2 ≤ (r - 1)^2 := Nat.pow_le_pow_left (by omega) _
  have fac : (r - 1)^2 - (s - 1)^2 = (r - s) * (r + s - 2) := by
    simp only [pow_two, Nat.mul_self_sub_mul_self_eq]
    rw [Nat.mul_comm]
    congr 1 <;> omega
  rw [← fac]
  exact ⟨fun h ↦ (Nat.modEq_iff_dvd' hle).mp h.symm,
    fun h ↦ ((Nat.modEq_iff_dvd' hle).mpr h).symm⟩

private theorem twice_prime {p r s : ℕ} (hp : p.Prime) (hp₂ : 2 < p)
    (hr : r.Prime) (hs : s.Prime) (hrs : s < r) (hrn : r ≤ 2 * p) :
    ((r - 1)^2 ≡ (s - 1)^2 [MOD 2 * p]) ↔ r + s = 2 * p + 2 := by
  have hs₂ := hs.two_le
  have ro := hr.odd_of_ne_two (by omega)
  have po := hp.odd_of_ne_two (by omega)
  constructor
  · intro hc
    have sne : s ≠ 2 := by
      intro he
      obtain ⟨a, ha⟩ := ro
      have h : (r - 1)^2 ≡ (s - 1)^2 [MOD 2] := hc.of_dvd (dvd_mul_right 2 p)
      change (r - 1)^2 % 2 = (s - 1)^2 % 2 at h
      rw [he, pow_two, Nat.mul_mod, show (r - 1) % 2 = 0 by omega] at h
      norm_num at h
    obtain ⟨a, ha⟩ := ro
    obtain ⟨b, hb⟩ := hs.odd_of_ne_two sne
    have d₂ : 2 ∣ r - s := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    have s₂ : 2 ∣ r + s - 2 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    have cop : (2 : ℕ).Coprime p := Nat.coprime_two_left.mpr po
    have divs := (collision_iff (show 1 ≤ s by omega) hrs).mp hc
    have divP : p ∣ (r - s) * (r + s - 2) := (dvd_mul_left p 2).trans divs
    rcases hp.dvd_mul.mp divP with hdiff | hsum
    · have h := Nat.le_of_dvd (by omega : 0 < r - s)
        (cop.mul_dvd_of_dvd_of_dvd d₂ hdiff)
      omega
    · obtain ⟨k, hk⟩ := cop.mul_dvd_of_dvd_of_dvd s₂ hsum
      have kpos : 0 < k := by
        by_contra! hz
        have : k = 0 := by omega
        rw [this, mul_zero] at hk
        omega
      have ksmall : k < 2 := by
        by_contra! ge
        have h := Nat.mul_le_mul_left (2 * p) ge
        rw [← hk] at h
        omega
      rw [show k = 1 by omega, mul_one] at hk
      omega
  · intro h
    apply (collision_iff (show 1 ≤ s by omega) hrs).mpr
    rw [show r + s - 2 = 2 * p by omega]
    exact dvd_mul_left _ _

/-- If the shifted primes outnumber all square residues, two shifts collide. -/
theorem collision_of_density (n : ℕ)
    (h : ((range n).image (fun x : ℕ ↦ x^2 % n)).card <
      ((range (n+1)).filter Nat.Prime).card) :
    ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ s < r ∧ r ≤ n ∧ (r-1)^2 ≡ (s-1)^2 [MOD n] := by
  classical
  by_contra none
  apply (not_le_of_gt h)
  apply card_le_card_of_injOn (fun p : ℕ ↦ (p-1)^2 % n)
  · intro p hp
    obtain ⟨hu, hpr⟩ := mem_filter.mp hp
    have hn := mem_range.mp hu
    have h₂ := hpr.two_le
    exact mem_image.mpr ⟨p-1, mem_range.mpr (by omega), rfl⟩
  · intro p hp q hq he
    obtain ⟨hp', hpP⟩ := mem_filter.mp hp
    obtain ⟨hq', hqP⟩ := mem_filter.mp hq
    have hpN := mem_range.mp hp'
    have hqN := mem_range.mp hq'
    by_contra hne
    rcases lt_or_gt_of_ne hne with lt | gt
    · exact none ⟨q, p, hqP, hpP, lt, by omega, he.symm⟩
    · exact none ⟨p, q, hpP, hqP, gt, by omega, he⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem small_collision {n : ℕ} (h₀ : 2 < n) (h₄ : n ≠ 4)
    (hcomp : ¬ n.Prime) (hsq : ∀ p : ℕ, p.Prime → 2 < p → n ≠ p^2)
    (hle : n ≤ 100) :
    ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ s < r ∧ r ≤ n ∧ (r-1)^2 ≡ (s-1)^2 [MOD n] := by
  let table : List (ℕ × ℕ) := [
    (0, 0), (0, 0), (0, 0), (3, 2), (0, 0), (5, 2), (5, 3), (7, 2), (7, 3), (0, 0),
    (7, 5), (11, 2), (5, 3), (13, 2), (11, 5), (5, 2), (7, 3), (17, 2), (13, 7), (19, 2),
    (7, 5), (11, 5), (13, 11), (23, 2), (11, 3), (0, 0), (17, 11), (13, 7), (11, 5), (29, 2),
    (17, 5), (31, 2), (7, 3), (11, 2), (19, 17), (7, 2), (13, 7), (37, 2), (23, 17), (17, 11),
    (17, 5), (41, 2), (11, 5), (43, 2), (13, 11), (19, 13), (29, 19), (47, 2), (11, 3), (43, 29),
    (29, 23), (17, 2), (17, 11), (53, 2), (13, 7), (17, 7), (17, 13), (23, 17), (31, 29), (59, 2),
    (17, 5), (61, 2), (41, 23), (17, 3), (11, 7), (29, 3), (29, 17), (67, 2), (19, 17), (23, 2),
    (13, 3), (71, 2), (19, 7), (73, 2), (47, 29), (29, 23), (23, 17), (19, 5), (17, 11), (79, 2),
    (17, 5), (37, 19), (43, 41), (83, 2), (11, 5), (17, 2), (47, 41), (29, 2), (29, 17), (89, 2),
    (19, 13), (41, 13), (29, 19), (41, 23), (53, 43), (59, 19), (11, 3), (97, 2), (43, 29), (11, 2),
    (29, 23)]
  have check : ∀ i : Fin 101, 2 < i.val → i.val ≠ 4 → ¬ i.val.Prime →
      (∀ p : Fin 101, p.val.Prime → 2 < p.val → i.val ≠ p.val^2) →
      let w := (table[i.val]?).getD (0, 0)
      w.1.Prime ∧ w.2.Prime ∧ w.2 < w.1 ∧ w.1 ≤ i.val ∧
        (w.1-1)^2 ≡ (w.2-1)^2 [MOD i.val] := by decide +kernel
  let i : Fin 101 := ⟨n, by omega⟩
  have hw := check i h₀ h₄ hcomp (fun p hp h₂ ↦ hsq p hp h₂)
  let w := (table[n]?).getD (0, 0)
  exact ⟨w.1, w.2, hw⟩

/-- The exact Goldbach condition for large twice-prime moduli. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 2 < p → 100 < 2 * p →
    ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ s < r ∧ r + s = 2 * p + 2

/-- For the other eligible moduli outside the density criterion, the two
factors of the modulus can divide the difference and shifted sum separately. -/
def H2 : Prop :=
  ∀ n : ℕ, 100 < n → ¬n.Prime →
    (∀ p : ℕ, p.Prime → 2 < p → n ≠ p^2) →
    (∀ p : ℕ, p.Prime → 2 < p → n ≠ 2*p) →
    ((range (n+1)).filter Nat.Prime).card ≤
      ((range n).image (fun x : ℕ ↦ x^2 % n)).card →
    ∃ r s a b : ℕ, r.Prime ∧ s.Prime ∧ s < r ∧ r ≤ n ∧
      a * b = n ∧ a ∣ r - s ∧ b ∣ r + s - 2

theorem main : H1 → H2 → OMA.R_oeis_a387947_R1.H2 := by
  classical
  intro gold split n h₀ h₄ hcomp hsq
  by_cases hsmall : n ≤ 100
  · exact small_collision h₀ h₄ hcomp hsq hsmall
  by_cases hdensity : ((range n).image (fun x : ℕ ↦ x^2 % n)).card <
      ((range (n+1)).filter Nat.Prime).card
  · exact collision_of_density n hdensity
  by_cases ht : ∃ p : ℕ, p.Prime ∧ 2 < p ∧ n = 2 * p
  · obtain ⟨p, hp, h₂, rfl⟩ := ht
    obtain ⟨r, s, hr, hs, hslt, he⟩ := gold p hp h₂ (by omega)
    have hsr : r ≤ 2 * p := by have := hs.two_le; omega
    exact ⟨r, s, hr, hs, hslt, hsr, (twice_prime hp h₂ hr hs hslt hsr).mpr he⟩
  · obtain ⟨r, s, a, b, hr, hs, hlt, hbound, hab, hda, hdb⟩ :=
      split n (by omega) hcomp hsq (fun p hp h₂ h ↦ ht ⟨p,hp,h₂,h⟩)
        (le_of_not_gt hdensity)
    refine ⟨r, s, hr, hs, hlt, hbound, (collision_iff (by have := hs.two_le; omega) hlt).mpr ?_⟩
    rw [← hab]
    exact Nat.mul_dvd_mul hda hdb

end OMA.R_oeis_a387947_R1_H2_R1
