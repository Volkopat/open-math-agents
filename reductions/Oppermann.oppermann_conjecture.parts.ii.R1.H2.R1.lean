import OMAReductions.R_Oppermann_oppermann_conjecture_parts_ii_R1
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Sqrt

/-! The second Oppermann interval beyond the finite computation of
Sorenson and Webster. Strong induction identifies the preceding
prime's square interval. Only gaps exceeding its square-root scale
can then miss the desired half interval. -/

namespace OMA.R_Oppermann_oppermann_conjecture_parts_ii_R1_H2_R1

open Finset

/-- The part of the published finite verification above the parent range. -/
def H1 : Prop :=
  ∀ x : ℕ, 1000 < x → x ≤ 70500000000000 →
    ∃ p ∈ Ioo (x ^ 2) (x * (x + 1)), p.Prime

/-- The upper endpoint test for long consecutive prime gaps beyond the
verified square indices. The integer x is the first square index after p. -/
def H2 : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p < q →
    (∀ r : ℕ, p < r → r < q → ¬r.Prime) →
    let x := p.sqrt + 1
    70500000000000 < x → x ^ 2 < q → x < q - p →
    q < x * (x + 1)

theorem main : H1 → H2 → OMA.R_Oppermann_oppermann_conjecture_parts_ii_R1.H2 := by
  intro hfinite hlong x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro hx
    by_cases hcut : x ≤ 70500000000000
    · exact hfinite x hx hcut
    have hprev : x - 1 + 1 = x := by omega
    obtain ⟨r, hr, hrp⟩ := ih (x - 1) (by omega) (by omega)
    obtain ⟨hrlo, hrhi⟩ := mem_Ioo.mp hr
    rw [hprev] at hrhi
    have hrx : r < x ^ 2 := by
      rw [pow_two]
      exact hrhi.trans (Nat.mul_lt_mul_of_pos_right (by omega) (by omega))
    let below := (range (x ^ 2)).filter Nat.Prime
    have hrmem : r ∈ below := mem_filter.mpr ⟨mem_range.mpr hrx, hrp⟩
    let p := below.max' ⟨r, hrmem⟩
    obtain ⟨hpx, hpp⟩ := mem_filter.mp (max'_mem below ⟨r, hrmem⟩)
    have hpx' : p < x ^ 2 := mem_range.mp hpx
    have hrp' : r ≤ p := le_max' below r hrmem
    have hsqrt : p.sqrt + 1 = x := by
      have hlo : x - 1 ≤ p.sqrt := Nat.le_sqrt'.mpr (hrlo.le.trans hrp')
      have hhi : p.sqrt < x := Nat.sqrt_lt'.mpr hpx'
      omega
    have hprime : ∃ q : ℕ, p < q ∧ q.Prime := by
      obtain ⟨q, hq, hqPrime⟩ := Nat.exists_infinite_primes (p + 1)
      exact ⟨q, hq, hqPrime⟩
    let q := Nat.find hprime
    obtain ⟨hpq, hqp⟩ := Nat.find_spec hprime
    change q.Prime at hqp
    have hnop (s : ℕ) (hps : p < s) (hsq : s < q) : ¬s.Prime := by
      intro hsp
      exact (not_le_of_gt hsq) (Nat.find_min' hprime ⟨hps, hsp⟩)
    have hxq : x ^ 2 < q := by
      by_contra! hqx
      have hne : q ≠ x ^ 2 := fun heq ↦
        Nat.Prime.not_prime_pow (by decide : 2 ≤ 2) (heq ▸ hqp)
      have hqmem : q ∈ below := mem_filter.mpr ⟨mem_range.mpr (lt_of_le_of_ne hqx hne), hqp⟩
      exact (not_le_of_gt hpq) (le_max' below q hqmem)
    refine ⟨q, mem_Ioo.mpr ⟨hxq, ?_⟩, hqp⟩
    by_cases hshort : q - p ≤ x
    · have hw : x * (x + 1) = x ^ 2 + x := by ring
      rw [hw]
      omega
    · have hg := hlong p q hpp hqp hpq hnop
      dsimp only at hg
      rw [hsqrt] at hg
      exact hg (lt_of_not_ge hcut) hxq (lt_of_not_ge hshort)

end OMA.R_Oppermann_oppermann_conjecture_parts_ii_R1_H2_R1
