import OMAStatements.S_oeis_a387947
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum
import Mathlib.Data.Finset.Basic

/-! For the prime-square branch, factor the difference of shifted squares. -/

namespace PrimeSquareCollision

private theorem dvd_both {p x y : ℕ} (hp : p.Prime) (h : p^2 ∣ x*y)
    (hx : ¬ p^2 ∣ x) (hy : ¬ p^2 ∣ y) : p ∣ x ∧ p ∣ y := by
  have hd₀ : p ∣ p^2 := ⟨p, by rw [pow_two]⟩
  rcases hp.dvd_mul.mp (hd₀.trans h) with hx' | hy'
  · obtain ⟨k, rfl⟩ := hx'
    rw [pow_two, Nat.mul_assoc] at h
    rcases hp.dvd_mul.mp (Nat.dvd_of_mul_dvd_mul_left hp.pos h) with hk | hy''
    · obtain ⟨l,rfl⟩ := hk
      exact (hx ⟨l, by rw [pow_two, Nat.mul_assoc]⟩).elim
    · exact ⟨⟨k,rfl⟩,hy''⟩
  · obtain ⟨k, rfl⟩ := hy'
    rw [pow_two, Nat.mul_left_comm] at h
    rcases hp.dvd_mul.mp (Nat.dvd_of_mul_dvd_mul_left hp.pos h) with hx'' | hk
    · exact ⟨hx'',⟨k,rfl⟩⟩
    · obtain ⟨l,rfl⟩ := hk
      exact (hy ⟨l, by rw [pow_two, Nat.mul_assoc]⟩).elim

/-- For distinct primes up to the square of an odd prime, a shifted-square collision
forces (and is forced by) both primes being one modulo the prime root. -/
theorem shifted_square_mod_prime_square_iff {p r s : ℕ}
    (hp : p.Prime) (hp2 : 2 < p) (hr : r.Prime) (hs : s.Prime)
    (hsr : s < r) (hrle : r ≤ p^2) :
    ((r-1)^2 ≡ (s-1)^2 [MOD p^2]) ↔ (r ≡ 1 [MOD p]) ∧ (s ≡ 1 [MOD p]) := by
  have hr2 := hr.two_le
  have hs2 := hs.two_le
  have hr1 : 1 ≤ r := by omega
  have hs1 : 1 ≤ s := by omega
  have hsqle : (s-1)^2 ≤ (r-1)^2 := Nat.pow_le_pow_left (by omega) _
  have factor : (r-1)^2-(s-1)^2 = (r+s-2)*(r-s) := by
    simp only [pow_two, Nat.mul_self_sub_mul_self_eq]
    congr 1 <;> omega
  have hpn : p^2 ≠ 0 := pow_ne_zero _ hp.ne_zero
  constructor
  · intro h
    have hprod := (Nat.modEq_iff_dvd' hsqle).mp h.symm
    rw [factor] at hprod
    have hdiff : ¬ p^2 ∣ r-s := by
      intro hd
      have hle := Nat.le_of_dvd (by omega : 0 < r-s) hd
      omega
    have hsum : ¬ p^2 ∣ r+s-2 := by
      intro hd
      by_cases he : s = 2
      · have hq : r = p^2 := by
          have hl := Nat.le_of_dvd (by omega : 0 < r+s-2) hd
          omega
        have hpSq : (p^2).Prime := hq ▸ hr
        have hEq := (Nat.prime_dvd_prime_iff_eq hp hpSq).mp (show p ∣ p^2 from ⟨p, by rw [pow_two]⟩)
        have hlt : p < p^2 := by
          rw [pow_two]
          simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left (by omega : 1 < p) hp.pos
        omega
      · have hlt : r+s-2 < 2*p^2 := by omega
        obtain ⟨j,hj⟩ := hd
        have hjpos : 0 < j := by
          by_contra hn
          have hz : j=0 := by omega
          simp [hz] at hj
          omega
        have hjlt : j < 2 := by
          by_contra hn
          have hh := Nat.mul_le_mul_left (p^2) (show 2 ≤ j by omega)
          rw [← hj, Nat.mul_comm (p^2) 2] at hh
          omega
        have heq : r+s-2 = p^2 := by
          have hj1 : j = 1 := by omega
          simpa [hj1] using hj
        obtain ⟨i,hi⟩ := hr.odd_of_ne_two (by omega)
        obtain ⟨l,hl⟩ := hs.odd_of_ne_two he
        obtain ⟨k,hk⟩ := hp.odd_of_ne_two (by omega)
        have hodd := congrArg (fun t : ℕ => t % 2) heq
        change (r+s-2)%2 = (p^2)%2 at hodd
        rw [pow_two, Nat.mul_mod, show p%2=1 by omega] at hodd
        omega
    obtain ⟨h₁,h₂⟩ := dvd_both hp hprod hsum hdiff
    have no_two : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by decide : 0<2) h; omega
    have dr₂ : p ∣ 2*(r-1) := by convert Nat.dvd_add h₁ h₂ using 1 <;> omega
    have ds₂ : p ∣ 2*(s-1) := by convert Nat.dvd_sub h₁ h₂ using 1 <;> omega
    have dr := (hp.dvd_mul.mp dr₂).resolve_left no_two
    have ds := (hp.dvd_mul.mp ds₂).resolve_left no_two
    exact ⟨((Nat.modEq_iff_dvd' hr1).mpr dr).symm,
      ((Nat.modEq_iff_dvd' hs1).mpr ds).symm⟩
  · rintro ⟨h₁,h₂⟩
    have dr := (Nat.modEq_iff_dvd' hr1).mp h₁.symm
    have ds := (Nat.modEq_iff_dvd' hs1).mp h₂.symm
    have dsum : p ∣ r+s-2 := by convert Nat.dvd_add dr ds using 1 <;> omega
    have ddiff := (Nat.modEq_iff_dvd' hsr.le).mp (h₂.trans h₁.symm)
    apply ((Nat.modEq_iff_dvd' hsqle).mpr ?_).symm
    rw [factor, pow_two]
    exact Nat.mul_dvd_mul dsum ddiff

end PrimeSquareCollision

namespace OMA.R_oeis_a387947_R1

private theorem small_check : ∀ r s : Fin 26,
    r.val.Prime → s.val.Prime → s.val < r.val →
    ¬ ((r.val ≤ 1 ∧ (r.val-1)^2 ≡ (s.val-1)^2 [MOD 1]) ∨
        (r.val ≤ 2 ∧ (r.val-1)^2 ≡ (s.val-1)^2 [MOD 2]) ∨
        (r.val ≤ 4 ∧ (r.val-1)^2 ≡ (s.val-1)^2 [MOD 4]) ∨
        (r.val ≤ 9 ∧ (r.val-1)^2 ≡ (s.val-1)^2 [MOD 9]) ∨
        (r.val ≤ 25 ∧ (r.val-1)^2 ≡ (s.val-1)^2 [MOD 25])) := by
  decide +kernel

private theorem prime_case {n : ℕ} (hn : 2 < n) :
    (n-1)^2 ≡ (2-1)^2 [MOD n] := by
  have hle : (2-1)^2 ≤ (n-1)^2 := Nat.pow_le_pow_left (by omega) _
  apply ((Nat.modEq_iff_dvd' hle).mpr ?_).symm
  refine ⟨n-2,?_⟩
  simp only [pow_two, Nat.mul_self_sub_mul_self_eq]
  congr 1 <;> omega

/-- The prime-square case is exactly a bound on the second prime in the progression 1 modulo p. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 7 ≤ p →
    ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ s < r ∧ r ≤ p^2 ∧
      (r ≡ 1 [MOD p]) ∧ (s ≡ 1 [MOD p])

/-- The remaining nonsquare-prime cases. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 < n → n ≠ 4 → ¬n.Prime →
    (∀ p : ℕ, p.Prime → 2 < p → n ≠ p^2) →
    ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ s < r ∧ r ≤ n ∧ (r-1)^2 ≡ (s-1)^2 [MOD n]

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a387947.main := by
  intro h1 h2 n hn
  constructor
  · rintro ⟨r,s,hr,hs,hsr,hrn,hm⟩ hmem
    have hc : n=1 ∨ n=2 ∨ n=4 ∨ n=9 ∨ n=25 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    have rn : r<26 := by omega
    have sn : s<26 := by omega
    apply small_check ⟨r,rn⟩ ⟨s,sn⟩ hr hs hsr
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨hrn,hm⟩
    · exact Or.inr (Or.inl ⟨hrn,hm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hrn,hm⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hrn,hm⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hrn,hm⟩)))
  · intro h
    have hex : ¬(n=1 ∨ n=2 ∨ n=4 ∨ n=9 ∨ n=25) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using h
    have hgt : 2 < n := by omega
    by_cases hp : n.Prime
    · exact ⟨n,2,hp,by decide,hgt,le_rfl,prime_case hgt⟩
    by_cases hsq : ∃ p : ℕ, p.Prime ∧ 2 < p ∧ n = p^2
    · obtain ⟨p,hp',hp2,rfl⟩ := hsq
      have h7 : 7 ≤ p := by
        by_contra hn7
        have hcases : p=3 ∨ p=4 ∨ p=5 ∨ p=6 := by omega
        rcases hcases with rfl | rfl | rfl | rfl
        · norm_num at hex
        · exact (by decide : ¬ Nat.Prime 4) hp'
        · norm_num at hex
        · exact (by decide : ¬ Nat.Prime 6) hp' 
      obtain ⟨r,s,hr,hs,hsr,hrn,ha,hb⟩ := h1 p hp' h7
      exact ⟨r,s,hr,hs,hsr,hrn,
        (PrimeSquareCollision.shifted_square_mod_prime_square_iff hp' hp2 hr hs hsr hrn).mpr ⟨ha,hb⟩⟩
    · exact h2 n hgt (by omega) hp (fun p hP hgt he => hsq ⟨p,hP,hgt,he⟩)

end OMA.R_oeis_a387947_R1
