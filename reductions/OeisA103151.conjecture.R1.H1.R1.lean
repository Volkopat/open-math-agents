import OMAReductions.R_OeisA103151_conjecture_R1

/-!
Write the target as three times an odd center. A prime center gives the
diagonal solution, and a fixed small prime can be used in either slot.
For composite centers surviving these tests, a solution is equivalent to
a positive displacement coprime to the center in one of two orientations.
The remaining cases distinguish whether three divides the center.
If it does, the displacement must be nonzero modulo three in both orientations.
-/

namespace OMA.R_OeisA103151_conjecture_R1_H1_R1

open OeisA103151

def H1 : Prop :=
  ∀ m : ℕ, 101 ≤ m → m % 2 = 1 → ¬ m.Prime → 3 ∣ m →
    (∀ r : ℕ, r ≤ 97 → r.Prime → r ≠ 2 →
      ¬ (3 * m - 2 * r).Prime ∧ ¬ ((3 * m - r) / 2).Prime) →
    ∃ k : ℕ, 0 < k ∧ k.Coprime m ∧
      ((97 < m - 2 * k ∧ (m - 2 * k).Prime ∧ (m + 4 * k).Prime) ∨
       (97 < m - 4 * k ∧ (m + 2 * k).Prime ∧ (m - 4 * k).Prime))

def H2 : Prop :=
  ∀ m : ℕ, 101 ≤ m → m % 2 = 1 → ¬ m.Prime → ¬ (3 ∣ m) →
    (∀ r : ℕ, r ≤ 97 → r.Prime → r ≠ 2 →
      ¬ (3 * m - 2 * r).Prime ∧ ¬ ((3 * m - r) / 2).Prime) →
    ∃ k : ℕ, 0 < k ∧ k.Coprime m ∧
      ((97 < m - 2 * k ∧ (m - 2 * k).Prime ∧ (m + 4 * k).Prime) ∨
       (97 < m - 4 * k ∧ (m + 2 * k).Prime ∧ (m - 4 * k).Prime))

section Proof

private theorem witness_iff {n m : ℕ} (hcenter : 2 * n + 1 = 3 * m) :
    1 ≤ a n ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ 2 ∧ 2 * p + q = 3 * m := by
  unfold a
  rw [Finset.one_le_card]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨_, hprime, hp2, hbound, hq⟩ := Finset.mem_filter.mp hp
    exact ⟨p, 2 * n + 1 - 2 * p, hprime, hq, hp2, by omega⟩
  · rintro ⟨p, q, hprime, hq, hp2, heq⟩
    have hq2 := hq.two_le
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      hprime, hp2, by omega, ?_⟩⟩
    convert hq using 1
    omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem small_table : ∀ i : Fin 50, 1 ≤ i.val →
    (6 * i.val + 3 - 6).Prime ∨ (6 * i.val + 3 - 10).Prime ∨
    (6 * i.val + 3 - 14).Prime ∨ (6 * i.val + 3 - 22).Prime ∨
    (6 * i.val + 3 - 34).Prime := by
  decide

private theorem small_center (i : Fin 50) (hi : 1 ≤ i.val) : 1 ≤ a (3 * i.val + 1) := by
  have hc : 2 * (3 * i.val + 1) + 1 = 3 * (2 * i.val + 1) := by omega
  apply (witness_iff hc).2
  rcases small_table i hi with h | h | h | h | h
  · exact ⟨3, _, by decide, h, by decide, by omega⟩
  · have := h.two_le
    exact ⟨5, _, by decide, h, by decide, by omega⟩
  · have := h.two_le
    exact ⟨7, _, by decide, h, by decide, by omega⟩
  · have := h.two_le
    exact ⟨11, _, by decide, h, by decide, by omega⟩
  · have := h.two_le
    exact ⟨17, _, by decide, h, by decide, by omega⟩

private theorem coprime_displacement {m k p q : ℕ} (hk : 0 < k)
    (hp : p.Prime) (hq : q.Prime)
    (h : (p + 2 * k = m ∧ q = m + 4 * k) ∨
         (p = m + 2 * k ∧ q + 4 * k = m)) : k.Coprime m := by
  let g := Nat.gcd k m
  have hgm : g ∣ m := Nat.gcd_dvd_right k m
  have hgk : g ∣ k := Nat.gcd_dvd_left k m
  have hg2 : g ∣ 2 * k := dvd_mul_of_dvd_right hgk 2
  have hg4 : g ∣ 4 * k := dvd_mul_of_dvd_right hgk 4
  have hdiv : g ∣ p ∧ g ∣ q := by
    rcases h with ⟨hp', hq'⟩ | ⟨hp', hq'⟩
    · refine ⟨(Nat.dvd_add_left hg2).mp ?_, ?_⟩
      · rw [hp']
        exact hgm
      · rw [hq']
        exact Nat.dvd_add hgm hg4
    · refine ⟨?_, (Nat.dvd_add_left hg4).mp ?_⟩
      · rw [hp']
        exact Nat.dvd_add hgm hg2
      · rw [hq']
        exact hgm
  change g = 1
  rcases (Nat.dvd_prime hp).mp hdiv.1 with hg | hg
  · exact hg
  rcases (Nat.dvd_prime hq).mp hdiv.2 with hg' | hg'
  · exact hg'
  have hpq : p = q := hg.symm.trans hg'
  rcases h with ⟨hp', hq'⟩ | ⟨hp', hq'⟩ <;> omega

/-- On centers surviving the small-prime tests the displacement problem is exact. -/
theorem displacement_iff {n m : ℕ} (hcenter : 2 * n + 1 = 3 * m)
    (hodd : m % 2 = 1) (hcomp : ¬ m.Prime)
    (hsmall : ∀ r : ℕ, r ≤ 97 → r.Prime → r ≠ 2 →
      ¬ (3 * m - 2 * r).Prime ∧ ¬ ((3 * m - r) / 2).Prime) :
    1 ≤ a n ↔ ∃ k : ℕ, 0 < k ∧ k.Coprime m ∧
      ((97 < m - 2 * k ∧ (m - 2 * k).Prime ∧ (m + 4 * k).Prime) ∨
       (97 < m - 4 * k ∧ (m + 2 * k).Prime ∧ (m - 4 * k).Prime)) := by
  rw [witness_iff hcenter]
  constructor
  · rintro ⟨p, q, hp, hq, hp2, hsum⟩
    have hq2 : q ≠ 2 := by omega
    have hp97 : 97 < p := by
      by_contra! h
      apply (hsmall p h hp hp2).1
      rwa [show 3 * m - 2 * p = q by omega]
    have hq97 : 97 < q := by
      by_contra! h
      apply (hsmall q h hq hq2).2
      rwa [show (3 * m - q) / 2 = p by omega]
    have hpodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).2 hp2
    have hpne : p ≠ m := fun h => hcomp (h ▸ hp)
    by_cases hpbelow : p < m
    · let k := (m - p) / 2
      have hk : 0 < k := by dsimp [k]; omega
      have hp' : p + 2 * k = m := by dsimp [k]; omega
      have hq' : q = m + 4 * k := by omega
      have hc := coprime_displacement hk hp hq (Or.inl ⟨hp', hq'⟩)
      refine ⟨k, hk, hc, Or.inl ?_⟩
      rw [show m - 2 * k = p by omega, ← hq']
      exact ⟨hp97, hp, hq⟩
    · let k := (p - m) / 2
      have hk : 0 < k := by dsimp [k]; omega
      have hp' : p = m + 2 * k := by dsimp [k]; omega
      have hq' : q + 4 * k = m := by omega
      have hc := coprime_displacement hk hp hq (Or.inr ⟨hp', hq'⟩)
      refine ⟨k, hk, hc, Or.inr ?_⟩
      rw [show m - 4 * k = q by omega, ← hp']
      exact ⟨hq97, hp, hq⟩
  · rintro ⟨k, _, _, ⟨h, hp, hq⟩ | ⟨h, hp, hq⟩⟩
    · exact ⟨m - 2 * k, m + 4 * k, hp, hq, by omega, by omega⟩
    · exact ⟨m + 2 * k, m - 4 * k, hp, hq, by omega, by omega⟩

theorem main : H1 → H2 → OMA.R_OeisA103151_conjecture_R1.H1 := by
  intro hDiv hOther n hn hmod
  let m := 2 * (n / 3) + 1
  have hcenter : 2 * n + 1 = 3 * m := by dsimp [m]; omega
  have hodd : m % 2 = 1 := by dsimp [m]; omega
  by_cases hlarge : 101 ≤ m
  · by_cases hp : m.Prime
    · exact (witness_iff hcenter).2 ⟨m, m, hp, hp, by omega, by omega⟩
    by_cases hfound : ∃ r : ℕ, r ≤ 97 ∧ r.Prime ∧ r ≠ 2 ∧
        ((3 * m - 2 * r).Prime ∨ ((3 * m - r) / 2).Prime)
    · obtain ⟨r, hr, hrp, hr2, h | h⟩ := hfound
      · exact (witness_iff hcenter).2 ⟨r, 3 * m - 2 * r, hrp, h, hr2, by omega⟩
      · have hrodd : r % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hrp).2 hr2
        exact (witness_iff hcenter).2 ⟨(3 * m - r) / 2, r, h, hrp, by omega, by omega⟩
    have hsmall (r : ℕ) (hr : r ≤ 97) (hrp : r.Prime) (hr2 : r ≠ 2) :
        ¬ (3 * m - 2 * r).Prime ∧ ¬ ((3 * m - r) / 2).Prime :=
      ⟨fun h => hfound ⟨r, hr, hrp, hr2, Or.inl h⟩,
       fun h => hfound ⟨r, hr, hrp, hr2, Or.inr h⟩⟩
    apply (displacement_iff hcenter hodd hp hsmall).2
    by_cases h3 : 3 ∣ m
    · exact hDiv m hlarge hodd hp h3 hsmall
    · exact hOther m hlarge hodd hp h3 hsmall
  · let i : Fin 50 := ⟨n / 3, by dsimp [m] at hlarge; omega⟩
    have hn' : 3 * i.val + 1 = n := by dsimp [i]; omega
    have hi : 1 ≤ i.val := by dsimp [i]; omega
    simpa only [hn'] using small_center i hi

end Proof

end OMA.R_OeisA103151_conjecture_R1_H1_R1
