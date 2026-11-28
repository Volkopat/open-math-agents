import OMAStatements.S_oeis_a387947

/-!
Two elementary witness constructions leave only collisions in which the modulus
splits across the two factors of the difference of squares. The pair involving
two is characterized by the quotient divisibility criterion below. The centered
pair construction is due to Sun (OEIS A387947). We also check all n ≤ 100.

For the converse interpretation of the residual tasks, take d = gcd(n,r-s).
It is smaller than n. If d = 1, the collision forces n to divide r+s-2.
This positive number is less than 2n, so the pair is centered. Otherwise
d and n/d are the two required nontrivial factors.
-/

namespace OMA.R_oeis_a387947_R2

private theorem collision {n r s : ℕ} (hs : 2 ≤ s) (hlt : s < r)
    (hd : n ∣ (r-s) * (r+s-2)) : (r-1)^2 ≡ (s-1)^2 [MOD n] := by
  have hle : (s-1)^2 ≤ (r-1)^2 := Nat.pow_le_pow_left (by omega) _
  apply ((Nat.modEq_iff_dvd' hle).mpr ?_).symm
  have factor : (r-1)^2 - (s-1)^2 = (r-s)*(r+s-2) := by
    rw [pow_two, pow_two, Nat.mul_self_sub_mul_self_eq, Nat.mul_comm]
    congr 1 <;> omega
  rwa [factor]

private theorem small_yes (n : ℕ) (hn : n ≤ 100) (hn₀ : 0 < n)
    (good : n ∉ ({1,2,4,9,25} : Finset ℕ)) :
    ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ s < r ∧ r ≤ n ∧ (r-1)^2 ≡ (s-1)^2 [MOD n] := by
  let witnesses : List (ℕ × ℕ) := [
    (0,0), (0,0), (0,0), (3,2), (0,0), (5,2), (5,3), (7,2),
    (7,3), (0,0), (7,5), (11,2), (5,3), (13,2), (11,5), (5,2),
    (7,3), (17,2), (13,7), (19,2), (7,5), (11,5), (13,11), (23,2),
    (11,3), (0,0), (17,11), (13,7), (11,5), (29,2), (17,5), (31,2),
    (7,3), (11,2), (19,17), (7,2), (13,7), (37,2), (23,17), (17,11),
    (17,5), (41,2), (11,5), (43,2), (13,11), (19,13), (29,19), (47,2),
    (11,3), (43,29), (29,23), (17,2), (17,11), (53,2), (13,7), (17,7),
    (17,13), (23,17), (31,29), (59,2), (17,5), (61,2), (41,23), (17,3),
    (11,7), (29,3), (29,17), (67,2), (19,17), (23,2), (13,3), (71,2),
    (19,7), (73,2), (47,29), (29,23), (23,17), (19,5), (17,11), (79,2),
    (17,5), (37,19), (43,41), (83,2), (11,5), (17,2), (47,41), (29,2),
    (29,17), (89,2), (19,13), (41,13), (29,19), (41,23), (53,43), (59,19),
    (11,3), (97,2), (43,29), (11,2), (29,23)]
  have verified : ∀ i : Fin 101, 0 < i.val → i.val ∉ ({1,2,4,9,25} : Finset ℕ) →
      let w := witnesses[i.val]!
      w.1.Prime ∧ w.2.Prime ∧ w.2 < w.1 ∧ w.1 ≤ i.val ∧ (w.1-1)^2 ≡ (w.2-1)^2 [MOD i.val] := by
    dsimp only [witnesses]
    decide +kernel
  exact ⟨_, _, verified ⟨n, by omega⟩ hn₀ good⟩

private theorem exceptions {n r s : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hlt : s < r) (hle : r ≤ n) (hm : (r-1)^2 ≡ (s-1)^2 [MOD n]) :
    n ∉ ({1,2,4,9,25} : Finset ℕ) := by
  intro bad
  simp only [Finset.mem_insert, Finset.mem_singleton] at bad
  have check : ∀ r s : Fin 26, r.val.Prime → s.val.Prime → s < r →
      ∀ j : Fin 5, let n := ([1,2,4,9,25] : List ℕ)[j.val]!
        r.val ≤ n → ¬ (r.val-1)^2 ≡ (s.val-1)^2 [MOD n] := by
    decide +kernel
  have ht := check ⟨r, by omega⟩ ⟨s, by omega⟩ hr hs hlt
  rcases bad with rfl | rfl | rfl | rfl | rfl
  · exact ht 0 hle hm
  · exact ht 1 hle hm
  · exact ht 2 hle hm
  · exact ht 3 hle hm
  · exact ht 4 hle hm

/-- Odd residual moduli after removing every possible witness with smaller prime two. -/
def H1 : Prop := ∀ n : ℕ, 100 < n → Odd n →
    (∀ p : ℕ, p.Prime → 2 < p → p ∣ n → ¬ n / p ∣ p - 2) →
    ∃ d e r s : ℕ, 1 < d ∧ 1 < e ∧ n = d * e ∧ r.Prime ∧ s.Prime ∧
      2 < s ∧ s < r ∧ r ≤ n ∧ d ∣ r - s ∧ e ∣ r + s - 2

/-- Even residual moduli after removing every distinct-prime Goldbach pair for n+2. -/
def H2 : Prop := ∀ n : ℕ, 100 < n → Even n →
    (¬ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ s < r ∧ r + s = n + 2) →
    ∃ d e r s : ℕ, 1 < d ∧ 1 < e ∧ n = d * e ∧ r.Prime ∧ s.Prime ∧
      2 < s ∧ s < r ∧ r ≤ n ∧ d ∣ r - s ∧ e ∣ r + s - 2

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a387947.main := by
  intro oddCase evenCase n hn
  constructor
  · rintro ⟨r,s,hr,hs,hlt,hle,hm⟩
    exact exceptions hr hs hlt hle hm
  intro outside
  by_cases low : n ≤ 100
  · exact small_yes n low hn outside
  have large : 100 < n := by omega
  by_cases two : ∃ p : ℕ, p.Prime ∧ 2 < p ∧ p ∣ n ∧ n / p ∣ p - 2
  · obtain ⟨p,hp,hp2,hpn,hd⟩ := two
    refine ⟨p,2,hp,Nat.prime_two,hp2,Nat.le_of_dvd hn hpn,collision (by decide) hp2 ?_⟩
    rw [show p+2-2 = p by omega, Nat.mul_comm]
    simpa only [Nat.mul_div_cancel_left' hpn] using Nat.mul_dvd_mul_left p hd
  by_cases centered : ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ s < r ∧ r+s=n+2
  · obtain ⟨r,s,hr,hs,hlt,hsum⟩ := centered
    have hs₂ := hs.two_le
    refine ⟨r,s,hr,hs,hlt,by omega,collision hs₂ hlt ?_⟩
    rw [show r+s-2 = n by omega]
    exact dvd_mul_left _ _
  have split : ∃ d e r s : ℕ, 1 < d ∧ 1 < e ∧ n = d * e ∧ r.Prime ∧ s.Prime ∧
      2 < s ∧ s < r ∧ r ≤ n ∧ d ∣ r - s ∧ e ∣ r + s - 2 := by
    rcases Nat.even_or_odd n with he | ho
    · exact evenCase n large he centered
    · exact oddCase n large ho (fun p hp hgt hd hquot => two ⟨p,hp,hgt,hd,hquot⟩)
  obtain ⟨d,e,r,s,_,_,hde,hr,hs,hgt,hlt,hle,hd,he⟩ := split
  exact ⟨r,s,hr,hs,hlt,hle,collision (by omega) hlt (hde ▸ Nat.mul_dvd_mul hd he)⟩

end OMA.R_oeis_a387947_R2
