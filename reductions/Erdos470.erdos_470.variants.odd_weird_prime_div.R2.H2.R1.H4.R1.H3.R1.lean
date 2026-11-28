import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H4_R1
import Mathlib
/-! Pseudoperfect multiples of 45 with least extra prime 23 or larger. -/
namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H4_R1_H3_R1
def H1 : Prop := ∀ n : ℕ, Odd n → n.Abundant → n.primeFactors.card ≤ 5 → 45 ∣ n →
    23 ∣ n → (∀ r ∈ n.primeFactors, r ≠ 3 → r ≠ 5 → 23 ≤ r) →
    n.Pseudoperfect

def H2 : Prop := ∀ n : ℕ, Odd n → n.Abundant → n.primeFactors.card ≤ 5 → 45 ∣ n →
    ∀ p ∈ ([29,31,37,41,43] : List ℕ), p ∣ n → (∀ r ∈ n.primeFactors, r ≠ 3 → r ≠ 5 → p ≤ r) → n.Pseudoperfect

theorem minimum_outside (n : ℕ) (S : List ℕ) {p : ℕ} (mp : p ∈ n.primeFactors) (away : p ∉ S) :
    ∃ q ∈ n.primeFactors, q ∉ S ∧ q ≤ p ∧ ∀ r ∈ n.primeFactors, r ∉ S → q ≤ r := by
  let F := n.primeFactors.filter (fun r => r ∉ S)
  have pm : p ∈ F := Finset.mem_filter.mpr ⟨mp,away⟩
  let q := F.min' ⟨p,pm⟩
  have h := Finset.mem_filter.mp (F.min'_mem ⟨p,pm⟩)
  exact ⟨q,h.1,h.2,F.min'_le _ pm,fun r hr ho => F.min'_le _ (Finset.mem_filter.mpr ⟨hr,ho⟩)⟩

theorem main : H1 → H2 → OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H4_R1.H3 := by
  intro f23 large n odd ab _ hc _ d45 no7 no11 no13 no17 no19 ⟨p,listed,dp⟩
  have table : ∀ z ∈ ([17,19,23,29,31,37,41,43] : List ℕ), Nat.Prime z ∧ 5 < z ∧ z ≤ 43 := by decide
  obtain ⟨pp,pbig,p43⟩ := table p listed
  have mp := Nat.mem_primeFactors.mpr ⟨pp,dp,odd.pos.ne'⟩
  obtain ⟨r,mr,ar,rp,least⟩ := minimum_outside n [3,5] mp (by simp [show p≠3 by omega,show p≠5 by omega])
  have rr := Nat.prime_of_mem_primeFactors mr
  have dr := Nat.dvd_of_mem_primeFactors mr
  have low : ∀ j ∈ n.primeFactors, j≠3 → j≠5 → r≤j :=
    fun j mj j3 j5 => least j mj (by simp [j3,j5])
  have census : ∀ j : Fin 44, j.val.Prime → j.val ∉ ([2,3,5,7,11,13] : List ℕ) →
      j.val = 17 ∨ j.val = 19 ∨ j.val = 23 ∨ j.val ∈ ([29,31,37,41,43] : List ℕ) := by decide
  have away : r ∉ ([2,3,5,7,11,13] : List ℕ) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at ar ⊢
    exact ⟨fun e => odd.not_two_dvd_nat (e ▸ dr),ar.1,ar.2,fun e => no7 (e ▸ dr),
      fun e => no11 (e ▸ dr),fun e => no13 (e ▸ dr)⟩
  rcases (show r=17 ∨ r=19 ∨ r=23 ∨ r ∈ ([29,31,37,41,43] : List ℕ) from census ⟨r,by omega⟩ rr away)
      with rfl|rfl|rfl|last
  · exact False.elim (no17 dr)
  · exact False.elim (no19 dr)
  · exact f23 n odd ab hc d45 dr low
  · exact large n odd ab hc d45 r last dr low
end OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H4_R1_H3_R1
