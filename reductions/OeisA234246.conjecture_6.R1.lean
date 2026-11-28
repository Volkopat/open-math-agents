import FormalConjectures.OEIS.«234246»

/-!
Work with pairs of odd positive integers (u, v) whose totients add to m(m+1).
Each pair covers both u+v and 2u+v because doubling an odd number preserves
its totient. Thus one relation on odd numbers gives two additive representation
problems, with coefficients (1,1) and (2,1).

The two hypotheses ask for these representations outside the observed finite
exceptions. Both were tested from 8 through 1,000,000. The exceptional inputs
allowed by the original conjecture are proved directly below.
-/

-- Credit: @Pixelstorm44
namespace OMA.R_OeisA234246_conjecture_6_R1

/-- Ordinary sums of odd pairs cover the even inputs outside this list. -/
def H1 : Prop :=
  ∀ n : ℕ, 7 < n → Even n →
    n ∉ ([10, 12, 24, 26, 34, 50, 60, 68, 128, 142, 186, 312] : List ℕ) →
    ∃ u v m : ℕ, Odd u ∧ Odd v ∧ n = u + v ∧ u.totient + v.totient = m * (m + 1)

/-- Weighted sums of the same odd pairs cover the odd inputs outside this list. -/
def H2 : Prop :=
  ∀ n : ℕ, 7 < n → Odd n →
    n ∉ ([9, 15, 19, 29, 31, 37, 65, 91, 101, 235] : List ℕ) →
    ∃ u v m : ℕ, Odd u ∧ Odd v ∧ n = 2 * u + v ∧ u.totient + v.totient = m * (m + 1)

theorem main : H1 → H2 → type_of% @OeisA234246.conjecture_6 := by
  intro h₁ h₂ n hn h10 h19
  rcases Nat.even_or_odd n with he | ho
  · by_cases hex : n ∈ ([10, 12, 24, 26, 34, 50, 60, 68, 128, 142, 186, 312] : List ℕ)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hex
      rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (h10 rfl).elim
      · exact ⟨4, by decide, by decide, 2, by decide⟩
      · exact ⟨8, by decide, by decide, 3, by decide⟩
      · exact ⟨4, by decide, by decide, 3, by decide⟩
      · exact ⟨10, by decide, by decide, 3, by decide⟩
      · exact ⟨10, by decide, by decide, 4, by decide⟩
      · exact ⟨6, by decide, by decide, 4, by decide⟩
      · exact ⟨8, by decide, by decide, 4, by decide⟩
      · exact ⟨14, by decide, by decide, 6, by decide⟩
      · exact ⟨22, by decide, by decide, 6, by decide⟩
      · exact ⟨14, by decide, by decide, 9, by decide⟩
      · exact ⟨18, by decide, by decide, 9, by decide⟩
    · obtain ⟨u, v, m, ⟨a, ha⟩, ⟨b, hb⟩, hnuv, hm⟩ := h₁ n hn he hex
      exact ⟨u, by omega, by omega, m, by simpa [hnuv] using hm⟩
  · by_cases hex : n ∈ ([9, 15, 19, 29, 31, 37, 65, 91, 101, 235] : List ℕ)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hex
      rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨4, by decide, by decide, 2, by decide⟩
      · exact ⟨3, by decide, by decide, 2, by decide⟩
      · exact (h19 rfl).elim
      · exact ⟨5, by decide, by decide, 3, by decide⟩
      · exact ⟨4, by decide, by decide, 4, by decide⟩
      · exact ⟨5, by decide, by decide, 4, by decide⟩
      · exact ⟨5, by decide, by decide, 4, by decide⟩
      · exact ⟨3, by decide, by decide, 6, by decide⟩
      · exact ⟨16, by decide, by decide, 8, by decide⟩
      · exact ⟨19, by decide, by decide, 9, by decide⟩
    · obtain ⟨u, v, m, hu, ⟨b, hb⟩, hnuv, hm⟩ := h₂ n hn ho hex
      have hu_pos : 0 < u := by obtain ⟨a, ha⟩ := hu; omega
      refine ⟨2 * u, by omega, by omega, m, ?_⟩
      simpa [hnuv, Nat.totient_two_mul_of_odd hu] using hm

end OMA.R_OeisA234246_conjecture_6_R1
