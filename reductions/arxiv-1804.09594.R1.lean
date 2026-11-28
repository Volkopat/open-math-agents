import OMAStatements.S_arxiv_1804_09594
import Mathlib

namespace OMA.R_arxiv_1804_09594_R1

open OMA.S_arxiv_1804_09594

/-- For every odd seed n ≥ 5 the first two even terms are 2 and 2n. -/
def H1 : Prop := ∀ n : ℕ, Odd n → 5 ≤ n → ∀ x : ℕ, x ≤ 2*n → Even x →
    (InV 2 n x ↔ x = 2 ∨ x = 2*n)

def H2 : Prop := ∀ n : ℕ, Odd n → 5 ≤ n → (∃ k : ℕ, n-1 = 2^k) →
    ∀ x : ℕ, 2*n < x → Even x → (InV 2 n x ↔ x = 2*n^2+2)

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_1804_09594.main := by
  intro h1 h2 n ho hn hk
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hg : 2*n < 2*n^2+2 := by nlinarith [Nat.le_mul_self n]
  constructor
  · rintro ⟨hx,he⟩
    by_cases hs : x ≤ 2*n
    · grind [h1 n ho hn x hs he]
    · grind [h2 n ho hn hk x (by omega) he]
  · rintro (rfl | rfl | rfl)
    · have he : Even (2 : ℕ) := by decide
      exact ⟨(h1 n ho hn 2 (by omega) he).2 (Or.inl rfl), he⟩
    · have he : Even (2*n) := ⟨n, by omega⟩
      exact ⟨(h1 n ho hn _ le_rfl he).2 (Or.inr rfl), he⟩
    · have he : Even (2*n^2+2) := ⟨n^2+1, by omega⟩
      exact ⟨(h2 n ho hn hk _ hg he).2 rfl, he⟩

end OMA.R_arxiv_1804_09594_R1
