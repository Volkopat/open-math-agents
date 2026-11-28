import OMAStatements.S_oeis_a183161

namespace OMA.R_oeis_a183161_R1

open Finset OMA.S_oeis_a183161

/- The candidate is a base-two automaton, starting in state zero and reading
least significant digit first. H1 is independently decidable by a finite
calculation with rational diagonals. H2 is a general lifting lemma about
square roots of integral series with constant coefficient one. -/

def H1 : Prop := ∃ b : ℕ → ℤ,
    (∀ n, b n =
      let transitions : List (ℕ × ℕ) :=
        [(1,2),(1,2),(0,3),(4,5),(6,7),(4,5),(6,4),(7,7)]
      let s := (Nat.digits 2 n).foldl (fun i digit =>
        let row := transitions.getD i (7,7)
        if digit = 0 then row.1 else row.2) 0
      if s ≤ 2 then 1 else if s ≤ 6 then 2 else 0) ∧
    ∀ n, (∑ k ∈ range (n+1), b k * b (n-k)) ≡ (A183160 n : ℤ) [ZMOD 8]

def H2 : Prop := ∀ (a b : ℕ → ℤ), a 0 = 1 → b 0 = 1 →
    (∀ n, (∑ k ∈ range (n+1), a k * a (n-k)) ≡
      (∑ k ∈ range (n+1), b k * b (n-k)) [ZMOD 8]) →
    ∀ n, 4 ∣ a n - b n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a183161.main := by
  rintro ⟨b, hvalue, hconv⟩ lift a ha heq n
  have hb : b 0 = 1 := by rw [hvalue] <;> decide
  have hmod : ∀ m, (∑ k ∈ range (m+1), a k * a (m-k)) ≡
      (∑ k ∈ range (m+1), b k * b (m-k)) [ZMOD 8] := by
    intro m
    have h : (∑ k ∈ range (m+1), a k * a (m-k)) = (A183160 m : ℤ) := by
      simpa only [mul_comm] using heq m
    rw [h]
    exact (hconv m).symm
  obtain ⟨q, hq⟩ := lift a b ha hb hmod n
  have hsmall : b n = 0 ∨ b n = 1 ∨ b n = 2 := by
    rw [hvalue]
    dsimp only
    split <;> (try split) <;> simp
  rcases hsmall with h | h | h <;> omega

end OMA.R_oeis_a183161_R1
