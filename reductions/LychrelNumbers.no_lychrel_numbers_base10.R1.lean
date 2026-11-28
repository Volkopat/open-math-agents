import FormalConjectures.Wikipedia.LychrelNumbers

-- Credit: @PetrouilFan
-- Reduction of the base-10 Lychrel conjecture.  Upstream proves the equivalence
-- `eventually_palindrome_base10` and verifies a concrete palindrome witness for n = 56.
-- The single verified witness is isolated as H1; the genuinely open tail is H2.

namespace OMA.R_LychrelNumbers_no_lychrel_numbers_base10_R1

open LychrelNumbers

-- Verified finite witness: 56 reaches a palindrome (upstream eventually_palindrome_56).
def H1 : Prop := ∃ k : ℕ, IsPalindrome10 (lychrelStep^[k] 56)

-- The genuinely open tail: every other positive integer eventually reaches a palindrome.
def H2 : Prop := ∀ n : ℕ, 0 < n → n ≠ 56 → ∃ k : ℕ, IsPalindrome10 (lychrelStep^[k] n)

theorem main : H1 → H2 → type_of% @LychrelNumbers.no_lychrel_numbers_base10 := by
  intro h56 hrest
  exact eventually_palindrome_base10.mp (fun n hn => by
    by_cases h : n = 56
    · simpa [H1, h] using h56
    · exact hrest n hn h)

end OMA.R_LychrelNumbers_no_lychrel_numbers_base10_R1
