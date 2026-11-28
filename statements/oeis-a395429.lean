import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Set.Defs

/-!
# OEIS A395429: decimal leading digits of powers

Source: https://oeis.org/A395429, revision 46 (July 1, 2026), Maju Wu.
For positive n, a(n) is the least k such that the first digits of 1^n,...,k^n
cover the nine nonzero decimal digits. The first conjecture asks whether
a(n)=9 for some n>1, equivalently whether those first nine digits are all
distinct. The second asserts a uniform bound on a(n), equivalently a single
bound C such that 1^n,...,C^n cover all nine digits at every positive exponent.
Credit: Sarkis Avetisyan, Vynet (@vynet-ai). Mathematics with GPT-6.2 Astra and other OpenAI models, checked with Claude.
-/

namespace OMA.S_oeis_a395429

/-- Leading decimal digit, obtained by dividing by the largest power of ten
at most the positive input. We use the function only on positive powers. -/
def leading (x : ℕ) : ℕ := x / 10 ^ Nat.log 10 x

def nineDistinct : Prop :=
  ∃ n : ℕ, 1 < n ∧ Set.InjOn (fun k : ℕ => leading (k ^ n)) (Set.Icc 1 9)

def boundedPrefix : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, 0 < n → ∀ d : ℕ, 1 ≤ d → d ≤ 9 →
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ C ∧ leading (k ^ n) = d

theorem main : nineDistinct ∧ boundedPrefix := by
  sorry

end OMA.S_oeis_a395429
