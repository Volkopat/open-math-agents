import FormalConjectures.ErdosProblems.«11»

-- Reduction Erdos11.erdos_11.variants.not_four_dvd.R1 of Erdős Problem 11 (n not divisible by 4)
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 11 for `n` not divisible by 4: the odd case and the case `n ≡ 2 (mod 4)`

A number `n > 1` not divisible by `4` is odd or `≡ 2 (mod 4)`. The reduction is this case split
and nothing more.

* `H1` (open): every odd `n > 1` is a squarefree number plus a power of `2`. This is the
  statement of the catalogue problem `Erdos11.erdos_11.variants.all_odd`.
* `H2` (open): every `n ≡ 2 (mod 4)` is a squarefree number plus a power of `2`. Here only
  `2 ^ 0` and the powers `2 ^ l` with `l ≥ 2` can occur, since `n - 2` is divisible by `4`.

Both hypotheses are special cases of the target, and together they are the target.
-/

namespace OMA.R_Erdos11_erdos_11_variants_not_four_dvd_R1

/-- Every odd `n > 1` is the sum of a squarefree number and a power of `2`. -/
def H1 : Prop :=
  ∀ n : ℕ, Odd n → 1 < n → ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l

/-- Every `n ≡ 2 (mod 4)` is the sum of a squarefree number and a power of `2`. -/
def H2 : Prop :=
  ∀ n : ℕ, n % 4 = 2 → ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l

theorem main : H1 → H2 → type_of% @Erdos11.erdos_11.variants.not_four_dvd := by
  intro h1 h2 n hn hn'
  rcases Nat.even_or_odd n with he | ho
  · apply h2 n
    obtain ⟨m, rfl⟩ := he
    omega
  · exact h1 n ho hn'

end OMA.R_Erdos11_erdos_11_variants_not_four_dvd_R1
