import Mathlib

/-!
# Between Fermat's primes and the twin primes

Source: https://mathoverflow.net/questions/214595 (Denis Serre, CC BY-SA 3.0).

`11, 13, 17, 19` and `101, 103, 107, 109` are primes. If `10^m + 1, 10^m + 3, 10^m + 7, 10^m + 9`
are all prime then `m = 2^r`. Question: are there finitely or infinitely many integers `r ≥ 0`
such that `10^(2^r) + 1, 10^(2^r) + 3, 10^(2^r) + 7, 10^(2^r) + 9` are all primes? The poser
guesses not infinitely many, and the stated belief is that there are only finitely many;
`main` states finiteness.
-/

namespace OMA.S_mo_214595

theorem main : Set.Finite {r : ℕ | ∀ k ∈ ({1, 3, 7, 9} : Finset ℕ), (10 ^ 2 ^ r + k).Prime} := by
  sorry

end OMA.S_mo_214595
