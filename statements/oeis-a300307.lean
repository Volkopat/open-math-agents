import Mathlib

/-!
# A300307: number of solutions to 1 +- 3 +- 6 +- ... +- n*(n+1)/2 == 0 mod n

Source: https://oeis.org/A300307 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A300307 (Seiichi Manyama, Mar 02 2018), offset 1: number of solutions to
1 +- 3 +- 6 +- ... +- n*(n+1)/2 == 0 mod n. Data
1, 2, 0, 4, 4, 16, 12, 32, 20, 112, 88, 384, 308, 1264, 1056, 4096, 3852, 15120, 13820, ...
Entry A000325: a(n) = 2^n - n.

Formula section of A300307: a(2^n) = 2^A000325(n) for n>0 (conjectured).

Formalization notes.
* A solution is a choice of signs for the triangular numbers T(2), ..., T(N), where
  T(k) = k*(k+1)/2 (the sign of T(1) = 1 is +). A choice of signs is the set A of the indices k
  in {2, ..., N} that get the sign -. So `a N` is the number of subsets A of `Finset.Icc 2 N`
  such that N divides the integer Sum_{k=1..N} s(k) * T(k), with s(k) = -1 for k in A and
  s(k) = 1 for k not in A.
* `main` is the conjecture: a(2^n) = 2^(2^n - n) for n > 0.
-/

namespace OMA.S_oeis_a300307

/-- A300307(N): the number of sign choices with 1 ± 3 ± 6 ± ... ± N(N+1)/2 ≡ 0 (mod N). -/
def a (N : ℕ) : ℕ :=
  ((Finset.Icc 2 N).powerset.filter (fun A =>
    (N : ℤ) ∣ ∑ k ∈ Finset.Icc 1 N,
      (if k ∈ A then (-1 : ℤ) else 1) * ((k * (k + 1) / 2 : ℕ) : ℤ))).card

/-- a(2^n) = 2^(2^n - n) for n > 0. -/
theorem main : ∀ n : ℕ, 0 < n → a (2 ^ n) = 2 ^ (2 ^ n - n) := by
  sorry

end OMA.S_oeis_a300307
