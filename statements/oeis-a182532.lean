import Mathlib

/-!
# A182532: Carmichael numbers divisible by 7 and 17

Source: https://oeis.org/A182532
Credit: @xor2k

Formalizes the OEIS A182532 conjecture(s), quoted from the entry:

Conjecture (1): Any Carmichael number C divisible by 7 and 17 of the form 10k+1 can be written
as C = 7*17*(120n+119). We got for the tested numbers the following values for n: 478, 1174,
34348, 38350, 82660, 107110, 158658, 162028, 176746, 179278, 262918, 313570, 377788, 563974,
710950.
Conjecture (2): Any Carmichael number C divisible by 7 and 17 of the form 10k+5 can be written
as C = 7*17*(120n+95). We got for the tested numbers the following values for n: 57, 3291,
28965, 357567, 451893.
Conjecture (3): Any Carmichael number C divisible by 7 and 17 of the form 10k+3 can be written
as C = 7*17*(120n+47). We got for the tested numbers the following values for n: 111835, 181157,
222733.
Conjecture (4): Any Carmichael number C divisible by 7 and 17 of the form 10k+9 can be written
as C = 7*17*(120n+71). We got for the tested number the following value for n: 435446.

Conventions: Carmichael numbers are taken with the defining property of OEIS A002997: composite
numbers `m` (that is, `1 < m` and `m` not prime) such that `b^(m-1) ≡ 1 (mod m)` for every `b`
coprime to `m`. The bases `b` range over `ℕ` (every residue class has a natural representative),
and `m - 1` is ordinary subtraction since `m > 1`. Korselt's criterion is not built into the
definition. The condition that `C` is of the form `10k+1`, `10k+5`, `10k+3` or `10k+9` is
rendered as `C % 10 = 1`, `C % 10 = 5`, `C % 10 = 3`, `C % 10 = 9` respectively, which is
equivalent to `∃ k : ℕ, C = 10 * k + d` for the natural number `C` at hand. In each of the four
implications the integer `n` is a natural number `n ≥ 0`, and the existential `n` is local to
that implication, exactly as in the four separate conjectures quoted above.

Remark: this statement is of the same kind as statements/oeis-a182206.lean (same definition of
Carmichael number, same conclusion shape `C = p * q * (a * n + b)`). There the prime divisors are
`37` and `73` and the single form is `37 * 73 * (18 * n + 91)`; here the prime divisors are `7` and
`17` and the form depends on the residue of `C` modulo `10`, as in the four conjectures of A182532:
`120 * n + 119`, `120 * n + 95`, `120 * n + 47`, `120 * n + 71`. The catalogue text of the site
stops after Conjecture (3); Conjecture (4) is taken from the OEIS entry itself.
-/

namespace OMA.S_oeis_a182532

/-- Carmichael numbers: composite `m` with `b^(m-1) ≡ 1 (mod m)` for all `b` coprime to `m`. -/
def IsCarmichael (m : ℕ) : Prop :=
  1 < m ∧ ¬ m.Prime ∧ ∀ b : ℕ, b.Coprime m → b ^ (m - 1) ≡ 1 [MOD m]

/-- Any Carmichael number `C` divisible by `7` and `17` which is `1`, `5`, `3` or `9` modulo
`10` is respectively `7 * 17 * (120 * n + 119)`, `7 * 17 * (120 * n + 95)`,
`7 * 17 * (120 * n + 47)` or `7 * 17 * (120 * n + 71)` for some natural number `n`. -/
theorem main :
    ∀ C : ℕ, IsCarmichael C → 7 ∣ C → 17 ∣ C →
      (C % 10 = 1 → ∃ n : ℕ, C = 7 * 17 * (120 * n + 119)) ∧
      (C % 10 = 5 → ∃ n : ℕ, C = 7 * 17 * (120 * n + 95)) ∧
      (C % 10 = 3 → ∃ n : ℕ, C = 7 * 17 * (120 * n + 47)) ∧
      (C % 10 = 9 → ∃ n : ℕ, C = 7 * 17 * (120 * n + 71)) := by
  sorry

end OMA.S_oeis_a182532
