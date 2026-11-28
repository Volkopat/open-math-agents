import Mathlib

/-!
# Can a Mirimanoff prime satisfy 3^(p-1) ≡ 1 (mod p³)?

Source: https://mathoverflow.net/questions/516909
A Mirimanoff prime (base-`3` Wieferich prime) is a prime `p` with `3^(p-1) ≡ 1 (mod p²)`
(the known ones are `11` and `1006003`). The question asks whether such a prime can also
satisfy `3^(p-1) ≡ 1 (mod p³)`. `main` states that one does.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_516909

theorem main : ∃ p : ℕ, p.Prime ∧ 3 ^ (p - 1) ≡ 1 [MOD p ^ 3] := by
  sorry

end OMA.S_mo_516909
