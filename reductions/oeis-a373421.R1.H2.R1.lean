import OMAReductions.R_oeis_a373421_R1

/-!
# A373421, step `R1.H2`: a finite range and the tail

Step `oeis-a373421.R1.H2` says that every `n > 2671` is a practical number plus a pentagonal
number. This reduction splits it at `98000`:

* `H1`, a finite range: every `n` with `2671 < n ≤ 98000` is representable. A kernel-checked
  proof is ready (sent as step `oeis-a373421.R1.H2.R1.H1` once this file is merged). Almost every
  such `n` is `P_k + 2^a 3^b t` with `t ≤ σ(2^a 3^b) + 1`, which is practical by Margenstern's
  lemma (if `m` is practical and `t ≤ σ(m) + 1` then `m t` is practical); a certificate lists one
  such decomposition per `n`, and the 25 remaining `n` use longer Stewart chains.
* `H2`, the open tail: every `n > 98000` is representable. Somu and Tran (2024) checked this
  numerically up to `10^8`; no proof is known.
-/

namespace OMA.R_oeis_a373421_R1_H2_R1

open OMA.S_oeis_a373421

/-- Every integer in `(2671, 98000]` is a practical number plus a pentagonal number. -/
def H1 : Prop := ∀ n : ℕ, 2671 < n → n ≤ 98000 → IsRepresentable n

/-- Every integer above `98000` is a practical number plus a pentagonal number. -/
def H2 : Prop := ∀ n : ℕ, 98000 < n → IsRepresentable n

theorem main : H1 → H2 → OMA.R_oeis_a373421_R1.H2 := by
  intro h1 h2 n hn
  rcases Nat.lt_or_ge 98000 n with h | h
  · exact h2 n h
  · exact h1 n hn h

end OMA.R_oeis_a373421_R1_H2_R1
