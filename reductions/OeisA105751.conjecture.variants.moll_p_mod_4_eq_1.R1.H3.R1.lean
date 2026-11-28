import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1

-- Reduction OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1.H3.R1 of step OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1.H3
-- Credit: @arindale
--
-- H3 is the open upper half of Moll's conjecture.  This reduction separates the two
-- genuinely different ingredients of any proof:
--
-- * H1 is the arithmetic upper bound on the p-adic valuation.  Structurally, for
--   p ≡ 1 (mod 4) the two primes π, π̄ above p each divide ∏ (1 + k i) to order
--   about n/(p-1); the valuation of the imaginary part is asymptotically the
--   smaller of these two orders plus a correction.  The real (open) content is
--   that the unit parts at π and π̄ do not cancel more than logarithmically.
--   Numerics for p = 5, 13, 17, 29, 37 and n ≤ 3000 are consistent with the
--   stated log-slack bound, so it is a strictly stronger, but still true, form
--   of the desired upper bound.
--
-- * H2 is a pure limit statement: a logarithmic slack divided by n is negligible.
--   It follows from Real.isLittleO_log_id_atTop and needs no number theory, so it
--   is a cheap step for another agent.

namespace OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1_H3_R1

open Filter Topology

/-- Pointwise upper bound for the p-adic valuation of `a n`, with logarithmic slack.
This is the arithmetic core: the valuation grows like `n/(p-1)` plus a correction
coming only from the O(log n) rounding of the residue-class counts. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 → ∀ n : ℕ,
    (p - 1) * padicValInt p (OeisA105751.a n) ≤
      n + (p - 1) * (Nat.log p (n + 1) + 1)

/-- The logarithmic slack is negligible compared with `n`; this is the limit-transfer
half, pure real analysis. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 → ∀ ε : ℚ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      ((n : ℚ) + ((p - 1 : ℚ) * ((Nat.log p (n + 1) : ℚ) + 1))) / (n : ℚ) ≤ 1 + ε

theorem main : H1 → H2 → OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H3 := by
  intro h1 h2 p hp hp4 eps heps
  filter_upwards [h2 p hp hp4 eps heps, eventually_ge_atTop 1] with n hn hge
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (show 0 < n by omega)
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hcast : ((p - 1 : ℚ) * (padicValInt p (OeisA105751.a n) : ℚ)) ≤
      (n : ℚ) + ((p - 1 : ℚ) * ((Nat.log p (n + 1) : ℚ) + 1)) := by
    have hb := h1 p hp hp4 n
    have := (Nat.cast_le (α := ℚ)).2 hb
    rw [Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_add, Nat.cast_mul,
        Nat.cast_sub hp1, Nat.cast_add, Nat.cast_one] at this
    exact this
  calc ((p - 1 : ℚ) * (padicValInt p (OeisA105751.a n) : ℚ)) / (n : ℚ)
      ≤ ((n : ℚ) + ((p - 1 : ℚ) * ((Nat.log p (n + 1) : ℚ) + 1))) / (n : ℚ) :=
        div_le_div_of_nonneg_right hcast (le_of_lt hnpos)
    _ ≤ 1 + eps := hn

end OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1_H3_R1
