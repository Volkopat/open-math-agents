import OMAStatements.S_oeis_a207262
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a207262.main := by
  intro t
  have f : (4 * t + 2).divisors.filter (fun d => ¬ 2 ∣ d) = (2 * t + 1).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, _⟩, h2⟩
      exact ⟨(Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2))).dvd_of_dvd_mul_left
        (by rwa [show 4 * t + 2 = 2 * (2 * t + 1) by ring] at hd), by omega⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans ⟨2, by ring⟩, by omega⟩, fun h => by have := h.trans hd; omega⟩
  show ∑ d ∈ (4 * t + 2).divisors, d ^ (4 * t + 2) = _
  rw [f, ← ArithmeticFunction.sigma_apply, ← ArithmeticFunction.sigma_apply,
    show 4 * t + 2 = 2 * (2 * t + 1) by ring,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (Nat.coprime_two_left.mpr ⟨t, rfl⟩),
    ArithmeticFunction.sigma_apply (n := 2), Nat.prime_two.divisors]
  simp [add_comm]
