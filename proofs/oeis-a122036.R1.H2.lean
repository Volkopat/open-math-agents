import OMAReductions.R_oeis_a122036_R1
import Mathlib

/-! If `s` is a set of proper divisors of `d` summing to `d`, then `{x * k : x ∈ s}` is a set of
proper divisors of `d * k` summing to `d * k`. -/

theorem OMA.solution : OMA.R_oeis_a122036_R1.H2 := by
  rintro d k hk ⟨s, hs, hsum⟩
  refine ⟨s.image (fun x => x * k), ?_, ?_⟩
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp (hs hx)
    refine Nat.mem_properDivisors.mpr ⟨mul_dvd_mul_right hdvd k, ?_⟩
    nlinarith
  · have hinj : Set.InjOn (fun x => x * k) (s : Set ℕ) := by
      intro a _ b _ h
      exact Nat.eq_of_mul_eq_mul_right hk h
    rw [Finset.sum_image hinj, ← Finset.sum_mul, hsum]
