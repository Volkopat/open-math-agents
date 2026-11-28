import OMAReductions.R_OeisA240088_conjecture_R1

-- Step OeisA240088.conjecture.R1.H1: hypothesis H1 of reduction OeisA240088.conjecture.R1
-- Credit: @luciusacarr
-- H1 := ∀ m : ℕ, 0 < m →     (∀ p ∈ m.primeFactors, Odd (m.factorization p) →       ∃ u v : ℕ, p = u^2 + 2*v^2) →     ∃ x y : ℕ, m = x^2 + 2*y^2

/-! The form `x^2 + 2 y^2` is multiplicative:
`(x^2+2y^2)(z^2+2w^2) = (xz+2yw)^2 + 2(xw-yz)^2`. Split `m = p^e r` with `p = minFac m` and
`p ∤ r`. An even power of `p` is a square, and an odd one is a power of `p`, which is
represented by hypothesis. The cofactor `r < m` has the same exponents at its primes, so it
is represented by induction. -/

namespace OMA.S240088

def Rep (n : ℕ) : Prop := ∃ x y : ℕ, n = x ^ 2 + 2 * y ^ 2

theorem rep_mul {a b : ℕ} (ha : Rep a) (hb : Rep b) : Rep (a * b) := by
  obtain ⟨x, y, rfl⟩ := ha
  obtain ⟨z, w, rfl⟩ := hb
  refine ⟨x * z + 2 * y * w, Int.natAbs ((x : ℤ) * w - (y : ℤ) * z), ?_⟩
  have : (((x ^ 2 + 2 * y ^ 2) * (z ^ 2 + 2 * w ^ 2) : ℕ) : ℤ) =
      (((x * z + 2 * y * w) ^ 2 + 2 * (Int.natAbs ((x : ℤ) * w - (y : ℤ) * z)) ^ 2 : ℕ) : ℤ) := by
    push_cast
    rw [sq_abs]
    ring
  exact_mod_cast this

theorem rep_one : Rep 1 := ⟨1, 0, by norm_num⟩

theorem rep_sq (k : ℕ) : Rep (k ^ 2) := ⟨k, 0, by ring⟩

theorem rep_pow {p : ℕ} (hp : Rep p) (e : ℕ) : Rep (p ^ e) := by
  induction e with
  | zero => simpa using rep_one
  | succ e ih => rw [pow_succ]; exact rep_mul ih hp

theorem main : ∀ m : ℕ, 0 < m →
    (∀ p ∈ m.primeFactors, Odd (m.factorization p) → ∃ u v : ℕ, p = u ^ 2 + 2 * v ^ 2) →
    Rep m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm hyp
  rcases Nat.eq_or_lt_of_le hm with h1 | h1
  · rw [← h1]; exact rep_one
  set p := m.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  obtain ⟨e, r, hpr, hmr⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : m ≠ 0) p hp.ne_one
  have hr0 : r ≠ 0 := by rintro rfl; simp at hmr; omega
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      simp at hmr
      exact absurd (hmr ▸ Nat.minFac_dvd m) hpr
    · exact h
  have hpe0 : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hfac : m.factorization = (p ^ e).factorization + r.factorization := by
    rw [hmr, Nat.factorization_mul hpe0 hr0]
  have hpe : (p ^ e).factorization = e • Finsupp.single p 1 := by
    rw [Nat.factorization_pow, hp.factorization]
  have hrlt : r < m := by
    rw [hmr]
    have : 2 ≤ p ^ e := by
      calc 2 ≤ p := hp.two_le
        _ ≤ p ^ e := Nat.le_self_pow (by omega) p
    have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    nlinarith
  have hrep_r : Rep r := by
    apply ih r hrlt (Nat.pos_of_ne_zero hr0)
    intro q hq hodd
    have hqp : q ≠ p := by
      rintro rfl
      exact hpr (Nat.dvd_of_mem_primeFactors hq)
    have hqm : q ∈ m.primeFactors := by
      rw [Nat.mem_primeFactors] at hq ⊢
      refine ⟨hq.1, ?_, by omega⟩
      rw [hmr]
      exact Dvd.dvd.mul_left hq.2.1 _
    apply hyp q hqm
    rw [hfac, Finsupp.add_apply, hpe]
    simpa [Finsupp.single_apply, Ne.symm hqp] using hodd
  have hrep_pe : Rep (p ^ e) := by
    rcases Nat.even_or_odd e with ⟨k, hk⟩ | hodd
    · rw [hk, ← two_mul, pow_mul']
      exact rep_sq _
    · have hpm : p ∈ m.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, Nat.minFac_dvd m, by omega⟩
      have hfp : m.factorization p = e := by
        rw [hfac, Finsupp.add_apply, hpe, Nat.factorization_eq_zero_of_not_dvd hpr]
        simp
      obtain ⟨u, v, huv⟩ := hyp p hpm (hfp ▸ hodd)
      exact rep_pow ⟨u, v, huv⟩ e
  rw [hmr]
  exact rep_mul hrep_pe hrep_r

end OMA.S240088

theorem OMA.solution : OMA.R_OeisA240088_conjecture_R1.H1 := by
  intro m hm hyp
  exact OMA.S240088.main m hm hyp
