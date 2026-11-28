import OMAReductions.R_FortuneConjecture_fortune_conjecture_R1

-- Step FortuneConjecture.fortune_conjecture.R1.H1: hypothesis H1 of reduction FortuneConjecture.fortune_conjecture.R1
-- Credit: @luciusacarr
-- H1 := ∀ n : ℕ, FortuneConjecture.fortunateNumber n < (Nat.nth Nat.Prime (n + 1)) ^ 2 →     (FortuneConjecture.fortunateNumber n).Prime

/-! Let `q` be the Fortunate number and `P = p_{n+1}` (`Nat.nth Nat.Prime n`). A prime `r ≤ P`
divides `P#`; if it also divided `q` it would divide the prime `P# + q > r`, impossible. So every
prime factor of `q` exceeds `P`, hence is at least the next prime `Q`. A composite `q` would then
satisfy `Q^2 ≤ minFac(q)^2 ≤ q`, contradicting `q < Q^2`. -/

theorem OMA.solution : OMA.R_FortuneConjecture_fortune_conjecture_R1.H1 := by
  intro n hlt
  obtain ⟨h1, hprime⟩ := FortuneConjecture.fortunateNumber_spec n
  set q := FortuneConjecture.fortunateNumber n with hq
  set P := Nat.nth Nat.Prime n with hP
  -- every prime factor of q is larger than P
  have hbig : ∀ r, r.Prime → r ∣ q → P < r := by
    intro r hr hrq
    by_contra hle
    push Not at hle
    have hrN : r ∣ primorial P := by
      unfold primorial
      exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hr⟩)
    have hrs : r ∣ primorial P + q := dvd_add hrN hrq
    have heq : r = primorial P + q := (Nat.prime_dvd_prime_iff_eq hr hprime).mp hrs
    have hrle : r ≤ q := Nat.le_of_dvd (by omega) hrq
    have : 0 < primorial P := primorial_pos P
    omega
  -- hence at least the next prime
  have hinf : (setOf Nat.Prime).Infinite := Nat.infinite_setOf_prime
  have hnext : ∀ r, r.Prime → P < r → Nat.nth Nat.Prime (n + 1) ≤ r := by
    intro r hr hPr
    have hc : Nat.nth Nat.Prime (Nat.count Nat.Prime r) = r := Nat.nth_count hr
    have hcn : n + 1 ≤ Nat.count Nat.Prime r := by
      by_contra h
      push Not at h
      have : Nat.nth Nat.Prime (Nat.count Nat.Prime r) ≤ Nat.nth Nat.Prime n :=
        (Nat.nth_strictMono hinf).monotone (by omega)
      omega
    calc Nat.nth Nat.Prime (n + 1) ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime r) :=
          (Nat.nth_strictMono hinf).monotone hcn
      _ = r := hc
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmf : (Nat.minFac q).Prime := Nat.minFac_prime hq1
  have hmfd : Nat.minFac q ∣ q := Nat.minFac_dvd q
  have hQ : Nat.nth Nat.Prime (n + 1) ≤ Nat.minFac q := hnext _ hmf (hbig _ hmf hmfd)
  have hsq : Nat.minFac q ^ 2 ≤ q := Nat.minFac_sq_le_self (by omega) hnp
  have : Nat.nth Nat.Prime (n + 1) ^ 2 ≤ Nat.minFac q ^ 2 := Nat.pow_le_pow_left hQ 2
  omega
