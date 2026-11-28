import OMAStatements.S_oeis_a071256

-- Reduction oeis-a071256.R1
-- Credit: @Pixelstorm44

namespace OMA.R_oeis_a071256_R1

open Filter
open OMA.S_oeis_a071256

private theorem six_dvd_center {m : ℕ} (hm : 5 ≤ m)
    (hl : (m - 1).Prime) (hr : (m + 1).Prime) : 6 ∣ m := by
  have h₂ : ¬ 2 ∣ m - 1 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hl).mp h
    omega
  have h₃ : ¬ 3 ∣ m - 1 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).mp h
    omega
  have h₃' : ¬ 3 ∣ m + 1 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp h
    omega
  have hdiv : 3 ∣ m := by
    by_cases h : m % 3 = 1
    · exact (h₃ ⟨m / 3, by omega⟩).elim
    by_cases h' : m % 3 = 2
    · exact (h₃' ⟨m / 3 + 1, by omega⟩).elim
    exact ⟨m / 3, by omega⟩
  exact (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd (by omega) hdiv

private theorem a_eq_inf {r : ℕ} (hr : 5 ≤ r) :
    a r = sInf {m | 0 < m ∧ r.lcm 6 ∣ m ∧ (m - 1).Prime ∧ (m + 1).Prime} := by
  unfold a
  congr 1
  ext m
  change (1 ≤ m ∧ r ∣ m ∧ _ ∧ _) ↔ (0 < m ∧ r.lcm 6 ∣ m ∧ (m - 1).Prime ∧ (m + 1).Prime)
  constructor
  · rintro ⟨hm, hd, hl, hu⟩
    exact ⟨hm, Nat.lcm_dvd hd (six_dvd_center (hr.trans (Nat.le_of_dvd hm hd)) hl hu), hl, hu⟩
  · rintro ⟨hm, hd, hl, hu⟩
    exact ⟨hm, (Nat.dvd_lcm_left r 6).trans hd, hl, hu⟩

private theorem drop_factor {p s : ℕ} (hp : p ∣ 6) (hc : p.Coprime s) :
    (p * s).lcm 6 = s.lcm 6 := by
  apply Nat.dvd_antisymm
  · exact Nat.lcm_dvd (hc.mul_dvd_of_dvd_of_dvd (hp.trans (Nat.dvd_lcm_right s 6))
      (Nat.dvd_lcm_left s 6)) (Nat.dvd_lcm_right s 6)
  · exact Nat.lcm_dvd ((dvd_mul_left s p).trans (Nat.dvd_lcm_left _ _))
      (Nat.dvd_lcm_right _ _)

/-- The smallest modulus in an lcm class is reduced and at least n/6.
Once this modulus exceeds 4, every class member has the same first center. -/
theorem representative {n : ℕ} (hn : 30 ≤ n) :
    ∃ r, ((2 ∣ r → 4 ∣ r) ∧ (3 ∣ r → 9 ∣ r)) ∧ r ≤ n ∧ n ≤ 6 * r ∧ 5 ≤ r ∧ a r = a n := by
  classical
  let h : ∃ r : ℕ, r.lcm 6 = n.lcm 6 := ⟨n, rfl⟩
  let r := Nat.find h
  have he : r.lcm 6 = n.lcm 6 := Nat.find_spec h
  have hmin : ∀ s : ℕ, s.lcm 6 = n.lcm 6 → r ≤ s := fun _ hs => Nat.find_min' h hs
  have hsmall : r ≤ n := hmin n rfl
  have hlarge : n ≤ 6 * r := by
    have hpos : r ≠ 0 := by
      rintro hz
      have hp := Nat.lcm_pos (show 0 < n by omega) (show 0 < 6 by decide)
      simp [hz] at he
      omega
    apply Nat.le_of_dvd (by omega)
    have hd := Nat.dvd_lcm_left n 6
    rw [← he] at hd
    exact hd.trans (Nat.lcm_dvd (dvd_mul_left _ _) (dvd_mul_right _ _))
  have hr : 5 ≤ r := by omega
  have reduced : ((2 ∣ r → 4 ∣ r) ∧ (3 ∣ r → 9 ∣ r)) := by
    constructor
    · rintro ⟨s, hs⟩
      by_contra bad
      have hc := Nat.prime_two.coprime_iff_not_dvd.mpr (show ¬ 2 ∣ s by omega)
      have hdrop := drop_factor (show 2 ∣ 6 by decide) hc
      have := hmin s (hdrop.symm.trans (hs ▸ he))
      omega
    · rintro ⟨s, hs⟩
      by_contra bad
      have hc := Nat.prime_three.coprime_iff_not_dvd.mpr (show ¬ 3 ∣ s by omega)
      have hdrop := drop_factor (show 3 ∣ 6 by decide) hc
      have := hmin s (hdrop.symm.trans (hs ▸ he))
      omega
  refine ⟨r, reduced, hsmall, hlarge, hr, ?_⟩
  rw [a_eq_inf hr, a_eq_inf (show 5 ≤ n by omega)]
  simp only [he]

private theorem ratio_nonneg (n : ℕ) : 0 ≤ ((a n : ℝ) / n ^ 2) := by positivity

private theorem ratio_mono_rep {n r : ℕ} (hr : 5 ≤ r) (hle : r ≤ n) (ha : a r = a n) :
    ((a n : ℝ) / n ^ 2) ≤ ((a r : ℝ) / r ^ 2) := by
  have h : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  rw [← ha]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)

private theorem hit_min {r : ℕ} (hr : 5 ≤ r)
    (hex : ∃ m, 0 < m ∧ r.lcm 6 ∣ m ∧ (m - 1).Prime ∧ (m + 1).Prime) :
    0 < a r ∧ r.lcm 6 ∣ a r ∧ (a r - 1).Prime ∧ (a r + 1).Prime := by
  rw [a_eq_inf hr]
  exact csInf_mem (s := {m | (0 < m ∧ r.lcm 6 ∣ m ∧ (m - 1).Prime ∧ (m + 1).Prime)}) hex

private theorem no_hit {r : ℕ} (hr : 5 ≤ r)
    (h : ¬ ∃ m, 0 < m ∧ r.lcm 6 ∣ m ∧ (m - 1).Prime ∧ (m + 1).Prime) : a r = 0 := by
  have hempty : {m | (0 < m ∧ r.lcm 6 ∣ m ∧ (m - 1).Prime ∧ (m + 1).Prime)} = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr (fun m hm => h ⟨m, hm⟩)
  rw [a_eq_inf hr, hempty]
  exact Nat.sInf_empty

/-- At arbitrarily large indices either the progression is empty, or one can
use a center itself as the new index. Both give a(n) ≤ n. -/
theorem frequently_small : ∃ᶠ n : ℕ in atTop, a n ≤ n := by
  apply frequently_atTop.mpr
  intro N
  let n := max 5 N
  have hn : 5 ≤ n := le_max_left ..
  have hN : N ≤ n := le_max_right ..
  by_cases hh : ∃ m, (0 < m ∧ n.lcm 6 ∣ m ∧ (m - 1).Prime ∧ (m + 1).Prime)
  · obtain ⟨m, hm, hd, hl, hu⟩ := hh
    have hnm := Nat.le_of_dvd hm ((Nat.dvd_lcm_left n 6).trans hd)
    refine ⟨m, hN.trans hnm, ?_⟩
    exact Nat.sInf_le (s := {k : ℕ | 1 ≤ k ∧ m ∣ k ∧ (k-1).Prime ∧ (k+1).Prime})
      ⟨hm, dvd_rfl, hl, hu⟩
  · exact ⟨n, hN, by rw [no_hit hn hh]; omega⟩

/-- The lower limit is zero regardless of the infinitude of twin primes. -/
theorem liminf_eq_zero : liminf (fun n : ℕ => (a n : ℝ) / n ^ 2) atTop = 0 := by
  have hsmall : ∃ᶠ n : ℕ in atTop, ((a n : ℝ) / n ^ 2) ≤ 1 / (n : ℝ) := by
    apply frequently_small.mono
    intro n hn
    calc
      _ ≤ (n : ℝ) / n ^ 2 := by gcongr
      _ = _ := by by_cases h : (n : ℝ) = 0 <;> simp [h, sq]
  have hfreq (ε : ℝ) (hε : 0 < ε) : ∃ᶠ n : ℕ in atTop, ((a n : ℝ) / n ^ 2) < ε := by
    have hev := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hε
    exact (hsmall.and_eventually hev).mono fun _ h => h.1.trans_lt h.2
  have hc : IsCoboundedUnder (· ≥ ·) atTop (fun n : ℕ => (a n : ℝ) / n ^ 2) :=
    IsCoboundedUnder.of_frequently_le ((hfreq 1 zero_lt_one).mono fun _ h => h.le)
  have hn := Eventually.of_forall ratio_nonneg (f := atTop)
  exact le_antisymm ((liminf_le_iff hc ⟨0, hn⟩).mpr hfreq) (le_liminf_of_le hc hn)

/-- A partial result on the initial gap in H2. For any prescribed number of
multipliers, arbitrarily large reduced moduli miss all of them. -/
theorem factorial_gaps (K N : ℕ) : ∃ r ≥ N, ((2 ∣ r → 4 ∣ r) ∧ (3 ∣ r → 9 ∣ r)) ∧
    ∀ k, 1 ≤ k → k ≤ K → ¬ (r * k + 1).Prime := by
  let b := (N + 1) * (K + 1).factorial
  let r := 6 * b + 1
  have hb : N + 1 ≤ b := Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
  have hr : 2 ≤ r := by dsimp [r]; omega
  refine ⟨r, by dsimp [r]; omega, ?_, ?_⟩
  · dsimp [r]
    constructor <;> omega
  · intro k hk hK
    obtain ⟨q, hq⟩ := Nat.dvd_factorial (Nat.succ_pos k) (Nat.succ_le_succ hK)
    apply Nat.not_prime_of_dvd_of_lt (m := k + 1)
    · refine ⟨6 * (N + 1) * q * k + 1, ?_⟩
      dsimp [r, b]
      rw [hq, Nat.succ_eq_add_one]
      ring
    · omega
    · have hlt := Nat.mul_lt_mul_of_pos_right (show 1 < r by omega) hk
      simpa using Nat.succ_lt_succ hlt

/-- A nonempty progression for a large reduced modulus has an early hit. -/
def H1 : Prop := ∃ U : ℝ, 0 < U ∧ U < 1 ∧ ∃ N : ℕ, ∀ r ≥ N,
  let centers := {m : ℕ | 0 < m ∧ r.lcm 6 ∣ m ∧ (m - 1).Prime ∧ (m + 1).Prime}
  ((2 ∣ r → 4 ∣ r) ∧ (3 ∣ r → 9 ∣ r)) → centers.Nonempty →
    ∃ m ∈ centers, (m : ℝ) ≤ U * r ^ 2

/-- Arbitrarily large reduced moduli have a hit but a long initial gap. -/
def H2 : Prop := ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ r ≥ N,
  let centers := {m : ℕ | 0 < m ∧ r.lcm 6 ∣ m ∧ (m - 1).Prime ∧ (m + 1).Prime}
  ((2 ∣ r → 4 ∣ r) ∧ (3 ∣ r → 9 ∣ r)) ∧ centers.Nonempty ∧
    ∀ m ∈ centers, δ * r ^ 2 ≤ (m : ℝ)

/-- Both prime-progression hypotheses are also necessary. In particular
the nonempty clause in the gap condition accounts for sInf of the empty set. -/
theorem necessary (h : type_of% @OMA.S_oeis_a071256.main) : H1 ∧ H2 := by
  obtain ⟨bdd, C, hC, hC1, he⟩ := h
  constructor
  · obtain ⟨U, hCU, hU⟩ := exists_between hC1
    obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt (he.trans_lt hCU) bdd)
    refine ⟨U, hC.trans hCU, hU, max 5 N, fun r hr _ hh => ?_⟩
    have hr' : 5 ≤ r := le_trans (le_max_left ..) hr
    have hp : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
    exact ⟨a r, hit_min hr' hh, (div_le_iff₀ (sq_pos_of_pos hp)).mp
      (hN r (le_trans (le_max_right ..) hr)).le⟩
  · obtain ⟨δ, hδ, hδC⟩ := exists_between hC
    have hf := frequently_lt_of_lt_limsup (isCoboundedUnder_le_of_le atTop ratio_nonneg)
      (hδC.trans_eq he.symm)
    refine ⟨δ, hδ, fun N => ?_⟩
    obtain ⟨n, hn, hv⟩ := frequently_atTop.mp hf (max 30 (6 * N))
    obtain ⟨r, hred, hle, hlarge, hr, ha⟩ := representative (le_trans (le_max_left ..) hn)
    have hval := hv.trans_le (ratio_mono_rep hr hle ha)
    have hp : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
    refine ⟨r, by omega, hred, ?_, fun m hm => ?_⟩
    · by_contra hh
      simp [no_hit hr hh] at hval
      linarith
    · have hmin : a r ≤ m := by
        rw [a_eq_inf hr]
        exact Nat.sInf_le hm
      exact ((le_div_iff₀ (sq_pos_of_pos hp)).mp hval.le).trans (Nat.cast_le.mpr hmin)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a071256.main := by
  rintro ⟨U, hU, hU1, N, hupper⟩ ⟨δ, hδ, hlower⟩
  have hub : ∀ᶠ n : ℕ in atTop, ((a n : ℝ) / n ^ 2) ≤ U := by
    apply eventually_atTop.mpr
    refine ⟨max 30 (6 * N), fun n hn => ?_⟩
    obtain ⟨r, hred, hle, hlarge, hr, ha⟩ := representative (le_trans (le_max_left ..) hn)
    apply (ratio_mono_rep hr hle ha).trans
    by_cases hh : ∃ m, (0 < m ∧ r.lcm 6 ∣ m ∧ (m - 1).Prime ∧ (m + 1).Prime)
    · obtain ⟨m, hm, hbound⟩ := hupper r (by omega) hred hh
      have hmin : a r ≤ m := by
        rw [a_eq_inf hr]
        exact Nat.sInf_le hm
      have hpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
      exact (div_le_iff₀ (sq_pos_of_pos hpos)).mpr ((Nat.cast_le.mpr hmin).trans hbound)
    · simpa [no_hit hr hh] using hU.le
  have hfreq : ∃ᶠ r : ℕ in atTop, δ ≤ ((a r : ℝ) / r ^ 2) := by
    apply frequently_atTop.mpr
    intro N
    obtain ⟨r, hr, _, hex, hall⟩ := hlower (max 5 N)
    have hr' : 5 ≤ r := le_trans (le_max_left ..) hr
    have hpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
    exact ⟨r, le_trans (le_max_right ..) hr, (le_div_iff₀ (sq_pos_of_pos hpos)).mpr
      (hall _ (hit_min hr' hex))⟩
  have bdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (a n : ℝ) / n ^ 2) := ⟨U, hub⟩
  exact ⟨bdd, limsup (fun n : ℕ => (a n : ℝ) / n ^ 2) atTop, hδ.trans_le (le_limsup_of_frequently_le hfreq bdd),
    (limsup_le_of_le (isCoboundedUnder_le_of_le atTop ratio_nonneg) hub).trans_lt hU1, rfl⟩

end OMA.R_oeis_a071256_R1
