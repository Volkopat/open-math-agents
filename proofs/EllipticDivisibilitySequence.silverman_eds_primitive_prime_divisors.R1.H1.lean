import OMAReductions.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1

/-!
# Ward's local p-adic valuation law for nonsingular elliptic divisibility sequences

We prove `EllipticDivisibilitySequence.silverman_eds_primitive_prime_divisors.R1.H1` directly
by elementary arithmetic on the Ward recurrence modulo `p ^ (2 * e)`.

For any prime `p` not dividing `2 * 3 * W 2 * W 3`:
1. `ward_rank_local` gives the rank of apparition `r ≥ 2` with `p ∣ |W n| ↔ r ∣ n`.
2. `eds_sum_identity` proves the exact Ward invariant identity
   `W 2 * W 3 * (W (n+2) * W (n-1)^2 + W (n-2) * W (n+1)^2 + W 2^2 * W n^3)`
   `= (W 4 + W 2^5) * W (n-1) * W n * W (n+1)` for all `n ≥ 2`.
3. Whenever `p ∣ |W n|` with valuation `e ≥ 1`, setting `u k = W (k * n) / W n` and
   `q = - W (n + 1) * W (n - 1)`, the invariant identity yields `u 2 ^ 2 ≡ 4 * q ^ 3 [MOD p ^ (2 * e)]`,
   providing a unit `c` in `ZMod (p ^ (2 * e))` with `c ^ 2 = q` and `u 2 = 2 * c ^ 3`.
4. The neighbor recurrences give `W (k * n + 1) * W (k * n - 1) ≡ - q ^ (k ^ 2) [MOD p ^ (2 * e)]`.
5. Strong induction on `k ≥ 1`, using the step-1 Ward recurrence when `p ∤ (k - 2)` and the
   step-2 Ward recurrence when `p ∣ (k - 2)` (hence `p ∤ (k - 4)` as `p ≥ 5`), proves
   `u k ≡ c ^ (k ^ 2 - 1) * k [MOD p ^ (2 * e)]` for all `k ≥ 1`.
6. Since `2 * e ≥ 2`, this immediately gives `v_p(W (n * k)) = v_p(W n)` for `p.Coprime k`
   and `v_p(W (n * p)) = v_p(W n) + 1`, from which `v_p(W (r * k)) = v_p(W r) + v_p(k)` follows.
-/

namespace OMA.EDSR1H1

open EllipticDivisibilitySequence

private def tri (k : ℕ) : ℕ := k * (k - 1) / 2

private lemma two_mul_tri (k : ℕ) : 2 * tri k = k * (k - 1) := by
  dsimp [tri]
  have hev : Even (k * (k - 1)) := Nat.even_mul_pred_self k
  rcases hev with ⟨m, hm⟩
  omega

private lemma tri_zero : tri 0 = 0 := rfl

private lemma tri_one : tri 1 = 0 := rfl

private lemma tri_step {k : ℕ} (hk : 1 ≤ k) : tri (k + 1) + tri (k - 1) = 2 * tri k + 1 := by
  have h1 := two_mul_tri (k + 1)
  have h2 := two_mul_tri (k - 1)
  have h3 := two_mul_tri k
  have hz : (k + 1) * k + (k - 1) * (k - 2) = 2 * (k * (k - 1)) + 2 := by
    rcases k with _ | _ | t
    · omega
    · decide
    · have hsub1 : t + 1 + 1 - 1 = t + 1 := by omega
      have hsub2 : t + 1 + 1 - 2 = t := by omega
      rw [hsub1, hsub2]
      ring
  have h1' : 2 * tri (k + 1) = (k + 1) * k := by simpa using h1
  have h2' : 2 * tri (k - 1) = (k - 1) * (k - 2) := by
    simpa [Nat.sub_sub] using h2
  omega

private lemma add_two_mul_tri (k : ℕ) : k + 2 * tri k = k ^ 2 := by
  rw [two_mul_tri]
  cases k with
  | zero => simp
  | succ m =>
    simp only [Nat.add_sub_cancel]
    ring

private lemma nat_dvd_sub_of_dvd {a b c : ℕ} (hab : a ∣ b) (hac : a ∣ c) : a ∣ b - c := by
  rcases hab with ⟨x, rfl⟩
  rcases hac with ⟨y, rfl⟩
  exact ⟨x - y, by rw [Nat.mul_sub_left_distrib]⟩

private lemma exp_step2_A {k : ℕ} (hk : 5 ≤ k) :
    ((k - 1) ^ 2 - 1) + ((k - 3) ^ 2 - 1) + 2 * (2 ^ 2 - 1) =
      (k ^ 2 - 1) + ((k - 4) ^ 2 - 1) := by
  rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
  have h1 : 5 + t - 1 = t + 4 := by omega
  have h3 : 5 + t - 3 = t + 2 := by omega
  have h4 : 5 + t - 4 = t + 1 := by omega
  rw [h1, h3, h4]
  have hs1 : (t + 4) ^ 2 = (t ^ 2 + 8 * t + 15) + 1 := by ring
  have hs3 : (t + 2) ^ 2 = (t ^ 2 + 4 * t + 3) + 1 := by ring
  have hs0 : (5 + t) ^ 2 = (t ^ 2 + 10 * t + 24) + 1 := by ring
  have hs4 : (t + 1) ^ 2 = (t ^ 2 + 2 * t) + 1 := by ring
  rw [hs1, hs3, hs0, hs4]
  omega

private lemma exp_step2_B {k : ℕ} (hk : 5 ≤ k) :
    (3 ^ 2 - 1) + 2 * ((k - 2) ^ 2 - 1) = (k ^ 2 - 1) + ((k - 4) ^ 2 - 1) := by
  rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
  have h2 : 5 + t - 2 = t + 3 := by omega
  have h4 : 5 + t - 4 = t + 1 := by omega
  rw [h2, h4]
  have hs2 : (t + 3) ^ 2 = (t ^ 2 + 6 * t + 8) + 1 := by ring
  have hs0 : (5 + t) ^ 2 = (t ^ 2 + 10 * t + 24) + 1 := by ring
  have hs4 : (t + 1) ^ 2 = (t ^ 2 + 2 * t) + 1 := by ring
  rw [hs2, hs0, hs4]
  omega

private lemma exp_step1_A {k : ℕ} (hk : 5 ≤ k) :
    2 * (k - 1) ^ 2 = (k ^ 2 - 1) + ((k - 2) ^ 2 - 1) := by
  rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
  have h1 : 5 + t - 1 = t + 4 := by omega
  have h2 : 5 + t - 2 = t + 3 := by omega
  rw [h1, h2]
  have hs1 : 2 * (t + 4) ^ 2 = 2 * t ^ 2 + 16 * t + 32 := by ring
  have hs0 : (5 + t) ^ 2 = (t ^ 2 + 10 * t + 24) + 1 := by ring
  have hs2 : (t + 3) ^ 2 = (t ^ 2 + 6 * t + 8) + 1 := by ring
  rw [hs1, hs0, hs2]
  omega

private lemma exp_step1_B {k : ℕ} (hk : 5 ≤ k) :
    2 + 2 * ((k - 1) ^ 2 - 1) = (k ^ 2 - 1) + ((k - 2) ^ 2 - 1) := by
  rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
  have h1 : 5 + t - 1 = t + 4 := by omega
  have h2 : 5 + t - 2 = t + 3 := by omega
  rw [h1, h2]
  have hs1 : (t + 4) ^ 2 = (t ^ 2 + 8 * t + 15) + 1 := by ring
  have hs0 : (5 + t) ^ 2 = (t ^ 2 + 10 * t + 24) + 1 := by ring
  have hs2 : (t + 3) ^ 2 = (t ^ 2 + 6 * t + 8) + 1 := by ring
  rw [hs1, hs0, hs2]
  omega

private lemma isUnit_intCast_zmod_pow {p m : ℕ} (hp : p.Prime) {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) : IsUnit (x : ZMod (p ^ m)) := by
  have hnd : ¬ p ∣ x.natAbs := fun h => hx (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h))
  have hcop : Nat.Coprime x.natAbs p := (hp.coprime_iff_not_dvd.mpr hnd).symm
  have hcopm : Nat.Coprime x.natAbs (p ^ m) := hcop.pow_right m
  have hic : IsCoprime x ((p ^ m : ℕ) : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using hcopm
  rcases hic with ⟨a, b, hab⟩
  have hcast := congrArg (fun t : ℤ => (t : ZMod (p ^ m))) hab
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one,
    ZMod.natCast_self, mul_zero, add_zero] at hcast
  exact isUnit_iff_exists_inv.mpr ⟨(a : ZMod (p ^ m)), by rw [mul_comm]; exact hcast⟩

private lemma isUnit_natCast_zmod_pow {p m : ℕ} (a : ℕ) (hp : p.Prime) (ha : ¬ p ∣ a) :
    IsUnit (a : ZMod (p ^ m)) := by
  have h : ¬ (p : ℤ) ∣ (a : ℤ) := fun hd => ha (Int.natCast_dvd_natCast.mp hd)
  simpa using isUnit_intCast_zmod_pow (m := m) hp h

private lemma w_zero_and_neg {W : ℤ → ℤ} (hW : IsNonsingularEDS W) :
    W 0 = 0 ∧ ∀ m : ℤ, W (-m) = -W m := by
  rcases hW with ⟨_, _, E, x, y, _, _, heval⟩
  constructor
  · have h0 : (W 0 : ℚ) = 0 := by
      rw [heval 0, WeierstrassCurve.ψ_zero, Polynomial.evalEval_zero]
    exact_mod_cast h0
  · intro m
    have hm : (W (-m) : ℚ) = -(W m : ℚ) := by
      rw [heval (-m), WeierstrassCurve.ψ_neg, Polynomial.evalEval_neg, ← heval m]
    exact_mod_cast hm

private lemma ward_rel3 {W : ℤ → ℤ} (hw : IsEllipticDvdSequence W) (a b c : ℤ) :
    W (a + b) * W (a - b) * W c ^ 2 =
      W (a + c) * W (a - c) * W b ^ 2 - W (b + c) * W (b - c) * W a ^ 2 := by
  have h := hw.1 a b c
  simp only [IsEllipticNet.rel, add_zero] at h
  linear_combination h

private lemma ward_rel1 {W : ℤ → ℤ} (hw : IsEllipticDvdSequence W) (h1 : W 1 = 1) (a b : ℤ) :
    W (a + b) * W (a - b) =
      W (a + 1) * W (a - 1) * W b ^ 2 - W (b + 1) * W (b - 1) * W a ^ 2 := by
  have h := ward_rel3 hw a b 1
  rw [h1, one_pow, mul_one] at h
  exact h

/-- Exact Ward invariant identity for all `n ≥ 2`. -/
private lemma eds_sum_identity {W : ℤ → ℤ} (hw : IsEllipticDvdSequence W)
    (h0 : W 0 = 0) (h1 : W 1 = 1) (hnz : ∀ i : ℤ, i ≠ 0 → W i ≠ 0) :
    ∀ n : ℕ, 2 ≤ n →
      W 2 * W 3 * (W ((n : ℤ) + 2) * W ((n : ℤ) - 1) ^ 2 +
        W ((n : ℤ) - 2) * W ((n : ℤ) + 1) ^ 2 + W 2 ^ 2 * W (n : ℤ) ^ 3) =
      (W 4 + W 2 ^ 5) * W ((n : ℤ) - 1) * W (n : ℤ) * W ((n : ℤ) + 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    norm_num [h0, h1]
    ring
  | succ n hn ih =>
    let N : ℤ → ℤ := fun m =>
      W (m + 2) * W (m - 1) ^ 2 + W (m - 2) * W (m + 1) ^ 2 + W 2 ^ 2 * W m ^ 3
    have hrel_hi : W ((n : ℤ) + 3) * W ((n : ℤ) - 1) =
        W ((n : ℤ) + 2) * W (n : ℤ) * W 2 ^ 2 - W 3 * W ((n : ℤ) + 1) ^ 2 := by
      have h := ward_rel1 hw h1 ((n : ℤ) + 1) 2
      have h_a1 : (n : ℤ) + 1 + 2 = (n : ℤ) + 3 := by ring
      have h_a2 : (n : ℤ) + 1 - 2 = (n : ℤ) - 1 := by ring
      have h_a3 : (n : ℤ) + 1 + 1 = (n : ℤ) + 2 := by ring
      have h_a4 : (n : ℤ) + 1 - 1 = (n : ℤ) := by ring
      rw [h_a1, h_a2, h_a3, h_a4] at h
      simpa [show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num, h1] using h
    have hrel_lo : W ((n : ℤ) + 2) * W ((n : ℤ) - 2) =
        W ((n : ℤ) + 1) * W ((n : ℤ) - 1) * W 2 ^ 2 - W 3 * W (n : ℤ) ^ 2 := by
      have h := ward_rel1 hw h1 (n : ℤ) 2
      simpa [show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num, h1] using h
    have hstep : W ((n : ℤ) - 1) * N ((n : ℤ) + 1) = W ((n : ℤ) + 2) * N (n : ℤ) := by
      dsimp only [N]
      have h1' : (n : ℤ) + 1 + 2 = (n : ℤ) + 3 := by ring
      have h2' : (n : ℤ) + 1 - 1 = (n : ℤ) := by ring
      have h3' : (n : ℤ) + 1 - 2 = (n : ℤ) - 1 := by ring
      have h4' : (n : ℤ) + 1 + 1 = (n : ℤ) + 2 := by ring
      rw [h1', h2', h3', h4']
      linear_combination W (n : ℤ) ^ 2 * hrel_hi - W ((n : ℤ) + 1) ^ 2 * hrel_lo
    have hwn1 : W ((n : ℤ) - 1) ≠ 0 := hnz ((n : ℤ) - 1) (by omega)
    have hmul : W ((n : ℤ) - 1) * (W 2 * W 3 * N ((n : ℤ) + 1)) =
        W ((n : ℤ) - 1) * ((W 4 + W 2 ^ 5) * W (n : ℤ) * W ((n : ℤ) + 1) * W ((n : ℤ) + 2)) := by
      calc W ((n : ℤ) - 1) * (W 2 * W 3 * N ((n : ℤ) + 1))
          = W 2 * W 3 * (W ((n : ℤ) - 1) * N ((n : ℤ) + 1)) := by ring
        _ = W ((n : ℤ) + 2) * (W 2 * W 3 * N (n : ℤ)) := by rw [hstep]; ring
        _ = W ((n : ℤ) + 2) * ((W 4 + W 2 ^ 5) * W ((n : ℤ) - 1) * W (n : ℤ) * W ((n : ℤ) + 1)) := by
            rw [ih]
        _ = W ((n : ℤ) - 1) * ((W 4 + W 2 ^ 5) * W (n : ℤ) * W ((n : ℤ) + 1) * W ((n : ℤ) + 2)) := by
            ring
    have hres := mul_left_cancel₀ hwn1 hmul
    have hcast : ((↑(n + 1) : ℤ)) = (n : ℤ) + 1 := by push_cast; ring
    rw [hcast]
    have h1' : (n : ℤ) + 1 + 2 = (n : ℤ) + 3 := by ring
    have h2' : (n : ℤ) + 1 - 1 = (n : ℤ) := by ring
    have h3' : (n : ℤ) + 1 - 2 = (n : ℤ) - 1 := by ring
    have h4' : (n : ℤ) + 1 + 1 = (n : ℤ) + 2 := by ring
    simpa only [N, h1', h2', h3', h4'] using hres

/-- Rank of apparition modulo a prime `p ∤ W 3`. -/
private lemma ward_rank_local {W : ℤ → ℤ} (hw : IsEllipticDvdSequence W) (h1 : W 1 = 1)
    {p : ℕ} (hp : p.Prime) (h3 : ¬ p ∣ (W 3).natAbs)
    (ex : ∃ n : ℕ, 0 < n ∧ p ∣ (W n).natAbs) :
    ∃ r : ℕ, 2 ≤ r ∧ ∀ n : ℕ, 0 < n → (p ∣ (W n).natAbs ↔ r ∣ n) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let z : ℤ → ZMod p := fun i => (W i : ZMod p)
  have hzero (i : ℤ) : z i = 0 ↔ p ∣ (W i).natAbs := by
    change ((W i : ℤ) : ZMod p) = 0 ↔ _
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  have hz1 : z 1 = 1 := by simp [z, h1]
  have hz3 : z 3 ≠ 0 := fun e => h3 ((hzero 3).mp e)
  have hward (a b : ℤ) : z (a + b) * z (a - b) =
      z (a + 1) * z (a - 1) * z b ^ 2 - z (b + 1) * z (b - 1) * z a ^ 2 := by
    have h := ward_rel1 hw h1 a b
    simpa only [z, Int.cast_mul, Int.cast_sub, Int.cast_pow] using
      congrArg (fun t : ℤ => (t : ZMod p)) h
  let r := Nat.find ex
  have hfound : 0 < r ∧ p ∣ (W r).natAbs := Nat.find_spec ex
  have hzr : z (r : ℤ) = 0 := (hzero _).mpr hfound.2
  have hr2 : 2 ≤ r := by
    by_contra hlt
    have hr1 : r = 1 := by omega
    rw [hr1] at hzr
    exact one_ne_zero (hz1.symm.trans hzr)
  have hlt_nz (j : ℕ) (hj : 0 < j) (hjr : j < r) : z (j : ℤ) ≠ 0 := fun e =>
    Nat.find_min ex hjr ⟨hj, (hzero _).mp e⟩
  have hzm : z ((r : ℤ) - 1) ≠ 0 := by
    have hcast : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
    rw [← hcast]
    exact hlt_nz (r - 1) (by omega) (by omega)
  have hzp : z ((r : ℤ) + 1) ≠ 0 := by
    intro h0
    have h := hward ((r : ℤ) - 1) 2
    have h1' : (r : ℤ) - 1 + 2 = (r : ℤ) + 1 := by ring
    have h2' : (r : ℤ) - 1 + 1 = (r : ℤ) := by ring
    rw [h1', h2', h0, hzr] at h
    norm_num [show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num, hz1] at h
    rcases h with h3' | hm'
    · exact hz3 h3'
    · exact hzm hm'
  have hadv (a : ℤ) (ha : z a ≠ 0) : z (a + (r : ℤ)) ≠ 0 := by
    intro h0
    have h := hward a (r : ℤ)
    rw [h0, hzr, zero_mul, zero_pow two_ne_zero, mul_zero, zero_sub] at h
    have hprod : z ((r : ℤ) + 1) * z ((r : ℤ) - 1) * z a ^ 2 = 0 := neg_eq_zero.mp h.symm
    exact mul_ne_zero (mul_ne_zero hzp hzm) (pow_ne_zero 2 ha) hprod
  have hprog (j : ℕ) (hj : 0 < j) (hjr : j < r) (k : ℕ) : z ((k * r + j : ℕ) : ℤ) ≠ 0 := by
    induction k with
    | zero => simpa using hlt_nz j hj hjr
    | succ k ih =>
      have hidx : ((k + 1) * r + j : ℕ) = (k * r + j) + r := by ring
      rw [hidx, Nat.cast_add]
      exact hadv _ ih
  refine ⟨r, hr2, fun n hn => ⟨fun hpn => ?_, fun hrn => ?_⟩⟩
  · by_contra hnd
    have hrem_pos : 0 < n % r := Nat.pos_of_ne_zero (fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0))
    have hrem_lt : n % r < r := Nat.mod_lt n (by omega)
    have hbad := hprog (n % r) hrem_pos hrem_lt (n / r)
    have hdiv : n / r * r + n % r = n := by rw [mul_comm, Nat.div_add_mod]
    rw [hdiv] at hbad
    exact hbad ((hzero _).mpr hpn)
  · have hZ : (r : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hrn
    have hW := hw.2 _ _ hZ
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs] at hfound ⊢
    exact dvd_trans hfound.2 hW

/-- Neighbor product formula `W (k * n + 1) * W (k * n - 1) = - qZ ^ (k ^ 2)` in `ZMod M`. -/
private lemma neighbor_product_mod {W : ℤ → ℤ} (hw : IsEllipticDvdSequence W)
    (h1 : W 1 = 1) (hneg : ∀ m : ℤ, W (-m) = -W m)
    {n M : ℕ} (hM_dvd_wn2 : (M : ℤ) ∣ W (n : ℤ) ^ 2)
    (hα_unit : IsUnit (W ((n : ℤ) + 1) : ZMod M))
    (hβ_unit : IsUnit (W ((n : ℤ) - 1) : ZMod M)) :
    ∀ k : ℕ, (W (((k * n : ℕ) : ℤ) + 1) : ZMod M) *
      (W (((k * n : ℕ) : ℤ) - 1) : ZMod M) =
      - (-(W ((n : ℤ) + 1) : ZMod M) * (W ((n : ℤ) - 1) : ZMod M)) ^ (k ^ 2) := by
  let αZ : ZMod M := (W ((n : ℤ) + 1) : ZMod M)
  let βZ : ZMod M := (W ((n : ℤ) - 1) : ZMod M)
  let qZ : ZMod M := -(αZ * βZ)
  have hq_unit : IsUnit qZ := (hα_unit.mul hβ_unit).neg
  have hM_dvd_wn3 : ∀ k : ℕ, (M : ℤ) ∣ W ((k * n : ℕ) : ℤ) * W (n : ℤ) ^ 2 := fun k =>
    dvd_mul_of_dvd_right hM_dvd_wn2 _
  have hA : ∀ k : ℕ, (W (((k * n : ℕ) : ℤ) + 1) : ZMod M) = αZ ^ k * qZ ^ (tri k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      match k with
      | 0 => simp [tri_zero, h1]
      | 1 => simp [tri_one, αZ]
      | m + 2 =>
        have hrel := ward_rel1 hw h1 ((((m + 1) * n : ℕ) : ℤ) + 1) (n : ℤ)
        have ha1 : (((m + 1) * n : ℕ) : ℤ) + 1 + (n : ℤ) = (((m + 2) * n : ℕ) : ℤ) + 1 := by
          push_cast; ring
        have ha2 : (((m + 1) * n : ℕ) : ℤ) + 1 - (n : ℤ) = (((m * n : ℕ) : ℤ)) + 1 := by
          push_cast; ring
        have ha3 : (((m + 1) * n : ℕ) : ℤ) + 1 - 1 = (((m + 1) * n : ℕ) : ℤ) := by ring
        rw [ha1, ha2, ha3] at hrel
        have hzero_term : ((W ((((m + 1) * n : ℕ) : ℤ) + 1 + 1) *
            W (((m + 1) * n : ℕ) : ℤ) * W (n : ℤ) ^ 2 : ℤ) : ZMod M) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd, mul_assoc]
          exact dvd_mul_of_dvd_right (hM_dvd_wn3 (m + 1)) _
        have hcast := congrArg (fun t : ℤ => (t : ZMod M)) hrel
        simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow] at hcast
        have hzero' : (W ((((m + 1) * n : ℕ) : ℤ) + 1 + 1) : ZMod M) *
            (W (((m + 1) * n : ℕ) : ℤ) : ZMod M) * (W (n : ℤ) : ZMod M) ^ 2 = 0 := by
          simpa only [Int.cast_mul, Int.cast_pow] using hzero_term
        rw [hzero', zero_sub] at hcast
        have hih1 := ih (m + 1) (by omega)
        have hih0 := ih m (by omega)
        rw [hih1, hih0] at hcast
        have hunit : IsUnit (αZ ^ m * qZ ^ (tri m)) := (hα_unit.pow m).mul (hq_unit.pow (tri m))
        have hts := tri_step (k := m + 1) (by omega)
        simp only [Nat.add_sub_cancel] at hts
        apply hunit.mul_right_cancel
        calc (W ((((m + 2) * n : ℕ) : ℤ) + 1) : ZMod M) * (αZ ^ m * qZ ^ (tri m))
            = - (αZ * βZ * (αZ ^ (m + 1) * qZ ^ (tri (m + 1))) ^ 2) := hcast
          _ = qZ * (αZ ^ (m + 1) * qZ ^ (tri (m + 1))) ^ 2 := by dsimp [qZ]; ring
          _ = αZ ^ (m + 2) * αZ ^ m * qZ ^ (2 * tri (m + 1) + 1) := by ring
          _ = αZ ^ (m + 2) * αZ ^ m * qZ ^ (tri (m + 2) + tri m) := by rw [← hts]
          _ = (αZ ^ (m + 2) * qZ ^ (tri (m + 2))) * (αZ ^ m * qZ ^ (tri m)) := by
              rw [pow_add]; ring
  have hB : ∀ k : ℕ, (W (((k * n : ℕ) : ℤ) - 1) : ZMod M) = - ((-βZ) ^ k * qZ ^ (tri k)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      match k with
      | 0 =>
        have hwm1 : W (-1) = -1 := by rw [hneg 1, h1]
        simp [tri_zero, hwm1]
      | 1 => simp [tri_one, βZ]
      | m + 2 =>
        have hrel := ward_rel1 hw h1 ((((m + 1) * n : ℕ) : ℤ) - 1) (n : ℤ)
        have ha1 : (((m + 1) * n : ℕ) : ℤ) - 1 + (n : ℤ) = (((m + 2) * n : ℕ) : ℤ) - 1 := by
          push_cast; ring
        have ha2 : (((m + 1) * n : ℕ) : ℤ) - 1 - (n : ℤ) = (((m * n : ℕ) : ℤ)) - 1 := by
          push_cast; ring
        have ha3 : (((m + 1) * n : ℕ) : ℤ) - 1 + 1 = (((m + 1) * n : ℕ) : ℤ) := by ring
        rw [ha1, ha2, ha3] at hrel
        have hzero_term : ((W (((m + 1) * n : ℕ) : ℤ) *
            W ((((m + 1) * n : ℕ) : ℤ) - 1 - 1) * W (n : ℤ) ^ 2 : ℤ) : ZMod M) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          have : W (((m + 1) * n : ℕ) : ℤ) * W ((((m + 1) * n : ℕ) : ℤ) - 1 - 1) * W (n : ℤ) ^ 2 =
              W ((((m + 1) * n : ℕ) : ℤ) - 1 - 1) * (W (((m + 1) * n : ℕ) : ℤ) * W (n : ℤ) ^ 2) := by
            ring
          rw [this]
          exact dvd_mul_of_dvd_right (hM_dvd_wn3 (m + 1)) _
        have hcast := congrArg (fun t : ℤ => (t : ZMod M)) hrel
        simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow] at hcast
        have hzero' : (W (((m + 1) * n : ℕ) : ℤ) : ZMod M) *
            (W ((((m + 1) * n : ℕ) : ℤ) - 1 - 1) : ZMod M) * (W (n : ℤ) : ZMod M) ^ 2 = 0 := by
          simpa only [Int.cast_mul, Int.cast_pow] using hzero_term
        rw [hzero', zero_sub] at hcast
        have hih1 := ih (m + 1) (by omega)
        have hih0 := ih m (by omega)
        rw [hih1, hih0] at hcast
        have hunit : IsUnit (- ((-βZ) ^ m * qZ ^ (tri m))) :=
          ((hβ_unit.neg.pow m).mul (hq_unit.pow (tri m))).neg
        have hts := tri_step (k := m + 1) (by omega)
        simp only [Nat.add_sub_cancel] at hts
        apply hunit.mul_right_cancel
        calc (W ((((m + 2) * n : ℕ) : ℤ) - 1) : ZMod M) * (- ((-βZ) ^ m * qZ ^ (tri m)))
            = - (αZ * βZ * (- ((-βZ) ^ (m + 1) * qZ ^ (tri (m + 1)))) ^ 2) := hcast
          _ = qZ * ((-βZ) ^ (m + 1) * qZ ^ (tri (m + 1))) ^ 2 := by dsimp [qZ]; ring
          _ = (-βZ) ^ (m + 2) * (-βZ) ^ m * qZ ^ (2 * tri (m + 1) + 1) := by ring
          _ = (-βZ) ^ (m + 2) * (-βZ) ^ m * qZ ^ (tri (m + 2) + tri m) := by rw [← hts]
          _ = (- ((-βZ) ^ (m + 2) * qZ ^ (tri (m + 2)))) * (- ((-βZ) ^ m * qZ ^ (tri m))) := by
              rw [pow_add]; ring
  intro k
  rw [hA k, hB k]
  have hq_exp : k + 2 * tri k = k ^ 2 := add_two_mul_tri k
  have hneg_q : -αZ * βZ = qZ := by dsimp [qZ]; ring
  rw [hneg_q]
  calc (αZ ^ k * qZ ^ (tri k)) * (- ((-βZ) ^ k * qZ ^ (tri k)))
      = - ((αZ * (-βZ)) ^ k * qZ ^ (2 * tri k)) := by rw [mul_pow]; ring
    _ = - (qZ ^ k * qZ ^ (2 * tri k)) := by
        have : αZ * (-βZ) = qZ := by dsimp [qZ]; ring
        rw [this]
    _ = - qZ ^ (k + 2 * tri k) := by rw [← pow_add]
    _ = - qZ ^ (k ^ 2) := by rw [hq_exp]

/-- Master congruence `(u k : ZMod (p ^ m)) = cZ ^ (k^2 - 1) * k` for all `k ≥ 1`. -/
private lemma u_zmod_formula {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (u : ℕ → ℤ) (cZ : ZMod (p ^ m))
    (hc_unit : IsUnit cZ) (h2_unit : IsUnit (2 : ZMod (p ^ m)))
    (hu1 : u 1 = 1) (hu2_val : ((u 2 : ℤ) : ZMod (p ^ m)) = cZ ^ 3 * 2)
    (hstep1 : ∀ j : ℕ, 1 ≤ j →
      ((u (j + 1) : ℤ) : ZMod (p ^ m)) * ((u (j - 1) : ℤ) : ZMod (p ^ m)) =
        - (cZ ^ 2) ^ (j ^ 2) + cZ ^ 2 * ((u j : ℤ) : ZMod (p ^ m)) ^ 2)
    (hstep2 : ∀ j : ℕ, 2 ≤ j →
      ((u (j + 2) : ℤ) : ZMod (p ^ m)) * ((u (j - 2) : ℤ) : ZMod (p ^ m)) =
        ((u (j + 1) : ℤ) : ZMod (p ^ m)) * ((u (j - 1) : ℤ) : ZMod (p ^ m)) *
          ((u 2 : ℤ) : ZMod (p ^ m)) ^ 2 -
        ((u 3 : ℤ) : ZMod (p ^ m)) * ((u j : ℤ) : ZMod (p ^ m)) ^ 2) :
    ∀ k : ℕ, 1 ≤ k → ((u k : ℤ) : ZMod (p ^ m)) = cZ ^ (k ^ 2 - 1) * (k : ZMod (p ^ m)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hk1 : k = 1
    · subst hk1; simp [hu1]
    by_cases hk2 : k = 2
    · subst hk2; simpa using hu2_val
    by_cases hk3 : k = 3
    · subst hk3
      have hs := hstep1 2 (by decide)
      rw [show (2 : ℕ) + 1 = 3 by rfl, show (2 : ℕ) - 1 = 1 by rfl,
        hu1, Int.cast_one, mul_one, hu2_val] at hs
      rw [hs]
      norm_num
      ring
    by_cases hk4 : k = 4
    · subst hk4
      have hs := hstep1 3 (by decide)
      rw [show (3 : ℕ) + 1 = 4 by rfl, show (3 : ℕ) - 1 = 2 by rfl] at hs
      have h3v := ih 3 (by omega) (by omega)
      rw [h3v, hu2_val] at hs
      have hu2_u : IsUnit (cZ ^ 3 * (2 : ZMod (p ^ m))) := (hc_unit.pow 3).mul h2_unit
      apply hu2_u.mul_right_cancel
      rw [hs]
      norm_num
      ring
    have hk5 : 5 ≤ k := by omega
    by_cases hdiv : p ∣ (k - 2)
    · -- Step-2 recurrence: `p ∤ (k - 4)` since `p ≥ 5`
      have hnd4 : ¬ p ∣ (k - 4) := by
        intro hd4
        have hsub : p ∣ (k - 2) - (k - 4) := nat_dvd_sub_of_dvd hdiv hd4
        have heq : (k - 2) - (k - 4) = 2 := by omega
        rw [heq] at hsub
        have := Nat.le_of_dvd (by decide : 0 < 2) hsub
        omega
      have hs := hstep2 (k - 2) (by omega)
      have he1' : k - 2 + 2 = k := by omega
      have he2' : k - 2 - 2 = k - 4 := by omega
      have he3' : k - 2 + 1 = k - 1 := by omega
      have he4' : k - 2 - 1 = k - 3 := by omega
      rw [he1', he2', he3', he4'] at hs
      rw [ih (k - 4) (by omega) (by omega), ih (k - 1) (by omega) (by omega),
          ih (k - 3) (by omega) (by omega), ih (k - 2) (by omega) (by omega),
          ih 2 (by omega) (by omega), ih 3 (by omega) (by omega)] at hs
      have hunit4 : IsUnit (cZ ^ ((k - 4) ^ 2 - 1) * ((k - 4 : ℕ) : ZMod (p ^ m))) :=
        (hc_unit.pow _).mul (isUnit_natCast_zmod_pow (m := m) (k - 4) hp hnd4)
      have hcast_k1 : ((k - 1 : ℕ) : ZMod (p ^ m)) = (k : ZMod (p ^ m)) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      have hcast_k2 : ((k - 2 : ℕ) : ZMod (p ^ m)) = (k : ZMod (p ^ m)) - 2 := by
        rw [Nat.cast_sub (by omega)]; simp
      have hcast_k3 : ((k - 3 : ℕ) : ZMod (p ^ m)) = (k : ZMod (p ^ m)) - 3 := by
        rw [Nat.cast_sub (by omega)]; simp
      have hcast_k4 : ((k - 4 : ℕ) : ZMod (p ^ m)) = (k : ZMod (p ^ m)) - 4 := by
        rw [Nat.cast_sub (by omega)]; simp
      have hexpA := exp_step2_A hk5
      have hexpB := exp_step2_B hk5
      apply hunit4.mul_right_cancel
      rw [hs, hcast_k1, hcast_k2, hcast_k3, hcast_k4]
      calc (cZ ^ ((k - 1) ^ 2 - 1) * ((k : ZMod (p ^ m)) - 1)) *
            (cZ ^ ((k - 3) ^ 2 - 1) * ((k : ZMod (p ^ m)) - 3)) *
            (cZ ^ (2 ^ 2 - 1) * (2 : ZMod (p ^ m))) ^ 2 -
            (cZ ^ (3 ^ 2 - 1) * (3 : ZMod (p ^ m))) *
            (cZ ^ ((k - 2) ^ 2 - 1) * ((k : ZMod (p ^ m)) - 2)) ^ 2
          = cZ ^ (((k - 1) ^ 2 - 1) + ((k - 3) ^ 2 - 1) + 2 * (2 ^ 2 - 1)) *
              (4 * ((k : ZMod (p ^ m)) - 1) * ((k : ZMod (p ^ m)) - 3)) -
            cZ ^ ((3 ^ 2 - 1) + 2 * ((k - 2) ^ 2 - 1)) *
              (3 * ((k : ZMod (p ^ m)) - 2) ^ 2) := by
              simp only [mul_pow, ← pow_mul, ← pow_add]; ring
        _ = cZ ^ ((k ^ 2 - 1) + ((k - 4) ^ 2 - 1)) *
              (4 * ((k : ZMod (p ^ m)) - 1) * ((k : ZMod (p ^ m)) - 3) -
                3 * ((k : ZMod (p ^ m)) - 2) ^ 2) := by
              rw [hexpA, hexpB]; ring
        _ = cZ ^ ((k ^ 2 - 1) + ((k - 4) ^ 2 - 1)) *
              ((k : ZMod (p ^ m)) * ((k : ZMod (p ^ m)) - 4)) := by
              ring
        _ = (cZ ^ (k ^ 2 - 1) * (k : ZMod (p ^ m))) *
              (cZ ^ ((k - 4) ^ 2 - 1) * ((k : ZMod (p ^ m)) - 4)) := by
              rw [pow_add]; ring
    · -- Step-1 recurrence: `p ∤ (k - 2)`
      have hs := hstep1 (k - 1) (by omega)
      have he1' : k - 1 + 1 = k := by omega
      have he2' : k - 1 - 1 = k - 2 := by omega
      rw [he1', he2'] at hs
      rw [ih (k - 2) (by omega) (by omega), ih (k - 1) (by omega) (by omega)] at hs
      have hunit2 : IsUnit (cZ ^ ((k - 2) ^ 2 - 1) * ((k - 2 : ℕ) : ZMod (p ^ m))) :=
        (hc_unit.pow _).mul (isUnit_natCast_zmod_pow (m := m) (k - 2) hp hdiv)
      have hcast_k1 : ((k - 1 : ℕ) : ZMod (p ^ m)) = (k : ZMod (p ^ m)) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      have hcast_k2 : ((k - 2 : ℕ) : ZMod (p ^ m)) = (k : ZMod (p ^ m)) - 2 := by
        rw [Nat.cast_sub (by omega)]; simp
      have hexp := exp_step1_A hk5
      have hexp2 := exp_step1_B hk5
      apply hunit2.mul_right_cancel
      rw [hs, hcast_k1, hcast_k2]
      calc - (cZ ^ 2) ^ ((k - 1) ^ 2) +
            cZ ^ 2 * (cZ ^ ((k - 1) ^ 2 - 1) * ((k : ZMod (p ^ m)) - 1)) ^ 2
          = - cZ ^ (2 * (k - 1) ^ 2) +
              cZ ^ (2 + 2 * ((k - 1) ^ 2 - 1)) * ((k : ZMod (p ^ m)) - 1) ^ 2 := by
              rw [← pow_mul, mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
              ring
        _ = cZ ^ ((k ^ 2 - 1) + ((k - 2) ^ 2 - 1)) * (((k : ZMod (p ^ m)) - 1) ^ 2 - 1) := by
              rw [hexp, hexp2]; ring
        _ = cZ ^ ((k ^ 2 - 1) + ((k - 2) ^ 2 - 1)) *
              ((k : ZMod (p ^ m)) * ((k : ZMod (p ^ m)) - 2)) := by
              ring
        _ = (cZ ^ (k ^ 2 - 1) * (k : ZMod (p ^ m))) *
              (cZ ^ ((k - 2) ^ 2 - 1) * ((k : ZMod (p ^ m)) - 2)) := by
              rw [pow_add]; ring

/-- Core local valuation law: for `p ∤ 2 * 3 * W 2 * W 3` and `p ∣ |W n|`,
we have `v_p(W (n * k)) = v_p(W n)` for `p.Coprime k` and `v_p(W (n * p)) = v_p(W n) + 1`. -/
private lemma valuation_lift_core {W : ℤ → ℤ} (hW : IsNonsingularEDS W)
    (hnz : ∀ i : ℤ, i ≠ 0 → W i ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h2 : ¬ p ∣ (W 2).natAbs) (h3 : ¬ p ∣ (W 3).natAbs)
    {n : ℕ} (hn : 0 < n) (hpn : p ∣ (W n).natAbs) :
    (∀ k : ℕ, 0 < k → p.Coprime k →
      (W ((n * k : ℕ) : ℤ)).natAbs.factorization p = (W (n : ℤ)).natAbs.factorization p) ∧
    (W ((n * p : ℕ) : ℤ)).natAbs.factorization p = (W (n : ℤ)).natAbs.factorization p + 1 := by
  have hw : IsEllipticDvdSequence W := hW.1
  have h1 : W 1 = 1 := hW.2.1
  obtain ⟨h0, hneg⟩ := w_zero_and_neg hW
  obtain ⟨r, hr2, hrank⟩ := ward_rank_local hw h1 hp h3 ⟨n, hn, hpn⟩
  have hrn : r ∣ n := (hrank n hn).mp hpn
  have hn2 : 2 ≤ n := le_trans hr2 (Nat.le_of_dvd hn hrn)
  have hwn_ne : W (n : ℤ) ≠ 0 := hnz (n : ℤ) (by omega)
  have hwn_abs_ne : (W (n : ℤ)).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hwn_ne
  set e : ℕ := (W (n : ℤ)).natAbs.factorization p
  have he1 : 1 ≤ e := by
    have hpos : 0 < (W (n : ℤ)).natAbs.factorization p :=
      Nat.Prime.factorization_pos_of_dvd hp hwn_abs_ne hpn
    omega
  set M : ℕ := p ^ (2 * e)
  have hpe_dvd_nat : p ^ e ∣ (W (n : ℤ)).natAbs := Nat.ordProj_dvd _ p
  have hpe_dvd : ((p : ℤ) ^ e) ∣ W (n : ℤ) := by
    have h : ((p ^ e : ℕ) : ℤ) ∣ W (n : ℤ) := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpe_dvd_nat)
    simpa using h
  have hM_dvd_wn2 : (M : ℤ) ∣ W (n : ℤ) ^ 2 := by
    rcases hpe_dvd with ⟨t, ht⟩
    refine ⟨t ^ 2, ?_⟩
    rw [ht]
    simp only [M, Nat.cast_pow]
    rw [pow_mul]
    ring
  -- `W (n + 1)` and `W (n - 1)` are not divisible by `p`
  have hnd_np1 : ¬ (p : ℤ) ∣ W ((n : ℤ) + 1) := by
    intro hd
    have hpn1 : p ∣ (W ((n + 1 : ℕ) : ℤ)).natAbs := by
      have : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      rw [this]
      exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd)
    have hr1 : r ∣ n + 1 := (hrank (n + 1) (by omega)).mp hpn1
    have h1r : r ∣ 1 := by
      have := nat_dvd_sub_of_dvd hr1 hrn
      simpa using this
    have := Nat.le_of_dvd one_pos h1r
    omega
  have hnd_nm1 : ¬ (p : ℤ) ∣ W ((n : ℤ) - 1) := by
    intro hd
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hpn1 : p ∣ (W ((n - 1 : ℕ) : ℤ)).natAbs := by
      rw [hcast]
      exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd)
    have hr1 : r ∣ n - 1 := (hrank (n - 1) (by omega)).mp hpn1
    have h1r : r ∣ 1 := by
      have := nat_dvd_sub_of_dvd hrn hr1
      have heq : n - (n - 1) = 1 := by omega
      rwa [heq] at this
    have := Nat.le_of_dvd one_pos h1r
    omega
  have hnd_w2 : ¬ (p : ℤ) ∣ W 2 := fun hd => h2 (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd))
  have hnd_w3 : ¬ (p : ℤ) ∣ W 3 := fun hd => h3 (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd))
  -- Define integer quotients `u k = W (k * n) / W n`
  let u : ℕ → ℤ := fun k => W ((k * n : ℕ) : ℤ) / W (n : ℤ)
  have hu_mul : ∀ k : ℕ, W ((k * n : ℕ) : ℤ) = W (n : ℤ) * u k := by
    intro k
    have hdvd : W (n : ℤ) ∣ W ((k * n : ℕ) : ℤ) :=
      hw.2 (n : ℤ) ((k * n : ℕ) : ℤ) ⟨(k : ℤ), by push_cast; ring⟩
    exact (Int.mul_ediv_cancel' hdvd).symm
  have hu1 : u 1 = 1 := by
    dsimp [u]
    rw [one_mul, Int.ediv_self hwn_ne]
  -- Unit elements in `ZMod M`
  let αZ : ZMod M := (W ((n : ℤ) + 1) : ZMod M)
  let βZ : ZMod M := (W ((n : ℤ) - 1) : ZMod M)
  let qZ : ZMod M := -(αZ * βZ)
  have hα_unit : IsUnit αZ := isUnit_intCast_zmod_pow (m := 2 * e) hp hnd_np1
  have hβ_unit : IsUnit βZ := isUnit_intCast_zmod_pow (m := 2 * e) hp hnd_nm1
  have hq_unit : IsUnit qZ := (hα_unit.mul hβ_unit).neg
  have h2_ndvd : ¬ p ∣ 2 := fun hd => by
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have h2_unit : IsUnit (2 : ZMod M) := by
    simpa using isUnit_natCast_zmod_pow (m := 2 * e) 2 hp h2_ndvd
  have hw2_unit : IsUnit (W 2 : ZMod M) := isUnit_intCast_zmod_pow (m := 2 * e) hp hnd_w2
  -- Prove `W 2 * u 2 = W (n + 2) * W (n - 1)^2 - W (n - 2) * W (n + 1)^2`
  have hw2_u2 : W 2 * u 2 =
      W ((n : ℤ) + 2) * W ((n : ℤ) - 1) ^ 2 - W ((n : ℤ) - 2) * W ((n : ℤ) + 1) ^ 2 := by
    have h := ward_rel1 hw h1 ((n : ℤ) + 1) ((n : ℤ) - 1)
    have hadd : (n : ℤ) + 1 + ((n : ℤ) - 1) = ((2 * n : ℕ) : ℤ) := by push_cast; ring
    have hsub : (n : ℤ) + 1 - ((n : ℤ) - 1) = 2 := by ring
    have h_a1 : (n : ℤ) + 1 + 1 = (n : ℤ) + 2 := by ring
    have h_a2 : (n : ℤ) + 1 - 1 = (n : ℤ) := by ring
    have h_b1 : (n : ℤ) - 1 + 1 = (n : ℤ) := by ring
    have h_b2 : (n : ℤ) - 1 - 1 = (n : ℤ) - 2 := by ring
    rw [hadd, hsub, h_a1, h_a2, h_b1, h_b2, hu_mul 2] at h
    apply mul_left_cancel₀ hwn_ne
    linear_combination h
  -- Prove `(u 2 : ZMod M) ^ 2 = 4 * qZ ^ 3`
  have hu2_sq : ((u 2 : ℤ) : ZMod M) ^ 2 = 4 * qZ ^ 3 := by
    have hsum_id := eds_sum_identity hw h0 h1 hnz n hn2
    have hpe_sum : ((p : ℤ) ^ e) ∣
        (W ((n : ℤ) + 2) * W ((n : ℤ) - 1) ^ 2 + W ((n : ℤ) - 2) * W ((n : ℤ) + 1) ^ 2) := by
      have hdvd_rhs : ((p : ℤ) ^ e) ∣
          W 2 * W 3 * (W ((n : ℤ) + 2) * W ((n : ℤ) - 1) ^ 2 +
            W ((n : ℤ) - 2) * W ((n : ℤ) + 1) ^ 2 + W 2 ^ 2 * W (n : ℤ) ^ 3) := by
        rw [hsum_id]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpe_dvd _) _
      have hcop23 : IsCoprime (W 2 * W 3) ((p : ℤ) ^ e) := by
        have hnd23 : ¬ (p : ℤ) ∣ W 2 * W 3 := fun hd => by
          have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
          rcases hpZ.dvd_or_dvd hd with h | h
          · exact hnd_w2 h
          · exact hnd_w3 h
        have hcop_p : Nat.Coprime (W 2 * W 3).natAbs p :=
          (hp.coprime_iff_not_dvd.mpr (fun hd =>
            hnd23 (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hd)))).symm
        rw [Int.isCoprime_iff_gcd_eq_one]
        simpa [Int.gcd] using hcop_p.pow_right e
      have hdvd_tot : ((p : ℤ) ^ e) ∣
          (W ((n : ℤ) + 2) * W ((n : ℤ) - 1) ^ 2 +
            W ((n : ℤ) - 2) * W ((n : ℤ) + 1) ^ 2 + W 2 ^ 2 * W (n : ℤ) ^ 3) :=
        hcop23.symm.dvd_of_dvd_mul_left hdvd_rhs
      have hdvd_cube : ((p : ℤ) ^ e) ∣ W 2 ^ 2 * W (n : ℤ) ^ 3 :=
        dvd_mul_of_dvd_right (dvd_pow hpe_dvd (by decide : 3 ≠ 0)) _
      exact (dvd_add_left hdvd_cube).mp hdvd_tot
    have hM_sum_sq : (M : ℤ) ∣
        (W ((n : ℤ) + 2) * W ((n : ℤ) - 1) ^ 2 + W ((n : ℤ) - 2) * W ((n : ℤ) + 1) ^ 2) ^ 2 := by
      rcases hpe_sum with ⟨t, ht⟩
      refine ⟨t ^ 2, ?_⟩
      rw [ht]
      simp only [M, Nat.cast_pow]
      rw [pow_mul]
      ring
    have hrel_n2 : W ((n : ℤ) + 2) * W ((n : ℤ) - 2) =
        W ((n : ℤ) + 1) * W ((n : ℤ) - 1) * W 2 ^ 2 - W 3 * W (n : ℤ) ^ 2 := by
      have h := ward_rel1 hw h1 (n : ℤ) 2
      simpa [show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num, h1] using h
    have hdiff_id : W 2 ^ 2 * (u 2 ^ 2 - 4 * (-(W ((n : ℤ) + 1) * W ((n : ℤ) - 1))) ^ 3) =
        (W ((n : ℤ) + 2) * W ((n : ℤ) - 1) ^ 2 + W ((n : ℤ) - 2) * W ((n : ℤ) + 1) ^ 2) ^ 2 +
        4 * W 3 * (W ((n : ℤ) + 1) * W ((n : ℤ) - 1)) ^ 2 * W (n : ℤ) ^ 2 := by
      linear_combination
        (W 2 * u 2 + (W ((n : ℤ) + 2) * W ((n : ℤ) - 1) ^ 2 - W ((n : ℤ) - 2) * W ((n : ℤ) + 1) ^ 2)) * hw2_u2 -
        4 * W ((n : ℤ) + 1) ^ 2 * W ((n : ℤ) - 1) ^ 2 * hrel_n2
    have hM_dvd_lhs : (M : ℤ) ∣
        W 2 ^ 2 * (u 2 ^ 2 - 4 * (-(W ((n : ℤ) + 1) * W ((n : ℤ) - 1))) ^ 3) := by
      rw [hdiff_id]
      exact dvd_add hM_sum_sq (dvd_mul_of_dvd_right hM_dvd_wn2 _)
    have hcast0 : ((W 2 ^ 2 * (u 2 ^ 2 - 4 * (-(W ((n : ℤ) + 1) * W ((n : ℤ) - 1))) ^ 3) : ℤ) : ZMod M) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hM_dvd_lhs
    push_cast at hcast0
    change (W 2 : ZMod M) ^ 2 * (((u 2 : ℤ) : ZMod M) ^ 2 - 4 * qZ ^ 3) = 0 at hcast0
    have hsub0 : ((u 2 : ℤ) : ZMod M) ^ 2 - 4 * qZ ^ 3 = 0 :=
      (hw2_unit.pow 2).mul_left_cancel (by rw [mul_zero]; exact hcast0)
    exact sub_eq_zero.mp hsub0
  -- Construct the unit `cZ` in `ZMod M` with `cZ^2 = qZ` and `(u 2 : ZMod M) = cZ^3 * 2`
  obtain ⟨u2q, hu2q⟩ := (h2_unit.mul hq_unit).exists_right_inv
  let cZ : ZMod M := ((u 2 : ℤ) : ZMod M) * u2q
  have hc_mul : 2 * qZ * cZ = ((u 2 : ℤ) : ZMod M) := by
    calc 2 * qZ * cZ = ((u 2 : ℤ) : ZMod M) * (2 * qZ * u2q) := by dsimp [cZ]; ring
      _ = ((u 2 : ℤ) : ZMod M) := by rw [hu2q, mul_one]
  have hc_sq : cZ ^ 2 = qZ := by
    have h4q : (2 * qZ) ^ 2 * cZ ^ 2 = (2 * qZ) ^ 2 * qZ := by
      calc (2 * qZ) ^ 2 * cZ ^ 2 = (2 * qZ * cZ) ^ 2 := by ring
        _ = ((u 2 : ℤ) : ZMod M) ^ 2 := by rw [hc_mul]
        _ = 4 * qZ ^ 3 := hu2_sq
        _ = (2 * qZ) ^ 2 * qZ := by ring
    exact ((h2_unit.mul hq_unit).pow 2).mul_left_cancel h4q
  have hc_unit : IsUnit cZ := by
    rcases hq_unit with ⟨qu, hqu⟩
    refine isUnit_iff_exists_inv.mpr ⟨cZ * (qu⁻¹ : (ZMod M)ˣ), ?_⟩
    calc cZ * (cZ * (qu⁻¹ : (ZMod M)ˣ)) = cZ ^ 2 * (qu⁻¹ : (ZMod M)ˣ) := by ring
      _ = (qu : ZMod M) * (qu⁻¹ : (ZMod M)ˣ) := by rw [hc_sq, hqu]
      _ = 1 := Units.mul_inv qu
  have hu2_val : ((u 2 : ℤ) : ZMod M) = cZ ^ 3 * 2 := by
    calc ((u 2 : ℤ) : ZMod M) = 2 * qZ * cZ := hc_mul.symm
      _ = 2 * cZ ^ 2 * cZ := by rw [hc_sq]
      _ = cZ ^ 3 * 2 := by ring
  -- Neighbor product mod `M`
  have hAB : ∀ k : ℕ, (W (((k * n : ℕ) : ℤ) + 1) : ZMod M) *
      (W (((k * n : ℕ) : ℤ) - 1) : ZMod M) = - qZ ^ (k ^ 2) := by
    intro k
    have h := neighbor_product_mod hw h1 hneg hM_dvd_wn2 hα_unit hβ_unit k
    have hneg_q : -αZ * βZ = qZ := by dsimp [qZ]; ring
    simpa only [αZ, βZ, hneg_q] using h
  -- Exact recurrences for `u` mod `M`
  have hu_step1 : ∀ m : ℕ, 1 ≤ m →
      ((u (m + 1) : ℤ) : ZMod M) * ((u (m - 1) : ℤ) : ZMod M) =
        - (cZ ^ 2) ^ (m ^ 2) + cZ ^ 2 * ((u m : ℤ) : ZMod M) ^ 2 := by
    intro m hm
    have h := ward_rel1 hw h1 ((m * n : ℕ) : ℤ) (n : ℤ)
    have h1' : ((m * n : ℕ) : ℤ) + (n : ℤ) = (((m + 1) * n : ℕ) : ℤ) := by push_cast; ring
    have h2' : ((m * n : ℕ) : ℤ) - (n : ℤ) = (((m - 1) * n : ℕ) : ℤ) := by
      have : (m - 1) * n + n = m * n := by
        cases m with
        | zero => omega
        | succ t => simp [Nat.add_mul]
      omega
    rw [h1', h2', hu_mul (m + 1), hu_mul (m - 1), hu_mul m] at h
    have hint : u (m + 1) * u (m - 1) =
        W (((m * n : ℕ) : ℤ) + 1) * W (((m * n : ℕ) : ℤ) - 1) -
        W ((n : ℤ) + 1) * W ((n : ℤ) - 1) * u m ^ 2 := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hwn_ne)
      linear_combination h
    have hcast := congrArg (fun t : ℤ => (t : ZMod M)) hint
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow] at hcast
    rw [hcast, hAB m, hc_sq]
    change - qZ ^ (m ^ 2) - αZ * βZ * ((u m : ℤ) : ZMod M) ^ 2 = _
    dsimp [qZ]
    ring
  have hu_step2 : ∀ m : ℕ, 2 ≤ m →
      ((u (m + 2) : ℤ) : ZMod M) * ((u (m - 2) : ℤ) : ZMod M) =
        ((u (m + 1) : ℤ) : ZMod M) * ((u (m - 1) : ℤ) : ZMod M) * ((u 2 : ℤ) : ZMod M) ^ 2 -
        ((u 3 : ℤ) : ZMod M) * ((u m : ℤ) : ZMod M) ^ 2 := by
    intro m hm
    have h := ward_rel3 hw ((m * n : ℕ) : ℤ) ((2 * n : ℕ) : ℤ) (n : ℤ)
    have h1' : ((m * n : ℕ) : ℤ) + ((2 * n : ℕ) : ℤ) = (((m + 2) * n : ℕ) : ℤ) := by
      push_cast; ring
    have h2' : ((m * n : ℕ) : ℤ) - ((2 * n : ℕ) : ℤ) = (((m - 2) * n : ℕ) : ℤ) := by
      have : (m - 2) * n + 2 * n = m * n := by
        have := Nat.sub_add_cancel hm
        calc (m - 2) * n + 2 * n = (m - 2 + 2) * n := by rw [Nat.add_mul]
          _ = m * n := by rw [this]
      omega
    have h3' : ((m * n : ℕ) : ℤ) + (n : ℤ) = (((m + 1) * n : ℕ) : ℤ) := by push_cast; ring
    have h4' : ((m * n : ℕ) : ℤ) - (n : ℤ) = (((m - 1) * n : ℕ) : ℤ) := by
      have : (m - 1) * n + n = m * n := by
        have := Nat.sub_add_cancel (by omega : 1 ≤ m)
        calc (m - 1) * n + n = (m - 1 + 1) * n := by rw [Nat.add_mul, one_mul]
          _ = m * n := by rw [this]
      omega
    have h5' : ((2 * n : ℕ) : ℤ) + (n : ℤ) = (((3 * n : ℕ) : ℤ)) := by push_cast; ring
    have h6' : ((2 * n : ℕ) : ℤ) - (n : ℤ) = (n : ℤ) := by push_cast; ring
    rw [h1', h2', h3', h4', h5', h6', hu_mul (m + 2), hu_mul (m - 2), hu_mul (m + 1),
      hu_mul (m - 1), hu_mul 2, hu_mul 3, hu_mul m] at h
    have hint : u (m + 2) * u (m - 2) =
        u (m + 1) * u (m - 1) * u 2 ^ 2 - u 3 * u m ^ 2 := by
      apply mul_left_cancel₀ (pow_ne_zero 4 hwn_ne)
      linear_combination h
    have hcast := congrArg (fun t : ℤ => (t : ZMod M)) hint
    simpa only [Int.cast_mul, Int.cast_sub, Int.cast_pow] using hcast
  -- Master formula: `(u k : ZMod M) = cZ ^ (k^2 - 1) * k` for all `k ≥ 1`
  have hu_formula : ∀ k : ℕ, 1 ≤ k → ((u k : ℤ) : ZMod M) = cZ ^ (k ^ 2 - 1) * (k : ZMod M) :=
    u_zmod_formula (m := 2 * e) hp hp5 u cZ hc_unit h2_unit hu1 hu2_val hu_step1 hu_step2
  -- Helper: factorization of `|W (n * k)| = factorization |W n| + factorization |u k|`
  have hfac_split : ∀ k : ℕ, 0 < k →
      (W ((n * k : ℕ) : ℤ)).natAbs.factorization p =
        (W (n : ℤ)).natAbs.factorization p + (u k).natAbs.factorization p := by
    intro k hk
    have hmul_eq : W ((n * k : ℕ) : ℤ) = W (n : ℤ) * u k := by
      rw [Nat.mul_comm]; exact hu_mul k
    have hwnk_ne : W ((n * k : ℕ) : ℤ) ≠ 0 := hnz _ (by exact_mod_cast (Nat.mul_pos hn hk).ne')
    have huk_ne : (u k).natAbs ≠ 0 := by
      intro h0
      apply hwnk_ne
      rw [hmul_eq, Int.natAbs_eq_zero.mp h0, mul_zero]
    rw [hmul_eq, Int.natAbs_mul, Nat.factorization_mul hwn_abs_ne huk_ne, Finsupp.add_apply]
  -- Deduce both parts
  constructor
  · intro k hk hcop
    rw [hfac_split k hk]
    have hnd_k : ¬ p ∣ k := fun hd => by
      have := Nat.dvd_gcd dvd_rfl hd
      rw [hcop.gcd_eq_one] at this
      exact hp.ne_one (Nat.eq_one_of_dvd_one this)
    have hu_unit : IsUnit ((u k : ℤ) : ZMod M) := by
      rw [hu_formula k hk]
      exact (hc_unit.pow _).mul (isUnit_natCast_zmod_pow (m := 2 * e) k hp hnd_k)
    have hnd_uk : ¬ p ∣ (u k).natAbs := by
      intro hd
      have hdZ : (p : ℤ) ∣ u k := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hd)
      have hM_div : p ∣ M := dvd_pow_self p (by omega : 2 * e ≠ 0)
      have hf : ZMod.castHom hM_div (ZMod p) ((u k : ℤ) : ZMod M) = 0 := by
        rw [map_intCast]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdZ
      have hu_p : IsUnit (ZMod.castHom hM_div (ZMod p) ((u k : ℤ) : ZMod M)) :=
        hu_unit.map (ZMod.castHom hM_div (ZMod p))
      rw [hf] at hu_p
      have : NeZero p := ⟨hp.ne_zero⟩
      have : Nontrivial (ZMod p) := ZMod.nontrivial_iff.mpr hp.ne_one
      exact not_isUnit_zero hu_p
    rw [Nat.factorization_eq_zero_of_not_dvd hnd_uk, add_zero]
  · rw [hfac_split p hp.pos]
    have hup : ((u p : ℤ) : ZMod M) = cZ ^ (p ^ 2 - 1) * (p : ZMod M) := hu_formula p hp.pos
    have hp2_dvd_M : p ^ 2 ∣ M := Nat.pow_dvd_pow p (by omega : 2 ≤ 2 * e)
    have hup_p2 : ((u p : ℤ) : ZMod (p ^ 2)) =
        (ZMod.castHom hp2_dvd_M (ZMod (p ^ 2)) (cZ ^ (p ^ 2 - 1))) * (p : ZMod (p ^ 2)) := by
      have h := congrArg (ZMod.castHom hp2_dvd_M (ZMod (p ^ 2))) hup
      simpa [map_mul, map_intCast, map_natCast] using h
    have hp_dvd_up : p ∣ (u p).natAbs := by
      have hp_dvd_M : p ∣ M := dvd_pow_self p (by omega : 2 * e ≠ 0)
      have h := congrArg (ZMod.castHom hp_dvd_M (ZMod p)) hup
      simp only [map_mul, map_intCast, map_natCast, ZMod.natCast_self, mul_zero] at h
      exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h))
    have hp2_ndvd_up : ¬ p ^ 2 ∣ (u p).natAbs := by
      intro hd
      have hdZ : ((p ^ 2 : ℕ) : ℤ) ∣ u p := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hd)
      have h0 : ((u p : ℤ) : ZMod (p ^ 2)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdZ
      rw [h0] at hup_p2
      have hcu : IsUnit (ZMod.castHom hp2_dvd_M (ZMod (p ^ 2)) (cZ ^ (p ^ 2 - 1))) :=
        (hc_unit.pow _).map (ZMod.castHom hp2_dvd_M (ZMod (p ^ 2)))
      have hp0 : (p : ZMod (p ^ 2)) = 0 :=
        hcu.mul_left_cancel (by rw [mul_zero]; exact hup_p2.symm)
      have hdvd : p ^ 2 ∣ p := (ZMod.natCast_eq_zero_iff p (p ^ 2)).mp hp0
      have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hdvd
      nlinarith [hp.two_le]
    have hup_ne : (u p).natAbs ≠ 0 := by
      intro h0
      apply hp2_ndvd_up
      rw [h0]; exact dvd_zero _
    have hge1 : 1 ≤ (u p).natAbs.factorization p := by
      have := Nat.Prime.factorization_pos_of_dvd hp hup_ne hp_dvd_up
      omega
    have hlt2 : (u p).natAbs.factorization p < 2 := by
      by_contra hge2
      push Not at hge2
      exact hp2_ndvd_up (dvd_trans (Nat.pow_dvd_pow p hge2) (Nat.ordProj_dvd _ p))
    have hfac1 : (u p).natAbs.factorization p = 1 := by omega
    rw [hfac1]

end OMA.EDSR1H1

theorem OMA.solution :
    OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1.H1 := by
  classical
  intro W hW hnz
  refine ⟨({2, 3} : Finset ℕ) ∪ (W 2).natAbs.primeFactors ∪ (W 3).natAbs.primeFactors, ?_⟩
  intro p hp hprime hex
  have hnot2 : p ≠ 2 := fun h => hp (by simp [h])
  have hnot3 : p ≠ 3 := fun h => hp (by simp [h])
  have hp5 : 5 ≤ p := by
    have h2 := hprime.two_le
    by_contra hlt
    interval_cases p
    · exact hnot2 rfl
    · exact hnot3 rfl
    · exact absurd hprime (by decide)
  have hw2_ne : (W 2).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hnz 2 (by decide))
  have hw3_ne : (W 3).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hnz 3 (by decide))
  have hnd2 : ¬ p ∣ (W 2).natAbs := fun hd =>
    hp (Finset.mem_union_left _ (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hprime, hd, hw2_ne⟩)))
  have hnd3 : ¬ p ∣ (W 3).natAbs := fun hd =>
    hp (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hprime, hd, hw3_ne⟩))
  obtain ⟨r, hr2, hrank⟩ := OMA.EDSR1H1.ward_rank_local hW.1 hW.2.1 hprime hnd3 hex
  have hr_pos : 0 < r := by omega
  refine ⟨r, hr_pos, hrank, ?_⟩
  have hpowLift : ∀ t : ℕ,
      (W ((r * p ^ t : ℕ) : ℤ)).natAbs.factorization p =
        (W (r : ℤ)).natAbs.factorization p + t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hpos : 0 < r * p ^ t := Nat.mul_pos hr_pos (pow_pos hprime.pos t)
      have hdiv : p ∣ (W ((r * p ^ t : ℕ) : ℤ)).natAbs := (hrank _ hpos).mpr (dvd_mul_right r _)
      have hstep := (OMA.EDSR1H1.valuation_lift_core hW hnz hprime hp5 hnd2 hnd3 hpos hdiv).2
      rw [pow_succ, ← Nat.mul_assoc, hstep, ih, Nat.add_assoc]
  intro k hk
  let t := k.factorization p
  let c := ordCompl[p] k
  have hdecomp : p ^ t * c = k := Nat.ordProj_mul_ordCompl_eq_self k p
  have hpos : 0 < r * p ^ t := Nat.mul_pos hr_pos (pow_pos hprime.pos t)
  have hdiv : p ∣ (W ((r * p ^ t : ℕ) : ℤ)).natAbs := (hrank _ hpos).mpr (dvd_mul_right r _)
  have hcop : p.Coprime c := Nat.coprime_ordCompl hprime hk.ne'
  have hc_pos : 0 < c := Nat.ordCompl_pos p hk.ne'
  have hunit := (OMA.EDSR1H1.valuation_lift_core hW hnz hprime hp5 hnd2 hnd3 hpos hdiv).1 c hc_pos hcop
  have hidx : r * p ^ t * c = r * k := by rw [Nat.mul_assoc, hdecomp]
  rw [hidx] at hunit
  exact hunit.trans (hpowLift t)
