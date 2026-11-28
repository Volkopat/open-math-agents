import OMAReductions.R_oeis_a391613_R1
import Mathlib

/-! Legendre's three-square theorem for squarefree `m ≡ 6 (mod 8)`, by Ankeny's method
(Minkowski's convex body theorem + Dirichlet's theorem + the two-square theorem).
Adapted from the m ≡ 3 (mod 8) formalization of Mehta and Monticone,
https://github.com/pitmonticone/SumsThreeSquares (Apache-2.0), following the outline of
case 2 of Ankeny, Sums of three squares, Proc. AMS 8 (1957). -/

open scoped BigOperators Real Int Nat Classical Pointwise

noncomputable section

namespace OMA.ThreeSq

open MeasureTheory Module Submodule

theorem minkowski_int {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h : 2 ^ n < volume s) :
    ∃ x ≠ 0, (x ∈ s) ∧ (∀ i : Fin n, (∃ (m : ℤ), m = x i)) := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have : Countable (span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (span ℤ (Set.range b)))
  have fund : IsAddFundamentalDomain (span ℤ (Set.range b)).toAddSubgroup
      (ZSpan.fundamentalDomain b) volume := ZSpan.isAddFundamentalDomain' b volume
  have hF : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [(ZSpan.fundamentalDomain_ae_parallelepiped b volume).measure_eq]
    exact (EuclideanSpace.basisFun _ _).volume_parallelepiped
  have hmeas : volume (ZSpan.fundamentalDomain b) *
      2 ^ finrank ℝ (EuclideanSpace ℝ (Fin n)) < volume s := by
    simpa [hF, finrank_euclideanSpace_fin] using h
  obtain ⟨x, hx_ne, hx_mem⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund h_symm h_conv hmeas
  refine ⟨x, fun h0 => hx_ne (Subtype.ext h0), hx_mem, fun i => ?_⟩
  obtain ⟨m, hm⟩ := (b.mem_span_iff_repr_mem ℤ x.1).mp x.2 i
  exact ⟨m, by simpa [b, EuclideanSpace.basisFun_repr] using hm⟩

lemma dvd_of_odd_padicValInt {p : ℕ} {n : ℤ}
    (h : Odd (padicValInt p n)) : (p : ℤ) ∣ n := by
  by_contra hpn
  rw [padicValInt.eq_zero_of_not_dvd hpn] at h
  exact absurd h (by decide)

lemma not_jacobiSym_eq_one_of_dvd {p : ℕ} (hp : Nat.Prime p) {k : ℤ} (hpk : (p : ℤ) ∣ k) :
    jacobiSym k p ≠ 1 := by
  rw [jacobiSym.mod_left, Int.emod_eq_zero_of_dvd hpk, jacobiSym.zero_left hp.one_lt]
  decide

/-! ### Choice of the auxiliary prime `q` -/

/-- CRT over the prime factors of an odd `m`, together with a residue `≡ 5 (mod 8)`. -/
lemma exists_crt_primeFactors_and_mod8 {m : ℕ} (hm_odd : Odd m) (a : ℕ → ℕ) :
    ∃ c : ℕ, (∀ p : ℕ, p ∣ m → Nat.Prime p → c ≡ a p [MOD p]) ∧ c ≡ 5 [MOD 8] := by
  have hodd : ∀ p ∈ m.primeFactors, Odd p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd'.resolve_left fun h2 => by
      subst h2
      have h2dvd := Nat.dvd_of_mem_primeFactors hp
      have := Nat.odd_iff.mp hm_odd
      omega
  obtain ⟨c, hc⟩ := Nat.chineseRemainderOfFinset (fun p => if p = 8 then 5 else a p) id
    (insert 8 m.primeFactors)
    (fun p hp => by rcases Finset.mem_insert.mp hp with rfl | hp
                    · norm_num
                    · exact (Nat.prime_of_mem_primeFactors hp).ne_zero)
    (fun p hp r hr hpr => by
      rcases Finset.mem_insert.mp hp with rfl | hp <;>
        rcases Finset.mem_insert.mp hr with rfl | hr
      · exact absurd rfl hpr
      · exact Nat.Coprime.pow_left 3 (hodd r hr).coprime_two_left
      · exact Nat.coprime_comm.mp (Nat.Coprime.pow_left 3 (hodd p hp).coprime_two_left)
      · exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
          (Nat.prime_of_mem_primeFactors hr)).mpr hpr)
  refine ⟨c, fun p hp_dvd hp_prime => ?_, by simpa using hc 8 (Finset.mem_insert_self _ _)⟩
  have hp_in : p ∈ insert 8 m.primeFactors := Finset.mem_insert_of_mem
    (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, hm_odd.pos.ne'⟩)
  have hp_ne_8 : p ≠ 8 := fun h => absurd hp_prime (h ▸ by decide)
  simpa [if_neg hp_ne_8] using hc p hp_in

lemma exists_prime_eq_mod {a N : ℕ} (hN : 0 < N) (hcop : Nat.Coprime a N) :
    ∃ q : ℕ, Nat.Prime q ∧ q % N = a % N := by
  have : NeZero N := ⟨hN.ne'⟩
  have h_dir : Set.Infinite {q : ℕ | Nat.Prime q ∧ q % N = a % N} := by
    convert Nat.infinite_setOf_prime_and_eq_mod (q := N) (a := (a : ZMod N))
      ((ZMod.isUnit_iff_coprime a N).mpr hcop) using 1
    norm_num [← ZMod.natCast_eq_natCast_iff']
  exact h_dir.nonempty

/-- For an odd prime `p`, `a = p - 1` has `(-a/p) = 1` and `p ∤ a`. -/
lemma residue_for_prime (p : ℕ) (hp : Nat.Prime p) :
    jacobiSym (-((p - 1 : ℕ) : ℤ)) p = 1 ∧ (p - 1) % p ≠ 0 := by
  have hp2 := hp.two_le
  constructor
  · have h1 : (-((p - 1 : ℕ) : ℤ)) = 1 + (p : ℤ) * (-1) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
    rw [jacobiSym.mod_left, h1, Int.add_mul_emod_self_left, ← jacobiSym.mod_left,
      jacobiSym.one_left]
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

lemma exists_prime_q (m₁ : ℕ) (hm_odd : Odd m₁) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 8 = 5 ∧
      ∀ p, p ∣ m₁ → Nat.Prime p → jacobiSym (-(q : ℤ)) p = 1 := by
  obtain ⟨c, hcp, hc8⟩ := exists_crt_primeFactors_and_mod8 hm_odd (fun p => p - 1)
  have hc_cop : Nat.Coprime c (8 * m₁) := by
    refine Nat.Coprime.mul_right (hc8.gcd_eq.trans (by norm_num)) ?_
    refine Nat.coprime_of_dvd' fun k hk hk₁ hk₂ => ?_
    have h1 := hcp k hk₂ hk
    have h2 := (residue_for_prime k hk).2
    exfalso; apply h2
    have : c % k = 0 := Nat.eq_zero_of_dvd_of_lt (Nat.dvd_mod_iff dvd_rfl |>.mpr hk₁)
      (Nat.mod_lt _ hk.pos) |> fun h => by simpa using h
    rw [← h1]; exact Nat.mod_eq_zero_of_dvd hk₁
  obtain ⟨q, hq_prime, hq_mod⟩ := exists_prime_eq_mod (by
    have := hm_odd.pos; omega : 0 < 8 * m₁) hc_cop
  refine ⟨q, hq_prime, ?_, fun p hp hp_prime => ?_⟩
  · rw [← Nat.mod_mod_of_dvd q (dvd_mul_right 8 m₁), hq_mod,
        Nat.mod_mod_of_dvd _ (dvd_mul_right 8 m₁)]
    exact hc8
  · have h_qap : (q : ℤ) ≡ ((p - 1 : ℕ) : ℤ) [ZMOD p] :=
      (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_right hp 8))
        (Int.natCast_modEq_iff.mpr hq_mod)).trans
        (Int.natCast_modEq_iff.mpr (hcp p hp hp_prime))
    rw [jacobiSym.mod_left (-(q : ℤ)), h_qap.neg, ← jacobiSym.mod_left]
    exact (residue_for_prime p hp_prime).1

lemma jacobi_prod_eq_one (m₁ : ℕ) (a : ℤ)
    (h : ∀ p, p ∣ m₁ → Nat.Prime p → jacobiSym a p = 1) : jacobiSym a m₁ = 1 := by
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_pmap.mp hx
  have hp_prime := Nat.prime_of_mem_primeFactorsList hp
  have := Fact.mk hp_prime
  simpa [jacobiSym, Nat.primeFactorsList_prime hp_prime] using
    h p (Nat.dvd_of_mem_primeFactorsList hp) hp_prime

/-- `(-m/q) = 1` for `m = 2 m₁`, `m₁ ≡ 3 (mod 4)`. -/
lemma jacobi_neg_m_q (m₁ q : ℕ) (hm₁ : m₁ % 4 = 3) (hq_mod : q % 8 = 5)
    (h_jacobi : ∀ p, p ∣ m₁ → Nat.Prime p → jacobiSym (-(q : ℤ)) p = 1) :
    jacobiSym (-((2 * m₁ : ℕ) : ℤ)) q = 1 := by
  have hm_odd : Odd m₁ := Nat.odd_iff.mpr (by omega)
  have hq_odd : Odd q := Nat.odd_iff.mpr (by omega)
  have hq4 : q % 4 = 1 := by omega
  have h_qm : jacobiSym (-(q : ℤ)) m₁ = 1 := jacobi_prod_eq_one m₁ _ h_jacobi
  have h_qm' : jacobiSym (q : ℤ) m₁ = -1 := by
    rw [jacobiSym.neg _ hm_odd, ZMod.χ₄_nat_three_mod_four hm₁] at h_qm
    linarith
  have h2 : jacobiSym 2 q = -1 := by
    rw [jacobiSym.at_two hq_odd, ZMod.χ₈_nat_mod_eight, hq_mod]; decide
  have hm1q : jacobiSym (m₁ : ℤ) q = -1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hm_odd hq4]; exact h_qm'
  have : (-((2 * m₁ : ℕ) : ℤ)) = (-1) * (2 * (m₁ : ℤ)) := by push_cast; ring
  rw [this, jacobiSym.mul_left, jacobiSym.mul_left, h2, hm1q, jacobiSym.at_neg_one hq_odd,
    ZMod.χ₄_nat_one_mod_four hq4]
  norm_num

/-! ### The integers `b, h, t` -/

lemma exists_b_h (m q : ℕ) (hq_prime : Nat.Prime q) (h_jacobi : jacobiSym (-(m : ℤ)) q = 1) :
    ∃ b h : ℤ, b ^ 2 - q * h = -m := by
  have := Fact.mk hq_prime
  obtain ⟨x, hx⟩ := ZMod.isSquare_of_jacobiSym_eq_one h_jacobi
  have hb₀ : (x.val : ℤ) ^ 2 ≡ -(m : ℤ) [ZMOD q] := by
    simpa [sq, ← ZMod.intCast_eq_intCast_iff] using hx.symm
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.mp hb₀.symm)
  exact ⟨x.val, k, by linarith⟩

lemma exists_t_local (p q : ℕ) (hp : Nat.Prime p) (hq_odd : Odd q)
    (hp_cop : Nat.Coprime q p) (hjac : p ≠ 2 → jacobiSym (-(q : ℤ)) p = 1) :
    ∃ t : ℤ, q * t ^ 2 ≡ -1 [ZMOD p] := by
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨1, Int.modEq_iff_dvd.mpr ?_⟩
    obtain ⟨k, hk⟩ := hq_odd
    exact ⟨-(k : ℤ) - 1, by push_cast [hk]; ring⟩
  have := Fact.mk hp
  obtain ⟨x, hx⟩ := ZMod.isSquare_of_jacobiSym_eq_one (hjac hp2)
  have hs : (x.val : ℤ) ^ 2 ≡ -q [ZMOD p] := by
    simpa [sq, ← ZMod.intCast_eq_intCast_iff] using hx.symm
  obtain ⟨inv, hinv⟩ : ∃ inv : ℤ, (q : ℤ) * inv ≡ 1 [ZMOD p] := Int.mod_coprime hp_cop
  refine ⟨x.val * inv, ?_⟩
  have e : (q : ℤ) * (x.val * inv) ^ 2 = (x.val : ℤ) ^ 2 * (q * inv) * inv := by ring
  rw [e]
  calc (x.val : ℤ) ^ 2 * (q * inv) * inv ≡ (-q) * 1 * inv [ZMOD p] :=
        ((hs.mul hinv).mul_right _)
    _ = -(q * inv) := by ring
    _ ≡ -1 [ZMOD p] := hinv.neg

lemma exists_t (m q : ℕ) (hm_sq : Squarefree m) (hq_prime : Nat.Prime q) (hq_odd : Odd q)
    (hqm : ¬ q ∣ m)
    (h_jacobi : ∀ p, p ∣ m → Nat.Prime p → p ≠ 2 → jacobiSym (-(q : ℤ)) p = 1) :
    ∃ t : ℤ, (q : ℤ) * t ^ 2 ≡ -1 [ZMOD m] := by
  have h_tp : ∀ p ∈ Nat.primeFactors m, ∃ t_p : ℤ, q * t_p ^ 2 ≡ -1 [ZMOD (p : ℤ)] := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hpm := Nat.dvd_of_mem_primeFactors hp
    refine exists_t_local p q hp_prime hq_odd ((Nat.coprime_primes hq_prime hp_prime).mpr
      fun heq => hqm (heq ▸ hpm)) (h_jacobi p hpm hp_prime)
  choose! t ht using h_tp
  obtain ⟨c, hc⟩ := Nat.chineseRemainderOfFinset (fun p => ((t p).emod p).toNat) id
    m.primeFactors (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
    (fun _ hp _ hq hpq => (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  refine ⟨c, ?_⟩
  rw [Int.modEq_iff_dvd, ← Nat.prod_primeFactors_of_squarefree hm_sq, Nat.cast_prod]
  refine Finset.prod_dvd_of_coprime
    (fun _ hp _ hq hpq => ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq).cast)
    (fun p hp => Int.modEq_iff_dvd.mp ?_)
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have h1 : (c : ℤ) ≡ ((t p).emod p).toNat [ZMOD (p : ℤ)] := by exact_mod_cast hc p hp
  have hcp : (c : ℤ) ≡ t p [ZMOD (p : ℤ)] :=
    (Int.toNat_of_nonneg (Int.emod_nonneg _ hp_ne) ▸ h1).trans (Int.emod_emod_of_dvd _ dvd_rfl)
  exact ((hcp.pow 2).mul_left _).trans (ht p hp)

/-! ### The lattice and Minkowski's theorem -/

noncomputable def linM (m q : ℕ) (t b : ℤ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  Matrix.toLin' (!![
    t * q, t * b, m;
    Real.sqrt q, b / Real.sqrt q, 0;
    0, Real.sqrt m / Real.sqrt q, 0])

lemma det_linM (m q : ℕ) (t b : ℤ) (hq : 0 < q) :
    LinearMap.det (linM m q t b) = m * Real.sqrt m := by
  unfold linM
  simp [Matrix.det_fin_three]
  have : Real.sqrt q ≠ 0 := by positivity
  field_simp

noncomputable abbrev linME (m q : ℕ) (t b : ℤ) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearMap ∘ₗ
    (linM m q t b) ∘ₗ (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap

lemma det_linME (m q : ℕ) (t b : ℤ) (hq : 0 < q) :
    LinearMap.det (linME m q t b) = m * Real.sqrt m :=
  (LinearMap.det_conj (linM m q t b)
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearEquiv).trans (det_linM m q t b hq)

lemma linME_apply (m q : ℕ) (t b : ℤ) (x : EuclideanSpace ℝ (Fin 3)) :
    (linME m q t b x) 0 = t * q * x 0 + t * b * x 1 + m * x 2 ∧
    (linME m q t b x) 1 = Real.sqrt q * x 0 + b / Real.sqrt q * x 1 ∧
    (linME m q t b x) 2 = Real.sqrt m / Real.sqrt q * x 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp [linME, linM, Matrix.toLin'_apply, Matrix.vecHead, Matrix.vecTail]; try ring)

lemma quad_form_decomposition (m q : ℕ) (b h x y : ℤ) (hq : 0 < q)
    (hbqm : b ^ 2 - q * h = -m) :
    (Real.sqrt q * x + (b : ℝ) / Real.sqrt q * y) ^ 2 + (Real.sqrt m / Real.sqrt q * y) ^ 2 =
      (q : ℝ) * x ^ 2 + 2 * (b : ℝ) * x * y + (h : ℝ) * y ^ 2 := by
  have hb2 : (b : ℝ) ^ 2 = q * h - m := by exact_mod_cast (by linarith : (b : ℤ) ^ 2 = q * h - m)
  have : Real.sqrt q ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ))]
  linear_combination (y : ℝ) ^ 2 * hb2

lemma vol_gt_eight (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    (2 : ENNReal) ^ 3 < MeasureTheory.volume
      ((linME m q t b) ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) := by
  have hdet_ne : LinearMap.det (linME m q t b) ≠ 0 := by
    rw [det_linME m q t b hq]; positivity
  rw [MeasureTheory.Measure.addHaar_preimage_linearMap _ hdet_ne,
      det_linME m q t b hq, EuclideanSpace.volume_ball_fin_three,
      abs_inv, abs_of_nonneg (by positivity),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      (by norm_num : ((2 : ENNReal) ^ 3) = ENNReal.ofReal 8),
      ENNReal.ofReal_lt_ofReal_iff (by positivity),
      (by rw [pow_succ, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * m),
          Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]; ring :
        (Real.sqrt (2 * m)) ^ 3 = 2 * Real.sqrt 2 * ((m : ℝ) * Real.sqrt m))]
  field_simp
  nlinarith [Real.pi_gt_three, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two,
    (by positivity : 0 < (m : ℝ) * Real.sqrt m)]

lemma exists_lattice_lt_two_m (m q : ℕ) (t b : ℤ) (hm : 0 < m) (hq : 0 < q) :
    ∃ (x y z : ℤ), (x, y, z) ≠ (0, 0, 0) ∧
    ((t * q : ℝ) * x + (t * b : ℝ) * y + (m : ℝ) * z) ^ 2 +
      (Real.sqrt q * x + (b : ℝ) / Real.sqrt q * y) ^ 2 +
      (Real.sqrt m / Real.sqrt q * y) ^ 2 < 2 * m := by
  obtain ⟨x, hx0, hxs, h⟩ :=
    minkowski_int (fun _ hx => by simpa using hx)
      (Convex.linear_preimage (convex_ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt (2 * m))) _)
      (vol_gt_eight m q t b hm hq)
  choose R hR using h
  refine ⟨R 0, R 1, R 2, ?_, ?_⟩
  · contrapose! hx0
    ext i; rw [← hR i]; fin_cases i <;> aesop
  · obtain ⟨h0, h1, h2⟩ := linME_apply m q t b x
    have h_norm_sq : (‖linME m q t b x‖ ^ 2 : ℝ) < 2 * m := by
      have : ‖linME m q t b x‖ < Real.sqrt (2 * m) := by simpa using hxs
      nlinarith [norm_nonneg (linME m q t b x), Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * m)]
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, h0, h1, h2] at h_norm_sq
    convert h_norm_sq using 1
    push_cast [hR 0, hR 1, hR 2]
    ring

lemma rst_modEq_zero (m q : ℕ) (t b h x y z : ℤ)
    (hqt : (q : ℤ) * t ^ 2 ≡ -1 [ZMOD m]) (hbqm : b ^ 2 - q * h = -m) :
    (t * q * x + t * b * y + m * z) ^ 2 + (q * x ^ 2 + 2 * b * x * y + h * y ^ 2)
      ≡ 0 [ZMOD m] := by
  obtain ⟨c, hc⟩ : (m : ℤ) ∣ q * t ^ 2 + 1 := by
    simpa [neg_sub] using (Int.modEq_iff_dvd.mp hqt).neg_right
  rw [Int.modEq_zero_iff_dvd]
  refine ⟨c * (q * x ^ 2 + 2 * b * x * y + h * y ^ 2) - t ^ 2 * y ^ 2 +
    2 * t * (q * x + b * y) * z + m * z ^ 2, ?_⟩
  linear_combination (q * x ^ 2 + 2 * b * x * y + h * y ^ 2) * hc + t ^ 2 * y ^ 2 * hbqm

lemma q_v_eq {m : ℕ} {q b h x y : ℤ} (hbqm : b ^ 2 - q * h = -(m : ℤ)) :
    q * (q * x ^ 2 + 2 * b * x * y + h * y ^ 2) = (q * x + b * y) ^ 2 + m * y ^ 2 := by
  linear_combination -hbqm * y ^ 2

lemma quadform_nonneg {q : ℕ} {b h : ℤ} {m : ℕ} (hq : 0 < q)
    (hbqm : b ^ 2 - (q : ℤ) * h = -(m : ℤ)) (x y : ℤ) :
    0 ≤ (q : ℤ) * x ^ 2 + 2 * b * x * y + h * y ^ 2 := by
  have e := q_v_eq (x := x) (y := y) hbqm
  have : 0 ≤ (q : ℤ) * ((q : ℤ) * x ^ 2 + 2 * b * x * y + h * y ^ 2) := by
    rw [e]; positivity
  exact nonneg_of_mul_nonneg_right this (by exact_mod_cast hq : (0 : ℤ) < q)

lemma quadform_eq_zero {q : ℕ} {b h : ℤ} {m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (hbqm : b ^ 2 - (q : ℤ) * h = -(m : ℤ)) {x y : ℤ}
    (h0 : (q : ℤ) * x ^ 2 + 2 * b * x * y + h * y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have e := q_v_eq (x := x) (y := y) hbqm
  rw [h0, mul_zero] at e
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hy : y = 0 := by nlinarith [sq_nonneg ((q : ℤ) * x + b * y), sq_nonneg y]
  subst hy
  have : (q : ℤ) * x = 0 := by nlinarith [sq_nonneg ((q : ℤ) * x)]
  exact ⟨(mul_eq_zero.mp this).resolve_left (by exact_mod_cast hq.ne'), rfl⟩

lemma exists_Rv (m q : ℕ) (t b h : ℤ) (hm : 0 < m) (hq : 0 < q)
    (hqt : (q : ℤ) * t ^ 2 ≡ -1 [ZMOD m]) (hbqm : b ^ 2 - (q : ℤ) * h = -(m : ℤ)) :
    ∃ (x y R : ℤ) (v : ℕ), (v : ℤ) = q * x ^ 2 + 2 * b * x * y + h * y ^ 2 ∧
      R ^ 2 + (v : ℤ) = (m : ℤ) := by
  obtain ⟨x, y, z, hne, hlt⟩ := exists_lattice_lt_two_m m q t b hm hq
  have hqf := quadform_nonneg hq hbqm x y
  set R : ℤ := t * q * x + t * b * y + m * z with hR
  have h_lt : R ^ 2 + ((q : ℤ) * x ^ 2 + 2 * b * x * y + h * y ^ 2) < 2 * m := by
    have hqfd := quad_form_decomposition m q b h x y hq hbqm
    have : ((R : ℤ) : ℝ) ^ 2 +
        (((q : ℤ) * x ^ 2 + 2 * b * x * y + h * y ^ 2 : ℤ) : ℝ) < 2 * m := by
      rw [hR]; push_cast; linarith
    exact_mod_cast this
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp (rst_modEq_zero m q t b h x y z hqt hbqm)
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hk0 : 0 ≤ k := by nlinarith [sq_nonneg R]
  have hk2 : k < 2 := by nlinarith
  interval_cases k
  · exfalso
    have hq0 : (q : ℤ) * x ^ 2 + 2 * b * x * y + h * y ^ 2 = 0 := by nlinarith [sq_nonneg R]
    obtain ⟨rfl, rfl⟩ := quadform_eq_zero hq hm hbqm hq0
    have hR0 : R = 0 := by nlinarith [sq_nonneg R]
    have hz : z = 0 := by
      rw [hR] at hR0
      simp at hR0
      exact hR0.resolve_left (by omega)
    exact hne (by simp [hz])
  · exact ⟨x, y, R, ((q : ℤ) * x ^ 2 + 2 * b * x * y + h * y ^ 2).toNat,
      Int.toNat_of_nonneg hqf, by rw [Int.toNat_of_nonneg hqf]; linarith⟩

/-! ### Odd primes `≡ 3 (mod 4)` divide `v` to an even power -/

lemma jacobi_neg_d_of_dvd_sq_add (p : ℕ) (a d b' : ℤ) (hp : Nat.Prime p)
    (hp_dvd : (p : ℤ) ∣ a ^ 2 + d * b' ^ 2) (hp_not_dvd_d : ¬ (p : ℤ) ∣ d)
    (hp_not_dvd_b : ¬ (p : ℤ) ∣ b') :
    jacobiSym (-d) p = 1 := by
  have := Fact.mk hp
  rw [jacobiSym]
  norm_num [Nat.primeFactorsList_prime hp]
  simp_all [← ZMod.intCast_zmod_eq_zero_iff_dvd, legendreSym.eq_one_iff]
  use a / b'
  grind

lemma jacobi_neg_d_of_odd_padicVal (p : ℕ) (a d b' : ℤ) (hp : Nat.Prime p)
    (hp_not_dvd_d : ¬ (p : ℤ) ∣ d)
    (h_odd_val : Odd (padicValInt p (a ^ 2 + d * b' ^ 2))) :
    jacobiSym (-d) p = 1 := by
  induction' n : Int.natAbs a + Int.natAbs b' using Nat.strong_induction_on with n ih
    generalizing a b'
  by_cases h_div_b' : (p : ℤ) ∣ b'
  · obtain ⟨k, hk⟩ := h_div_b'
    obtain ⟨a', ha'⟩ : ∃ a', a = p * a' :=
      Int.Prime.dvd_pow' hp <| by
        simpa [hk, ← ZMod.intCast_zmod_eq_zero_iff_dvd] using dvd_of_odd_padicValInt h_odd_val
    contrapose! ih
    refine ⟨a'.natAbs + k.natAbs, ?_, a', k, ?_, rfl, ih⟩
    · rcases eq_or_ne a' 0 with ha0 | ha0 <;> rcases eq_or_ne k 0 with hk0 | hk0 <;>
        simp_all [Int.natAbs_mul]
      · exact n ▸ lt_mul_of_one_lt_left (Int.natAbs_pos.mpr hk0) hp.one_lt
      · exact n ▸ lt_mul_of_one_lt_left (Int.natAbs_pos.mpr ha0) hp.one_lt
      · nlinarith [hp.two_le, abs_pos.mpr ha0, abs_pos.mpr hk0]
    · simp_all [padicValInt, parity_simps]
      have hfactor : (p * a') ^ 2 + d * (p * k) ^ 2 = p ^ 2 * (a' ^ 2 + d * k ^ 2) := by ring
      rw [hfactor, Int.natAbs_mul, Int.natAbs_pow] at h_odd_val
      have := Fact.mk hp
      rw [padicValNat.mul] at h_odd_val <;> simp_all +decide [parity_simps]
      · exact hp.ne_zero
      · intro H; simp_all
  · exact jacobi_neg_d_of_dvd_sq_add p a d b' hp (dvd_of_odd_padicValInt h_odd_val)
      hp_not_dvd_d h_div_b'

lemma jacobiSym_eq_one_of_sq_modEq {p : ℕ} (hp : Nat.Prime p) {a R : ℤ}
    (hpa : ¬ (p : ℤ) ∣ a) (hRa : R ^ 2 ≡ a [ZMOD p]) :
    jacobiSym a p = 1 := by
  have := Fact.mk hp
  simp_all [← ZMod.intCast_eq_intCast_iff, jacobiSym, Nat.primeFactorsList_prime hp]
  rw [legendreSym.eq_one_iff]
  · exact ⟨R, by simpa [sq] using hRa.symm⟩
  · rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hpa

lemma padicValInt_q_v {p : ℕ} {q v : ℤ} (hp : Nat.Prime p) (hpq : ¬ (p : ℤ) ∣ q)
    (hpv : Odd (padicValInt p v)) : padicValInt p (q * v) = padicValInt p v := by
  have := Fact.mk hp
  have hq0 : q ≠ 0 := by rintro rfl; exact hpq (dvd_zero _)
  have hv0 : v ≠ 0 := by rintro rfl; simp at hpv
  rw [padicValInt.mul hq0 hv0, padicValInt.eq_zero_of_not_dvd hpq, zero_add]

lemma mod4_of_jacobi {p : ℕ} (hp : Nat.Prime p) (hp3 : p % 4 = 3) {a : ℤ}
    (h1 : jacobiSym a p = 1) (h2 : jacobiSym (-a) p = 1) : False := by
  rw [jacobiSym.neg _ (hp.odd_of_ne_two (by omega)), ZMod.χ₄_nat_three_mod_four hp3, h1] at h2
  norm_num at h2

/-- `p ∤ m`: an odd power of `p ≡ 3 (mod 4)` cannot exactly divide `v`. -/
lemma case_not_dvd (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 4 = 3) (m : ℕ) (q b h x y R v : ℤ)
    (hv : v = q * x ^ 2 + 2 * b * x * y + h * y ^ 2) (hbqm : b ^ 2 - q * h = -(m : ℤ))
    (hRv : R ^ 2 + v = m) (hpv : Odd (padicValInt p v)) (hpm : ¬ (p : ℤ) ∣ m) : False := by
  have hpv_dvd : (p : ℤ) ∣ v := dvd_of_odd_padicValInt hpv
  have h_m : jacobiSym m p = 1 :=
    jacobiSym_eq_one_of_sq_modEq hp hpm (R := R)
      (Int.modEq_iff_dvd.mpr (by rw [show (m : ℤ) - R ^ 2 = v by linarith]; exact hpv_dvd))
  have h_negm : jacobiSym (-(m : ℤ)) p = 1 := by
    by_cases hpq : (p : ℤ) ∣ q
    · refine jacobiSym_eq_one_of_sq_modEq hp (by simpa using hpm) (R := b) ?_
      obtain ⟨c, hc⟩ := hpq
      exact Int.modEq_iff_dvd.mpr ⟨-h * c, by linear_combination -hbqm - h * hc⟩
    · have hval := padicValInt_q_v hp hpq hpv
      apply jacobi_neg_d_of_odd_padicVal p (q * x + b * y) m y hp hpm
      rw [← q_v_eq hbqm, ← hv, hval]; exact hpv
  exact mod4_of_jacobi hp hp3 h_m h_negm

/-- `p ∣ m`: then `y² ≡ q (mod p)`, contradicting `(-q/p) = 1` when `p ≡ 3 (mod 4)`. -/
lemma case_dvd (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 4 = 3) (m : ℕ) (hm_sq : Squarefree m)
    (q : ℕ) (b h x y R v : ℤ)
    (hv : v = q * x ^ 2 + 2 * b * x * y + h * y ^ 2) (hbqm : b ^ 2 - (q : ℤ) * h = -(m : ℤ))
    (hRv : R ^ 2 + v = m) (hpv : (p : ℤ) ∣ v) (hpm : p ∣ m)
    (hjac : jacobiSym (-(q : ℤ)) p = 1) : False := by
  have hpm' : (p : ℤ) ∣ m := Int.natCast_dvd_natCast.mpr hpm
  have hpR : (p : ℤ) ∣ R := Int.Prime.dvd_pow' hp <| by
    have : R ^ 2 = m - v := by linarith
    rw [this]; exact dvd_sub hpm' hpv
  have hqv := q_v_eq (x := x) (y := y) hbqm
  rw [← hv] at hqv
  have hpe : (p : ℤ) ∣ q * x + b * y := Int.Prime.dvd_pow' hp <| by
    have : (q * x + b * y) ^ 2 = q * v - m * y ^ 2 := by linarith
    rw [this]; exact dvd_sub (hpv.mul_left _) (hpm'.mul_right _)
  obtain ⟨r, hr⟩ := hpR
  obtain ⟨s, hs⟩ := hpe
  obtain ⟨m', hm'⟩ := hpm
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  -- q m = q R² + q v = q p² r² + p² s² + p m' y², so m' (q - y²) = p (q r² + s²)
  have key : (m' : ℤ) * ((q : ℤ) - y ^ 2) = p * (q * r ^ 2 + s ^ 2) := by
    have e1 : (q : ℤ) * m = q * R ^ 2 + (q * x + b * y) ^ 2 + m * y ^ 2 := by
      linear_combination (-(q : ℤ)) * hRv + hqv
    rw [hr, hs, hm'] at e1
    push_cast at e1
    have : (p : ℤ) * ((m' : ℤ) * ((q : ℤ) - y ^ 2)) = p * (p * (q * r ^ 2 + s ^ 2)) := by
      linear_combination e1
    exact mul_left_cancel₀ hp0 this
  have hpm'_not : ¬ (p : ℤ) ∣ m' := by
    intro ⟨c, hc⟩
    have : p * p ∣ m := ⟨c.toNat, by
      have hc0 : 0 ≤ c := by
        by_contra hneg
        have : (m' : ℤ) < 0 := by rw [hc]; nlinarith [hp.pos]
        omega
      zify; rw [Int.toNat_of_nonneg hc0, hm']; push_cast; rw [hc]; ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hm_sq p this))
  have hdiv : (p : ℤ) ∣ (q : ℤ) - y ^ 2 :=
    (Int.Prime.dvd_mul' hp ⟨_, key⟩).resolve_left hpm'_not
  have hpq : ¬ (p : ℤ) ∣ q := fun hd =>
    not_jacobiSym_eq_one_of_dvd hp (dvd_neg.mpr hd) hjac
  have h1 : jacobiSym (q : ℤ) p = 1 :=
    jacobiSym_eq_one_of_sq_modEq hp hpq (R := y) ((Int.modEq_iff_dvd.mpr hdiv))
  exact mod4_of_jacobi hp hp3 h1 hjac

lemma even_padicVal (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 4 = 3) (m : ℕ) (hm_sq : Squarefree m)
    (q : ℕ) (b h x y R : ℤ) (v : ℕ)
    (hv : (v : ℤ) = q * x ^ 2 + 2 * b * x * y + h * y ^ 2)
    (hbqm : b ^ 2 - (q : ℤ) * h = -(m : ℤ)) (hRv : R ^ 2 + (v : ℤ) = m)
    (hjac : ∀ p', p' ∣ m → Nat.Prime p' → p' ≠ 2 → jacobiSym (-(q : ℤ)) p' = 1) :
    Even (padicValNat p v) := by
  rw [← padicValInt.of_nat]
  by_contra h_even
  have h_odd : Odd (padicValInt p (v : ℤ)) := Nat.not_even_iff_odd.mp h_even
  by_cases hpm : p ∣ m
  · exact case_dvd p hp hp3 m hm_sq q b h x y R v hv hbqm hRv (dvd_of_odd_padicValInt h_odd) hpm
      (hjac p hpm hp (by omega))
  · exact case_not_dvd p hp hp3 m q b h x y R v hv hbqm hRv h_odd (by exact_mod_cast hpm)

/-- Legendre's three-square theorem for squarefree `m ≡ 6 (mod 8)`. -/
theorem three_sq_of_six (m : ℕ) (hm_sq : Squarefree m) (hm_mod : m % 8 = 6) :
    ∃ a b c : ℤ, (m : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 := by
  set m₁ := m / 2 with hm₁_def
  have hm2 : m = 2 * m₁ := by omega
  have hm₁ : m₁ % 4 = 3 := by omega
  have hm₁_odd : Odd m₁ := Nat.odd_iff.mpr (by omega)
  obtain ⟨q, hq_prime, hq_mod, hjac₁⟩ := exists_prime_q m₁ hm₁_odd
  have hq_odd : Odd q := Nat.odd_iff.mpr (by omega)
  have hjac : ∀ p, p ∣ m → Nat.Prime p → p ≠ 2 → jacobiSym (-(q : ℤ)) p = 1 := by
    intro p hp hpp hp2
    refine hjac₁ p ?_ hpp
    rw [hm2] at hp
    exact (Nat.Coprime.dvd_of_dvd_mul_left
      ((Nat.coprime_primes hpp Nat.prime_two).mpr hp2) hp)
  have hqm : ¬ q ∣ m := by
    intro hd
    have hqm₁ : q ∣ m₁ := by
      rw [hm2] at hd
      exact Nat.Coprime.dvd_of_dvd_mul_left
        ((Nat.coprime_primes hq_prime Nat.prime_two).mpr (by omega)) hd
    exact not_jacobiSym_eq_one_of_dvd hq_prime (by simp) (hjac₁ q hqm₁ hq_prime)
  have hJ := jacobi_neg_m_q m₁ q hm₁ hq_mod hjac₁
  rw [← hm2] at hJ
  obtain ⟨b, h, hbqm⟩ := exists_b_h m q hq_prime hJ
  obtain ⟨t, hqt⟩ := exists_t m q hm_sq hq_prime hq_odd hqm hjac
  obtain ⟨x, y, R, v, hv, hRv⟩ := exists_Rv m q t b h (by omega) hq_prime.pos hqt hbqm
  obtain ⟨s, u, hsu⟩ : ∃ s u : ℕ, v = s ^ 2 + u ^ 2 := Nat.eq_sq_add_sq_iff.mpr fun p hp hp3 =>
    even_padicVal p (Nat.prime_of_mem_primeFactors hp) hp3 m hm_sq q b h x y R v hv hbqm hRv hjac
  exact ⟨R, s, u, by rw [← hRv, hsu]; push_cast; ring⟩

end OMA.ThreeSq

namespace OMA.ThreeSq

theorem H1_core : ∀ n : ℕ, n % 8 = 7 → ∃ a b c : ℕ, 2 * n = a ^ 2 + b ^ 2 + c ^ 2 := by
  intro n hn
  obtain ⟨m, k, hkm, hm_sq⟩ := Nat.sq_mul_squarefree (2 * n)
  have hk_odd : k % 2 = 1 := by
    by_contra hk
    have h4 : 4 ∣ 2 * n := by
      rw [← hkm]
      obtain ⟨j, hj⟩ : 2 ∣ k := by omega
      exact ⟨j ^ 2 * m, by rw [hj]; ring⟩
    omega
  have hk8 : k ^ 2 % 8 = 1 := by
    have : k % 8 = 1 ∨ k % 8 = 3 ∨ k % 8 = 5 ∨ k % 8 = 7 := by omega
    rw [Nat.pow_mod]; rcases this with h | h | h | h <;> rw [h]
  have hm8 : m % 8 = 6 := by
    have e : (k ^ 2 * m) % 8 = (2 * n) % 8 := by rw [hkm]
    rw [Nat.mul_mod, hk8, one_mul, Nat.mod_mod] at e
    omega
  obtain ⟨a, b, c, habc⟩ := three_sq_of_six m hm_sq hm8
  refine ⟨k * a.natAbs, k * b.natAbs, k * c.natAbs, ?_⟩
  have hkz : (k : ℤ) ^ 2 * m = 2 * n := by exact_mod_cast hkm
  zify
  rw [← hkz]
  simp only [mul_pow, sq_abs]
  rw [habc]; ring

end OMA.ThreeSq

theorem OMA.solution : OMA.R_oeis_a391613_R1.H1 := OMA.ThreeSq.H1_core
