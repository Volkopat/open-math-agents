import OMAStatements.S_mse_141308
import Mathlib

-- Problem: Primality test for specific class of 3 * 2 ^ n + 1 (mse-141308)
-- The seeds are t ^ 3 - 3 * t for t = 37, 32, 12, 28.
--  * prime => test passes: t + 2 and t - 2 are quadratic non-residues modulo N (quadratic reciprocity),
--    so b + 1 / b = t has a root b in ZMod N that is not a square, and Euler's criterion gives
--    b ^ ((N - 1) / 2) = -1, which is the test for a = b ^ 3.
--  * test passes => prime: in (ZMod q)[X] / (X ^ 2 - s X + 1), for a prime factor q of N, the root has
--    order 2 ^ n and Frobenius maps it to itself or to its inverse, so 2 ^ n divides q - 1 or q + 1;
--    this is impossible for the least prime factor of a composite N.

namespace OMA.P141308

open OMA.S_mse_141308 Polynomial


lemma S_eq {R : Type*} [CommRing R] {N s : ℕ} (f : ZMod N →+* R) {a b : R}
    (hab : a * b = 1) (hs : a + b = (s : R)) (i : ℕ) :
    f (S N s i) = a ^ 2 ^ i + b ^ 2 ^ i := by
  induction i with
  | zero => simp [S, hs]
  | succ i ih =>
    have h1 : a ^ 2 ^ i * b ^ 2 ^ i = 1 := by rw [← mul_pow, hab, one_pow]
    change f (S N s i ^ 2 - 2) = _
    rw [map_sub, map_pow, ih, map_ofNat, pow_succ 2 i, pow_mul, pow_mul]
    linear_combination 2 * h1

lemma isUnit_pow_sub_one {R : Type*} [CommRing R] {a : R} {k : ℕ} (h2 : IsUnit (2 : R))
    (ha : a ^ 2 ^ k = -1) {j : ℕ} (hj : ¬ 2 ^ (k + 1) ∣ j) : IsUnit (a ^ j - 1) := by
  have hj0 : j ≠ 0 := fun h => hj (h ▸ dvd_zero _)
  obtain ⟨i, t, ht, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hj0
  have hik : i ≤ k := by
    by_contra hcon
    exact hj (Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) t)
  have hpow : (a ^ (2 ^ i * t)) ^ 2 ^ (k - i) = -1 := by
    rw [← pow_mul, mul_right_comm, ← pow_add, Nat.add_sub_cancel' hik, pow_mul, ha, ht.neg_one_pow]
  have hdvd : a ^ (2 ^ i * t) - 1 ∣ (a ^ (2 ^ i * t)) ^ 2 ^ (k - i) - 1 := by
    simpa using sub_dvd_pow_sub_pow (a ^ (2 ^ i * t)) 1 (2 ^ (k - i))
  rw [hpow] at hdvd
  refine isUnit_of_dvd_unit hdvd ?_
  have : (-1 - 1 : R) = -2 := by ring
  rw [this]; exact h2.neg

/-- A prime factor `q` of `N` for which the test passes satisfies `2 ^ n ≤ q + 1`. -/
lemma two_pow_le {N q n s : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2) (hqN : q ∣ N) (hn : 2 ≤ n)
    (h0 : S N s (n - 2) = 0) : 2 ^ n ≤ q + 1 := by
  set f : (ZMod q)[X] := C 1 * X ^ 2 + C (-(s : ZMod q)) * X + C 1 with hf
  have : Nontrivial (AdjoinRoot f) :=
    AdjoinRoot.nontrivial f (by rw [hf, degree_quadratic one_ne_zero]; decide)
  set α : AdjoinRoot f := AdjoinRoot.root f with hα
  set β : AdjoinRoot f := (s : AdjoinRoot f) - α with hβ
  have hroot : α ^ 2 - (s : AdjoinRoot f) * α + 1 = 0 := by
    have h := AdjoinRoot.mk_self (f := f)
    rw [hf] at h
    simpa [sub_eq_add_neg] using h
  have hab : α * β = 1 := by rw [hβ]; linear_combination -hroot
  have hs : α + β = (s : AdjoinRoot f) := by rw [hβ]; ring
  have hS := S_eq ((AdjoinRoot.of f).comp (ZMod.castHom hqN (ZMod q))) hab hs (n - 2)
  rw [h0, map_zero] at hS
  have h1 : α ^ 2 ^ (n - 2) * β ^ 2 ^ (n - 2) = 1 := by rw [← mul_pow, hab, one_pow]
  have hk : α ^ 2 ^ (n - 1) = -1 := by
    have e : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by rw [← pow_succ]; congr 1; omega
    rw [e, pow_mul]
    linear_combination α ^ 2 ^ (n - 2) * hS.symm - h1
  have h2 : IsUnit (2 : AdjoinRoot f) := by
    have h2q : (2 : ZMod q) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).mp this)
    have h3 := (IsUnit.mk0 _ h2q).map (AdjoinRoot.of f)
    rwa [map_ofNat] at h3
  have : CharP (AdjoinRoot f) q :=
    charP_of_injective_algebraMap (algebraMap (ZMod q) (AdjoinRoot f)).injective q
  have : ExpChar (AdjoinRoot f) q := ExpChar.prime hq.out
  have hfrob : (α ^ q) ^ 2 - (s : AdjoinRoot f) * α ^ q + 1 = 0 := by
    have h := congrArg (frobenius (AdjoinRoot f) q) hroot
    simp only [map_sub, map_add, map_mul, map_pow, map_one, map_zero, map_natCast] at h
    simpa [frobenius_def] using h
  have hq1 : 1 ≤ q := hq.out.one_lt.le
  have e1 : α ^ q = α ^ (q - 1) * α := by rw [← pow_succ]; congr 1; omega
  have e2 : α ^ (q + 1) = α ^ (q - 1) * α ^ 2 := by rw [← pow_add]; congr 1; omega
  have hprod : (α ^ (q - 1) - 1) * (α ^ (q + 1) - 1) = 0 := by
    rw [e2]; rw [e1] at hfrob
    linear_combination hfrob - α ^ (q - 1) * hroot
  have hkk : n - 1 + 1 = n := by omega
  by_cases hd : 2 ^ n ∣ q - 1
  · have := Nat.le_of_dvd (by have := hq.out.two_le; omega) hd
    omega
  · have hu := isUnit_pow_sub_one h2 hk (j := q - 1) (by rwa [hkk])
    have hz : α ^ (q + 1) - 1 = 0 := (hu.mul_right_eq_zero).mp hprod
    by_contra hlt
    have hd' : ¬ 2 ^ n ∣ q + 1 := fun h => hlt (Nat.le_of_dvd (by omega) h)
    have hu' := isUnit_pow_sub_one h2 hk (j := q + 1) (by rwa [hkk])
    rw [hz] at hu'
    exact not_isUnit_zero hu'

/-- Sufficiency. -/
lemma prime_of_S_zero {n s : ℕ} (hn : 3 ≤ n) (h0 : S (3 * 2 ^ n + 1) s (n - 2) = 0) :
    (3 * 2 ^ n + 1).Prime := by
  by_contra hNp
  have hT : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hN1 : 3 * 2 ^ n + 1 ≠ 1 := by omega
  have hqp := Nat.minFac_prime hN1
  have : Fact (3 * 2 ^ n + 1).minFac.Prime := ⟨hqp⟩
  have hqq := Nat.minFac_sq_le_self (by omega) hNp
  have hq2 : (3 * 2 ^ n + 1).minFac ≠ 2 := by
    intro h
    have hdvd := Nat.minFac_dvd (3 * 2 ^ n + 1)
    rw [h] at hdvd
    have he : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have hle := two_pow_le hq2 (Nat.minFac_dvd _) (by omega) h0
  nlinarith [hle, hqq, hT]

lemma pow_per {m d e : ℕ} (hper : 2 ^ (e + d) % m = 2 ^ e % m) :
    ∀ t a : ℕ, e ≤ a → 2 ^ (a + d * t) % m = 2 ^ a % m := by
  intro t
  induction t with
  | zero => intro a _; simp
  | succ t ih =>
    intro a ha
    have ha' : a + d * (t + 1) = (a - e + d * t) + (e + d) := by
      rw [Nat.mul_succ]; omega
    rw [ha', pow_add, Nat.mul_mod, hper, ← Nat.mul_mod, ← pow_add]
    have h2 : a - e + d * t + e = a + d * t := by omega
    rw [h2]; exact ih a ha

lemma pow_congr {m d e a b : ℕ} (hper : 2 ^ (e + d) % m = 2 ^ e % m) (ha : e ≤ a) (hb : e ≤ b)
    (hab : a % d = b % d) : 2 ^ a % m = 2 ^ b % m := by
  rcases le_total a b with h | h
  · obtain ⟨t, ht⟩ : d ∣ b - a := (Nat.modEq_iff_dvd' h).mp hab
    have hb' : b = a + d * t := by omega
    rw [hb', pow_per hper t a ha]
  · obtain ⟨t, ht⟩ : d ∣ a - b := (Nat.modEq_iff_dvd' h).mp hab.symm
    have ha' : a = b + d * t := by omega
    rw [ha', pow_per hper t b hb]

/-- The Legendre symbol of `a` modulo the prime `N = 3 * 2 ^ n + 1`, from `n` modulo a period. -/
lemma leg_val {N n : ℕ} [Fact N.Prime] (hN : N = 3 * 2 ^ n + 1) (hodd : Odd N) (a : ℤ)
    {m d e r c : ℕ} (hm : 4 * a.natAbs = m) (hper : 2 ^ (e + d) % m = 2 ^ e % m)
    (he : e ≤ r) (hen : e ≤ n) (hnr : n % d = r % d) (hc : (3 * (2 ^ r % m) + 1) % m = c) :
    legendreSym N a = jacobiSym a c := by
  have key : 2 ^ n ≡ 2 ^ r % m [MOD m] := by
    unfold Nat.ModEq; rw [Nat.mod_mod]; exact pow_congr hper hen he hnr
  have hNm : N % m = c := by rw [hN, ← hc]; exact (key.mul_left 3).add_right 1
  rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.mod_right a hodd, hm, hNm]

/-- Necessity, given the two non-residues `t + 2` and `t - 2`. -/
lemma S_zero_aux {N n s : ℕ} [Fact N.Prime] (hN : N = 3 * 2 ^ n + 1) (hn : 2 ≤ n) (t : ℤ)
    (hs : (s : ZMod N) = (t : ZMod N) ^ 3 - 3 * t)
    (hu : legendreSym N (t + 2) = -1) (hw : legendreSym N (t - 2) = -1) :
    S N s (n - 2) = 0 := by
  have he : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have h2ne : (2 : ZMod N) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod N) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    have hpos : 0 < 2 ^ n := by positivity
    omega
  have hsq : legendreSym N ((t + 2) * (t - 2)) = 1 := by rw [legendreSym.mul, hu, hw]; norm_num
  have hne : (((t + 2) * (t - 2) : ℤ) : ZMod N) ≠ 0 := by
    intro h
    rw [(legendreSym.eq_zero_iff N _).mpr h] at hsq
    norm_num at hsq
  obtain ⟨d, hd⟩ := (legendreSym.eq_one_iff N hne).mp hsq
  have hd' : d * d = (t : ZMod N) ^ 2 - 4 := by rw [← hd]; push_cast; ring
  have h2 : (2 : ZMod N) * 2⁻¹ = 1 := mul_inv_cancel₀ h2ne
  set h : ZMod N := 2⁻¹ with hh
  set β : ZMod N := ((t : ZMod N) + d) * h with hβ
  set βi : ZMod N := ((t : ZMod N) - d) * h with hβi
  have hββ : β * βi = 1 := by
    rw [hβ, hβi]; linear_combination (-(h * h)) * hd' + (2 * h + 1) * h2
  have hβs : β + βi = t := by rw [hβ, hβi]; linear_combination (t : ZMod N) * h2
  have hαα : β ^ 3 * βi ^ 3 = 1 := by rw [← mul_pow, hββ, one_pow]
  have hαs : β ^ 3 + βi ^ 3 = (s : ZMod N) := by
    rw [hs]
    linear_combination ((β + βi) ^ 2 + (β + βi) * t + (t : ZMod N) ^ 2 - 3) * hβs - 3 * (β + βi) * hββ
  have hS := S_eq (RingHom.id (ZMod N)) hαα hαs (n - 2)
  have hβ0 : β ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hββ; exact zero_ne_one hββ
  have hβns : ¬ IsSquare β := by
    rintro ⟨γ, hγ⟩
    have hγ0 : γ ≠ 0 := by
      rintro rfl; rw [mul_zero] at hγ; exact hβ0 hγ
    have hγi : γ * γ⁻¹ = 1 := mul_inv_cancel₀ hγ0
    have hββ' : γ * γ * βi = 1 := by rw [← hγ]; exact hββ
    have hβi' : βi = γ⁻¹ * γ⁻¹ := by
      linear_combination (-βi * (γ * γ⁻¹ + 1)) * hγi + (γ⁻¹ * γ⁻¹) * hββ'
    apply (legendreSym.eq_neg_one_iff N).mp hu
    refine ⟨γ + γ⁻¹, ?_⟩
    push_cast
    linear_combination -hβs + hγ + hβi' - 2 * hγi
  have hE : β ^ (N / 2) = -1 := by
    rcases ZMod.pow_div_two_eq_neg_one_or_one N hβ0 with h1 | h1
    · exact absurd ((ZMod.euler_criterion N hβ0).mpr h1) hβns
    · exact h1
  have hN2 : N / 2 = 3 * 2 ^ (n - 1) := by omega
  have he2 : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by rw [← pow_succ]; congr 1; omega
  have hx2 : ((β ^ 3) ^ 2 ^ (n - 2)) ^ 2 = -1 := by
    rw [← pow_mul, ← pow_mul, ← hE, hN2, he2]
  have hxy : (β ^ 3) ^ 2 ^ (n - 2) * (βi ^ 3) ^ 2 ^ (n - 2) = 1 := by
    rw [← mul_pow, hαα, one_pow]
  rw [RingHom.id_apply] at hS
  rw [hS]
  linear_combination (βi ^ 3) ^ 2 ^ (n - 2) * hx2 - (β ^ 3) ^ 2 ^ (n - 2) * hxy

/-- Necessity. -/
lemma S_zero_of_prime {n : ℕ} (hn : 2 < n)
    (hres : n % 12 = 2 ∨ n % 12 = 6 ∨ n % 12 = 8 ∨ n % 12 = 10 ∨ n % 4 = 1)
    (hp : (3 * 2 ^ n + 1).Prime) : S (3 * 2 ^ n + 1) (seed n) (n - 2) = 0 := by
  have : Fact (3 * 2 ^ n + 1).Prime := ⟨hp⟩
  have he : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have hodd : Odd (3 * 2 ^ n + 1) := Nat.odd_iff.mpr (by omega)
  have L := fun (a : ℤ) (m d e r c : ℕ) (h1 : 4 * a.natAbs = m)
      (h2 : 2 ^ (e + d) % m = 2 ^ e % m) (h3 : e ≤ r) (h4 : e ≤ n) (h5 : n % d = r % d)
      (h6 : (3 * (2 ^ r % m) + 1) % m = c) =>
    leg_val (N := 3 * 2 ^ n + 1) rfl hodd a h1 h2 h3 h4 h5 h6
  by_cases hA : n % 12 = 8
  · -- t = 37
    refine S_zero_aux rfl (by omega) 37 ?_ ?_ ?_
    · simp only [seed, hA, if_true]; push_cast; norm_num
    · have := L 39 156 12 2 8 145 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
      norm_num at this ⊢; exact this
    · have := L 35 140 12 2 8 69 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
      norm_num at this ⊢; exact this
  by_cases hB : n % 4 = 1
  · -- t = 32
    refine S_zero_aux rfl (by omega) 32 ?_ ?_ ?_
    · simp only [seed, hA, hB, if_true, if_false]; push_cast; norm_num
    · rcases (by omega : n % 8 = 5 ∨ n % 8 = 1) with h8 | h8
      · have := L 34 136 8 3 5 97 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
        norm_num at this ⊢; exact this
      · have := L 34 136 8 3 9 41 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
        norm_num at this ⊢; exact this
    · have := L 30 120 4 3 5 97 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
      norm_num at this ⊢; exact this
  by_cases hC : n % 12 = 2
  · -- t = 12
    refine S_zero_aux rfl (by omega) 12 ?_ ?_ ?_
    · simp only [seed, hB, hC, if_true, if_false]; push_cast; norm_num
    · have := L 14 56 3 3 5 41 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
      norm_num at this ⊢; exact this
    · have := L 10 40 4 3 6 33 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
      norm_num at this ⊢; exact this
  · -- t = 28, n % 12 = 6 or 10
    refine S_zero_aux rfl (by omega) 28 ?_ ?_ ?_
    · simp only [seed, hA, hB, hC, if_false]; push_cast; norm_num
    · have := L 30 120 4 3 6 73 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
      norm_num at this ⊢; exact this
    · rcases (by omega : n % 12 = 6 ∨ n % 12 = 10) with h12 | h12
      · have := L 26 104 12 3 6 89 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
        norm_num at this ⊢; exact this
      · have := L 26 104 12 3 10 57 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
        norm_num at this ⊢; exact this

end OMA.P141308

theorem OMA.solution : type_of% @OMA.S_mse_141308.main :=
  fun _ hn hres => ⟨OMA.P141308.S_zero_of_prime hn hres, OMA.P141308.prime_of_S_zero (by omega)⟩
