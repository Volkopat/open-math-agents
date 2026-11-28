import OMAStatements.S_oeis_a158690
import Mathlib

namespace OMA.P_oeis_a158690

open OMA.S_oeis_a158690

/-- Iterated backward difference of a function `f : ℤ → ℤ` with odd steps `1, 3, ..., 2m-1`. -/
private def diffOp : ℕ → (ℤ → ℤ) → (ℤ → ℤ)
  | 0, f, x => f x
  | m + 1, f, x => diffOp m f x - diffOp m f (x - (2 * (m : ℤ) + 1))

private lemma diffOp_eq_sum (m : ℕ) (f : ℤ → ℤ) (x : ℤ) :
    diffOp m f x = ∑ S ∈ (Finset.range m).powerset,
      (-1 : ℤ) ^ S.card * f (x - ∑ i ∈ S, (2 * (i : ℤ) + 1)) := by
  induction m generalizing x with
  | zero => simp [diffOp]
  | succ m ih =>
    rw [diffOp, ih x, ih (x - (2 * (m : ℤ) + 1))]
    have hsplit : (Finset.range (m + 1)).powerset =
        (Finset.range m).powerset ∪ ((Finset.range m).powerset.image (insert m)) := by
      ext S
      simp only [Finset.mem_powerset, Finset.mem_union, Finset.mem_image]
      constructor
      · intro hS
        by_cases hm : m ∈ S
        · right
          refine ⟨S.erase m, ?_, Finset.insert_erase hm⟩
          intro j hj
          have h1 := Finset.mem_range.mp (hS (Finset.mem_of_mem_erase hj))
          have h2 := Finset.ne_of_mem_erase hj
          exact Finset.mem_range.mpr (by omega)
        · left
          intro j hj
          have h1 := Finset.mem_range.mp (hS hj)
          have h2 : j ≠ m := fun h => hm (h ▸ hj)
          exact Finset.mem_range.mpr (by omega)
      · rintro (hS | ⟨T, hT, rfl⟩)
        · exact hS.trans (Finset.range_mono (Nat.le_succ m))
        · intro j hj
          rcases Finset.mem_insert.mp hj with hjm | hjT
          · rw [hjm]; exact Finset.mem_range.mpr (Nat.lt_succ_self m)
          · exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp (hT hjT)))
    have hdisj : Disjoint (Finset.range m).powerset
        ((Finset.range m).powerset.image (insert m)) := by
      rw [Finset.disjoint_left]
      intro S hS1 hS2
      obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hS2
      exact Nat.lt_irrefl m (Finset.mem_range.mp (Finset.mem_powerset.mp hS1 (Finset.mem_insert_self m T)))
    have hinj : Set.InjOn (insert m) ((Finset.range m).powerset : Set (Finset ℕ)) := by
      intro T₁ hT₁ T₂ hT₂ heq
      have hm1 : m ∉ T₁ := fun hm => Nat.lt_irrefl m (Finset.mem_range.mp (Finset.mem_powerset.mp hT₁ hm))
      have hm2 : m ∉ T₂ := fun hm => Nat.lt_irrefl m (Finset.mem_range.mp (Finset.mem_powerset.mp hT₂ hm))
      have := congr_arg (fun s => s.erase m) heq
      simpa [Finset.erase_insert hm1, Finset.erase_insert hm2] using this
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_image hinj, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun T hT => ?_)
    have hmT : m ∉ T := fun hm => Nat.lt_irrefl m (Finset.mem_range.mp (Finset.mem_powerset.mp hT hm))
    rw [Finset.card_insert_of_notMem hmT, Finset.sum_insert hmT, pow_succ]
    ring_nf

private lemma diffOp_zero_eq_w (m n : ℕ) : diffOp m (fun x => x ^ n) 0 = w m n := by
  rw [diffOp_eq_sum]
  simp [w]

private lemma diffOp_add (m : ℕ) (f g : ℤ → ℤ) (x : ℤ) :
    diffOp m (fun t => f t + g t) x = diffOp m f x + diffOp m g x := by
  induction m generalizing x with
  | zero => simp [diffOp]
  | succ m ih => simp only [diffOp, ih]; ring

private lemma diffOp_smul (m : ℕ) (c : ℤ) (f : ℤ → ℤ) (x : ℤ) :
    diffOp m (fun t => c * f t) x = c * diffOp m f x := by
  induction m generalizing x with
  | zero => simp [diffOp]
  | succ m ih => simp only [diffOp, ih]; ring

private lemma diffOp_sum {ι : Type*} (s : Finset ι) (m : ℕ) (f : ι → ℤ → ℤ) (x : ℤ) :
    diffOp m (fun t => ∑ i ∈ s, f i t) x = ∑ i ∈ s, diffOp m (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    induction m generalizing x with
    | zero => simp [diffOp]
    | succ m ih => simp [diffOp, ih]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha, diffOp_add, ih]

private lemma diffOp_step_pow (n : ℕ) (h x : ℤ) :
    x ^ n - (x - h) ^ n =
      ∑ k ∈ Finset.range n, (-((-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * h ^ (n - k))) * x ^ k := by
  have hbin : (x - h) ^ n = ∑ k ∈ Finset.range (n + 1), x ^ k * (-h) ^ (n - k) * (n.choose k : ℤ) := by
    rw [sub_eq_add_neg, add_pow]
  rw [hbin, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
    mul_one, sub_add_eq_sub_sub, sub_right_comm, sub_self, zero_sub, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [neg_eq_neg_one_mul h, mul_pow]
  ring

private lemma diffOp_eq_zero_of_lt : ∀ m n : ℕ, n < m → ∀ x : ℤ, diffOp m (fun t => t ^ n) x = 0 := by
  intro m
  induction m with
  | zero => intro n hn; omega
  | succ m ih =>
    intro n hn x
    have hstep : diffOp (m + 1) (fun t => t ^ n) x =
        diffOp m (fun t => t ^ n - (t - (2 * (m : ℤ) + 1)) ^ n) x := by
      have hcomm : ∀ k (f : ℤ → ℤ) (y : ℤ),
          diffOp (k + 1) f y = diffOp k (fun t => f t - f (t - (2 * (k : ℤ) + 1))) y := by
        intro k f y
        rw [diffOp, diffOp_eq_sum, diffOp_eq_sum, diffOp_eq_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [← mul_sub, sub_right_comm]
      exact hcomm m _ x
    rw [hstep]
    have hfun : (fun t : ℤ => t ^ n - (t - (2 * (m : ℤ) + 1)) ^ n) =
        (fun t : ℤ => ∑ k ∈ Finset.range n,
          (-((-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * (2 * (m : ℤ) + 1) ^ (n - k))) * t ^ k) := by
      funext t; exact diffOp_step_pow n (2 * (m : ℤ) + 1) t
    rw [hfun, diffOp_sum]
    refine Finset.sum_eq_zero (fun k hk => ?_)
    rw [diffOp_smul, ih k (by have := Finset.mem_range.mp hk; omega) x, mul_zero]

private lemma w_eq_zero_of_lt {m n : ℕ} (h : n < m) : w m n = 0 := by
  rw [← diffOp_zero_eq_w]
  exact diffOp_eq_zero_of_lt m n h 0

private lemma a_eq_sum_of_le {n M : ℕ} (h : n ≤ M) :
    a n = ∑ m ∈ Finset.range (M + 1), w m n := by
  unfold a
  refine Finset.sum_subset (Finset.range_mono (by omega)) (fun m _ hnot => ?_)
  have hm : n < m := by simp only [Finset.mem_range] at hnot; omega
  exact w_eq_zero_of_lt hm

private lemma euler_pow_totient_modEq {x : ℤ} {m : ℕ} (hm : m ≠ 0) (hcop : Nat.Coprime x.natAbs m) :
    x ^ m.totient ≡ 1 [ZMOD (m : ℤ)] := by
  have : NeZero m := ⟨hm⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  have hcop_z : IsCoprime x (m : ℤ) :=
    (Int.isCoprime_iff_gcd_eq_one).mpr (by simpa [Int.gcd] using hcop)
  obtain ⟨a, b, hab⟩ := hcop_z
  have hab' := congr_arg (Int.cast (R := ZMod m)) hab
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
    add_zero, Int.cast_one] at hab'
  let u : (ZMod m)ˣ := Units.mkOfMulEqOne (x : ZMod m) (a : ZMod m) (by rw [mul_comm]; exact hab')
  have hu : (u : ZMod m) = (x : ZMod m) := rfl
  rw [← hu, ← Units.val_pow_eq_pow_val, ← ZMod.card_units_eq_totient, pow_card_eq_one]
  simp

private lemma pow_modEq_of_ge {x : ℤ} {k n : ℕ} (hk : 1 ≤ k) (hn : k ≤ n) :
    x ^ (n + k.totient) ≡ x ^ n [ZMOD (k : ℤ)] := by
  have hk0 : k ≠ 0 := by omega
  have hprod : ∏ p ∈ k.primeFactors, (p ^ k.factorization p : ℕ) = k :=
    Nat.prod_factorization_pow_eq_self hk0
  rw [Int.modEq_iff_dvd]
  have hprod_z : (∏ p ∈ k.primeFactors, ((p ^ k.factorization p : ℕ) : ℤ)) = (k : ℤ) := by
    rw [← Nat.cast_prod, hprod]
  rw [← hprod_z]
  refine Finset.prod_dvd_of_coprime ?_ (fun p hp => ?_)
  · intro p₁ hp₁ p₂ hp₂ hne
    have h1 := Nat.prime_of_mem_primeFactors hp₁
    have h2 := Nat.prime_of_mem_primeFactors hp₂
    have hcop : Nat.Coprime (p₁ ^ k.factorization p₁) (p₂ ^ k.factorization p₂) :=
      ((Nat.coprime_primes h1 h2).mpr hne).pow _ _
    exact (Int.isCoprime_iff_gcd_eq_one).mpr (by exact_mod_cast hcop)
  · rw [← Int.modEq_iff_dvd]
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    set e := k.factorization p
    have hdvd : p ^ e ∣ k := Nat.ordProj_dvd k p
    have htot : (p ^ e).totient ∣ k.totient := Nat.totient_dvd_of_dvd hdvd
    by_cases hpx : (p : ℤ) ∣ x
    · have he_le : e ≤ n := by
        have h1 : e ≤ p ^ e := by
          have : e < 2 ^ e := Nat.lt_two_pow_self
          have : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hpp.two_le e
          omega
        exact h1.trans ((Nat.le_of_dvd (by omega) hdvd).trans hn)
      have h1 : ((p ^ e : ℕ) : ℤ) ∣ x ^ (n + k.totient) := by
        push_cast
        exact (pow_dvd_pow_of_dvd hpx e).trans (pow_dvd_pow x (by omega))
      have h2 : ((p ^ e : ℕ) : ℤ) ∣ x ^ n := by
        push_cast
        exact (pow_dvd_pow_of_dvd hpx e).trans (pow_dvd_pow x he_le)
      rw [Int.modEq_iff_dvd]
      exact dvd_sub h2 h1
    · obtain ⟨q, hq⟩ := htot
      rw [pow_add, hq, pow_mul]
      have hcop' : Nat.Coprime x.natAbs (p ^ e) :=
        (((hpp.coprime_iff_not_dvd).mpr (fun h => hpx (Int.natCast_dvd.mpr h))).symm).pow_right e
      have heuler := euler_pow_totient_modEq (pow_ne_zero e hpp.ne_zero) hcop'
      have hpow1 : (x ^ (p ^ e).totient) ^ q ≡ 1 ^ q [ZMOD ((p ^ e : ℕ) : ℤ)] :=
        heuler.pow q
      rw [one_pow] at hpow1
      simpa using (Int.ModEq.mul_left (x ^ n) hpow1)

private lemma pow_gauss_modEq {x : ℤ} {p n k i : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    x ^ (n * p ^ k + i) ≡ x ^ (n * p ^ (k - 1) + i) [ZMOD ((p ^ k : ℕ) : ℤ)] := by
  by_cases hpx : (p : ℤ) ∣ x
  · have hge : k ≤ n * p ^ (k - 1) + i := by
      have hk_le : k ≤ p ^ (k - 1) := by
        cases k with
        | zero => omega
        | succ m =>
          simp only [Nat.add_sub_cancel]
          have : m < 2 ^ m := Nat.lt_two_pow_self
          have : 2 ^ m ≤ p ^ m := Nat.pow_le_pow_left hp.two_le m
          omega
      have h2 : p ^ (k - 1) ≤ n * p ^ (k - 1) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hge2 : k ≤ n * p ^ k + i := by
      have : p ^ (k - 1) ≤ p ^ k := Nat.pow_le_pow_right hp.pos (Nat.sub_le k 1)
      have : n * p ^ (k - 1) ≤ n * p ^ k := Nat.mul_le_mul_left n this
      omega
    rw [Int.modEq_iff_dvd]
    have h1 : ((p ^ k : ℕ) : ℤ) ∣ x ^ (n * p ^ k + i) := by
      push_cast; exact (pow_dvd_pow_of_dvd hpx k).trans (pow_dvd_pow x hge2)
    have h2 : ((p ^ k : ℕ) : ℤ) ∣ x ^ (n * p ^ (k - 1) + i) := by
      push_cast; exact (pow_dvd_pow_of_dvd hpx k).trans (pow_dvd_pow x hge)
    exact dvd_sub h2 h1
  · have hdiff : n * p ^ k + i = (n * p ^ (k - 1) + i) + n * (p ^ k).totient := by
      rw [Nat.totient_prime_pow hp (by omega)]
      have hpk : p ^ k = p ^ (k - 1) * p := by
        conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ]
      have hle : p ^ (k - 1) ≤ p ^ k := Nat.pow_le_pow_right hp.pos (Nat.sub_le k 1)
      zify [hle, hp.one_le]
      have hpkz : (p : ℤ) ^ k = (p : ℤ) ^ (k - 1) * (p : ℤ) := by exact_mod_cast hpk
      nlinarith
    rw [hdiff, pow_add, pow_mul']
    have hcop' : Nat.Coprime x.natAbs (p ^ k) :=
      (((hp.coprime_iff_not_dvd).mpr (fun h => hpx (Int.natCast_dvd.mpr h))).symm).pow_right k
    have heuler := euler_pow_totient_modEq (pow_ne_zero k hp.ne_zero) hcop'
    have hpow1 : (x ^ (p ^ k).totient) ^ n ≡ 1 ^ n [ZMOD ((p ^ k : ℕ) : ℤ)] := heuler.pow n
    rw [one_pow] at hpow1
    simpa [pow_mul'] using (Int.ModEq.mul_left (x ^ (n * p ^ (k - 1) + i)) hpow1)

private lemma w_modEq_of_ge {m k n : ℕ} (hk : 1 ≤ k) (hn : k ≤ n) :
    w m (n + k.totient) ≡ w m n [ZMOD (k : ℤ)] := by
  unfold w
  refine Int.ModEq.sum (fun S _ => ?_)
  exact Int.ModEq.mul_left _ (pow_modEq_of_ge hk hn)

private lemma w_gauss_modEq {m i p n k : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    w m (n * p ^ k + i) ≡ w m (n * p ^ (k - 1) + i) [ZMOD ((p ^ k : ℕ) : ℤ)] := by
  unfold w
  refine Int.ModEq.sum (fun S _ => ?_)
  exact Int.ModEq.mul_left _ (pow_gauss_modEq hp hn hk)

end OMA.P_oeis_a158690

theorem OMA.solution : type_of% @OMA.S_oeis_a158690.main := by
  open OMA.S_oeis_a158690 OMA.P_oeis_a158690 in
  constructor
  · intro k hk
    refine ⟨k, fun n hn => ?_⟩
    set M := n + k.totient
    rw [a_eq_sum_of_le (show n + k.totient ≤ M by omega),
        a_eq_sum_of_le (show n ≤ M by omega)]
    refine Int.ModEq.sum (fun m _ => ?_)
    exact w_modEq_of_ge hk hn
  · intro i p n k hp hn hk
    have h1 : n * p ^ (k - 1) + i ≤ n * p ^ k + i := by
      have := Nat.pow_le_pow_right hp.pos (Nat.sub_le k 1)
      have := Nat.mul_le_mul_left n this
      omega
    set M := n * p ^ k + i
    rw [a_eq_sum_of_le (show n * p ^ k + i ≤ M by omega),
        a_eq_sum_of_le (show n * p ^ (k - 1) + i ≤ M by omega)]
    refine Int.ModEq.sum (fun m _ => ?_)
    exact w_gauss_modEq hp hn hk
