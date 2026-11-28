import OMAStatements.S_oeis_a000089

namespace OMA.OeisA000089
open ArithmeticFunction OMA.S_oeis_a000089

/-- number of roots of x^2+1 in ZMod n -/
noncomputable def r (n : ℕ) : ℕ := Nat.card {x : ZMod n // x ^ 2 + 1 = 0}

lemma a_eq_r (n : ℕ) (hn : n ≠ 0) : a n = (r n : ℤ) := by
  have : NeZero n := ⟨hn⟩
  simp only [a, ArithmeticFunction.coe_mk, hn, if_false, r]
  congr 1
  rw [← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  refine
    { toFun := fun x => ⟨(x.1 : ZMod n), ?_⟩
      invFun := fun y => ⟨y.1.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hx := x.2
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    have : ((x.1 ^ 2 + 1 : ℕ) : ZMod n) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_of_mod_eq_zero hx.2
    push_cast at this
    exact this
  · simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt _, ?_⟩
    apply Nat.mod_eq_zero_of_dvd
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact y.2
  · intro x
    apply Subtype.ext
    simp only
    have hx := x.2
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    exact ZMod.val_natCast_of_lt hx.1
  · intro y
    apply Subtype.ext
    simp only
    exact ZMod.natCast_zmod_val _

lemma r_mul {m n : ℕ} (h : m.Coprime n) : r (m * n) = r m * r n := by
  unfold r
  rw [← Nat.card_prod]
  apply Nat.card_congr
  let e := ZMod.chineseRemainder h
  refine (Equiv.subtypeEquiv (q := fun y : ZMod m × ZMod n => (y.1 ^ 2 + 1 = 0) ∧ (y.2 ^ 2 + 1 = 0))
    e.toEquiv ?_).trans (Equiv.subtypeProdEquivProd (p := fun x : ZMod m => x ^ 2 + 1 = 0)
      (q := fun x : ZMod n => x ^ 2 + 1 = 0))
  intro x
  have h1 : e (x ^ 2 + 1) = e x ^ 2 + 1 := by simp
  have h2 : (e x ^ 2 + 1 = 0) ↔ ((e x).1 ^ 2 + 1 = 0) ∧ ((e x).2 ^ 2 + 1 = 0) := by
    rw [Prod.ext_iff]; simp
  change _ ↔ ((e x).1 ^ 2 + 1 = 0) ∧ ((e x).2 ^ 2 + 1 = 0)
  rw [← h2, ← h1, map_eq_zero_iff e e.injective]

lemma a_one : a 1 = 1 := by
  simp [a]
  decide

lemma a_mult : IsMultiplicative a := by
  refine ⟨a_one, fun {m n} h => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [a_eq_r _ (by positivity), a_eq_r m hm.ne', a_eq_r n hn.ne', r_mul h]
  push_cast
  ring

lemma root_iff (n : ℕ) (x : ZMod n) : x ^ 2 + 1 = 0 ↔ (n : ℤ) ∣ (x.cast : ℤ) ^ 2 + 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact Iff.rfl

lemma not_dvd_of_root {p : ℕ} (hp : p.Prime) {X : ℤ} (h : (p : ℤ) ∣ X ^ 2 + 1) :
    ¬ (p : ℤ) ∣ X := by
  intro hX
  have h2 : (p : ℤ) ∣ X ^ 2 := dvd_pow hX two_ne_zero
  have h3 : (p : ℤ) ∣ 1 := by
    have := dvd_sub h h2
    simpa using this
  have : p ∣ 1 := by exact_mod_cast h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

lemma not_dvd_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : ¬ (p : ℤ) ∣ 2 := by
  intro h
  have : p ∣ 2 := by exact_mod_cast h
  rcases Nat.prime_two.eq_one_or_self_of_dvd p this with h' | h'
  · exact hp.one_lt.ne' h'
  · exact h2 h'

lemma not_dvd_two_mul {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) {X : ℤ} (h : (p : ℤ) ∣ X ^ 2 + 1) :
    ¬ (p : ℤ) ∣ 2 * X := by
  intro hd
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hd with h' | h'
  · exact not_dvd_two hp h2 h'
  · exact not_dvd_of_root hp h h'

lemma uniq {p k : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hk : 1 ≤ k) {X R : ℤ}
    (hX : (p : ℤ) ^ k ∣ X ^ 2 + 1) (hR : (p : ℤ) ^ k ∣ R ^ 2 + 1) :
    (p : ℤ) ^ k ∣ X - R ∨ (p : ℤ) ^ k ∣ X + R := by
  have hP := Nat.prime_iff_prime_int.mp hp
  have hpX : (p : ℤ) ∣ X ^ 2 + 1 := dvd_trans (dvd_pow_self _ (by omega)) hX
  have hd : (p : ℤ) ^ k ∣ (X - R) * (X + R) := by
    have := dvd_sub hX hR
    rwa [show X ^ 2 + 1 - (R ^ 2 + 1) = (X - R) * (X + R) by ring] at this
  by_cases h1 : (p : ℤ) ∣ X - R
  · have h1' : ¬ (p : ℤ) ∣ X + R := by
      intro h1'
      apply not_dvd_two_mul hp h2 hpX
      have := dvd_add h1 h1'
      rwa [show X - R + (X + R) = 2 * X by ring] at this
    left
    exact (((Prime.coprime_iff_not_dvd hP).mpr h1').pow_left).dvd_of_dvd_mul_right hd
  · right
    exact (((Prime.coprime_iff_not_dvd hP).mpr h1).pow_left).dvd_of_dvd_mul_left hd

lemma hensel {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) {X0 : ℤ} (h0 : (p : ℤ) ∣ X0 ^ 2 + 1) :
    ∀ k, 1 ≤ k → ∃ X : ℤ, (p : ℤ) ^ k ∣ X ^ 2 + 1 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨X0, by simpa using h0⟩
  | succ k hk ih =>
    obtain ⟨X, c, hc⟩ := ih
    have hpX : (p : ℤ) ∣ X ^ 2 + 1 := dvd_trans (dvd_pow_self _ (by omega)) ⟨c, hc⟩
    have hcop : IsCoprime (2 * X) (p : ℤ) :=
      ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr
        (not_dvd_two_mul hp h2 hpX)).symm
    obtain ⟨u, v, huv⟩ := hcop
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine ⟨X + (-c * u) * (p : ℤ) ^ (j + 1), c * v + (c * u) ^ 2 * (p : ℤ) ^ j, ?_⟩
    linear_combination hc + (-(p : ℤ) ^ (j + 1) * c) * huv

lemma exists_root {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h1 : p % 4 = 1) :
    ∀ k, 1 ≤ k → ∃ X : ℤ, (p : ℤ) ^ k ∣ X ^ 2 + 1 := by
  have := Fact.mk hp
  obtain ⟨y, hy⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
  have : y ^ 2 + 1 = 0 := by linear_combination -hy
  exact hensel hp h2 ((root_iff p y).mp this)

lemma r_one_mod {p k : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h1 : p % 4 = 1) (hk : 1 ≤ k) :
    r (p ^ k) = 2 := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨X, hX⟩ := exists_root hp h2 h1 k hk
  have hx : (X : ZMod (p ^ k)) ^ 2 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (X ^ 2 + 1) (p ^ k)).mpr (by exact_mod_cast hX)
    push_cast at this
    exact this
  have hpX : (p : ℤ) ∣ X ^ 2 + 1 := dvd_trans (dvd_pow_self _ (by omega)) hX
  have hne : (X : ZMod (p ^ k)) ≠ -(X : ZMod (p ^ k)) := by
    intro h
    have h' : ((2 * X : ℤ) : ZMod (p ^ k)) = 0 := by
      push_cast
      linear_combination h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
    push_cast at h'
    exact not_dvd_two_mul hp h2 hpX (dvd_trans (dvd_pow_self _ (by omega)) h')
  unfold r
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have : (Finset.univ.filter fun y : ZMod (p ^ k) => y ^ 2 + 1 = 0) =
      {(X : ZMod (p ^ k)), -(X : ZMod (p ^ k))} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hy
      have hY := (root_iff _ y).mp hy
      push_cast at hY
      rcases uniq hp h2 hk hY hX with h | h
      · left
        have h' : (((y.cast : ℤ) - X : ℤ) : ZMod (p ^ k)) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact h
        push_cast at h'
        linear_combination h'
      · right
        have h' : (((y.cast : ℤ) + X : ℤ) : ZMod (p ^ k)) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact h
        push_cast at h'
        linear_combination h'
    · rintro (rfl | rfl)
      · exact hx
      · linear_combination hx
  rw [this, Finset.card_pair hne]

lemma r_three_mod {p k : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (hk : 1 ≤ k) :
    r (p ^ k) = 0 := by
  have := Fact.mk hp
  unfold r
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun ⟨y, hy⟩ => ?_⟩
  have hY := (root_iff _ y).mp hy
  push_cast at hY
  have hp' : (p : ℤ) ∣ (y.cast : ℤ) ^ 2 + 1 := dvd_trans (dvd_pow_self _ (by omega)) hY
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hp'
  push_cast at hp'
  have : IsSquare (-1 : ZMod p) := ⟨((y.cast : ℤ) : ZMod p), by linear_combination -hp'⟩
  exact (ZMod.exists_sq_eq_neg_one_iff.mp this) h3

lemma r_two_pow {k : ℕ} (hk : 2 ≤ k) : r (2 ^ k) = 0 := by
  unfold r
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun ⟨y, hy⟩ => ?_⟩
  have hY := (root_iff _ y).mp hy
  push_cast at hY
  have h4 : ((4 : ℕ) : ℤ) ∣ (y.cast : ℤ) ^ 2 + 1 :=
    dvd_trans (by norm_num; exact pow_dvd_pow 2 hk) hY
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h4
  push_cast at h4
  have key : ∀ z : ZMod 4, z ^ 2 + 1 ≠ 0 := by decide
  exact key _ h4

lemma a_two : a 2 = 1 := by
  simp [a]
  decide

lemma a_pow_odd {p k : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hk : 1 ≤ k) :
    a (p ^ k) = 1 + chi p := by
  rw [a_eq_r _ (pow_ne_zero _ hp.ne_zero)]
  have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left h2
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h
  · rw [r_one_mod hp h2 h hk]
    norm_num [chi, h]
  · rw [r_three_mod hp h hk]
    simp [chi, h]

lemma a_two_pow {k : ℕ} (hk : 2 ≤ k) : a (2 ^ k) = 0 := by
  rw [a_eq_r _ (by positivity), r_two_pow hk]
  simp

/-- Liouville-type sign function. -/
def lam : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else (-1) ^ (cardFactors n), by simp⟩

lemma lam_mult : IsMultiplicative lam := by
  refine ⟨by simp [lam], fun {m n} _ => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [lam]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lam]
  simp only [lam, ArithmeticFunction.coe_mk, mul_ne_zero hm.ne' hn.ne', hm.ne', hn.ne',
    if_false, cardFactors_mul hm.ne' hn.ne', pow_add]

def c (p : ℕ) : ℤ := if p ≠ 2 then 1 + chi p else 1

def C : ArithmeticFunction ℤ := prodPrimeFactors c

def h : ArithmeticFunction ℤ := lam.pmul C

lemma h_mult : IsMultiplicative h := lam_mult.pmul (IsMultiplicative.prodPrimeFactors c)

lemma lam_apply {n : ℕ} (hn : n ≠ 0) : lam n = (-1) ^ (cardFactors n) := by
  simp [lam, hn]

lemma h_apply {n : ℕ} (hn : n ≠ 0) :
    h n = (-1) ^ (cardFactors n) * ∏ p ∈ n.primeFactors, c p := by
  rw [h, pmul_apply, lam_apply hn, C, prodPrimeFactors_apply hn]

lemma h_pow {p k : ℕ} (hp : p.Prime) :
    h (p ^ k) = (-1) ^ k * (if k = 0 then 1 else c p) := by
  have hne : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [h_apply hne, cardFactors_apply_prime_pow hp]
  congr 1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [Nat.primeFactors_prime_pow hk.ne' hp]
    simp [hk.ne']

lemma c_nonneg (p : ℕ) : 0 ≤ c p := by
  unfold c chi
  split_ifs <;> norm_num

lemma abs_h {n : ℕ} (hn : 1 ≤ n) : |h n| = A091400 n := by
  have hne : n ≠ 0 := by omega
  rw [h_apply hne, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Finset.prod_nonneg fun p _ => c_nonneg p), A091400, Finset.prod_filter]
  rfl

lemma conv_two (F G : ℕ → ℤ) (_hF0 : F 0 = 1) (hF1 : F 1 = 1) (hF : ∀ x, F (x + 2) = 0)
    (hG : ∀ y, G y = (-1) ^ y) (m : ℕ) :
    ∑ x ∈ Finset.range (m + 2), F x * G (m + 1 - x) = 0 := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [hF, zero_mul, Finset.sum_const_zero, _hF0, hF1, hG, zero_add, one_mul]
  rw [show m + 1 - (0 + 1) = m by omega, show m + 1 - 0 = m + 1 by omega, pow_succ]
  ring

lemma conv_zero (F G : ℕ → ℤ) (hF0 : F 0 = 1) (hF : ∀ x, F (x + 1) = 0)
    (hG : ∀ y, G (y + 1) = 0) (m : ℕ) :
    ∑ x ∈ Finset.range (m + 2), F x * G (m + 1 - x) = 0 := by
  rw [Finset.sum_range_succ']
  simp [hF, hG]

lemma sum_G (G : ℕ → ℤ) (hG0 : G 0 = 1) (hG : ∀ y, G (y + 1) = 2 * (-1) ^ (y + 1)) (m : ℕ) :
    ∑ x ∈ Finset.range (m + 1), G x = (-1) ^ m := by
  induction m with
  | zero => simp [hG0]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, hG, pow_succ]
    ring

lemma conv_two' (F G : ℕ → ℤ) (hF0 : F 0 = 1) (hF : ∀ x, F (x + 1) = 2) (hG0 : G 0 = 1)
    (hG : ∀ y, G (y + 1) = 2 * (-1) ^ (y + 1)) (m : ℕ) :
    ∑ x ∈ Finset.range (m + 2), F x * G (m + 1 - x) = 0 := by
  rw [Finset.sum_range_succ']
  simp only [hF, hF0, one_mul]
  have e : ∑ x ∈ Finset.range (m + 1), 2 * G (m + 1 - (x + 1)) =
      2 * ∑ x ∈ Finset.range (m + 1), G (m + 1 - 1 - x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    congr 2
    omega
  rw [e, Finset.sum_range_reflect G (m + 1), sum_G G hG0 hG m, show m + 1 - 0 = m + 1 by omega,
    hG, pow_succ]
  ring

lemma ah_one : a * h = 1 := by
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ (a_mult.mul h_mult) _ isMultiplicative_one]
  intro p i hp
  rcases i with _ | m
  · simp [a_mult.map_one, h_mult.map_one]
  rw [ArithmeticFunction.one_apply_ne (by
    intro h1; exact absurd (Nat.pow_eq_one.mp h1) (by simp [hp.one_lt.ne']))]
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => a x * h y), Nat.sum_divisors_prime_pow hp]
  have e : ∑ x ∈ Finset.range (m + 1 + 1), a (p ^ x) * h (p ^ (m + 1) / p ^ x) =
      ∑ x ∈ Finset.range (m + 2), (fun j => a (p ^ j)) x * (fun j => h (p ^ j)) (m + 1 - x) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_range] at hx
    rw [Nat.pow_div (by omega) hp.pos]
  rw [e]
  by_cases h2 : p = 2
  · subst h2
    refine conv_two (fun j => a (2 ^ j)) (fun j => h (2 ^ j)) ?_ ?_ ?_ ?_ m
    · simp [a_mult.map_one]
    · simpa using a_two
    · intro x; exact a_two_pow (by omega)
    · intro y; rw [h_pow hp]; split_ifs <;> simp [c]
  have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left h2
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h4 | h4
  · refine conv_two' (fun j => a (p ^ j)) (fun j => h (p ^ j)) ?_ ?_ ?_ ?_ m
    · simp [a_mult.map_one]
    · intro x; rw [a_pow_odd hp h2 (by omega)]; norm_num [chi, h4]
    · simp [h_mult.map_one]
    · intro y; rw [h_pow hp]; norm_num [c, chi, h2, h4]; ring
  · refine conv_zero (fun j => a (p ^ j)) (fun j => h (p ^ j)) ?_ ?_ ?_ m
    · simp [a_mult.map_one]
    · intro x; rw [a_pow_odd hp h2 (by omega)]; simp [chi, h4]
    · intro y; rw [h_pow hp]; simp [c, chi, h2, h4]

end OMA.OeisA000089

theorem OMA.solution : type_of% @OMA.S_oeis_a000089.main := by
  intro g hg n hn
  have : g = OMA.OeisA000089.h := by
    calc g = 1 * g := (one_mul g).symm
      _ = (OMA.OeisA000089.h * OMA.S_oeis_a000089.a) * g := by
          rw [mul_comm OMA.OeisA000089.h, OMA.OeisA000089.ah_one]
      _ = OMA.OeisA000089.h := by rw [mul_assoc, hg, mul_one]
  rw [this]
  exact OMA.OeisA000089.abs_h hn
