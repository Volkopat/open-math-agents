import OMAStatements.S_oeis_a370102
import Mathlib

namespace A370102Old
/-- original integer form of the sequence -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((Nat.choose (4 * n) k * Nat.choose (5 * n - k - 1) (n - k) : ℕ) : ℤ)

theorem a_eq (n : ℕ) : ((OMA.S_oeis_a370102.a n : ℕ) : ℤ) = a n := by
  simp only [OMA.S_oeis_a370102.a, a]; push_cast; rfl
end A370102Old

/-! Proof of A370102 supercongruence: a(N) = [x^N] F^(4N), F = (1+x)/(1-x); F^(4N) = F(x^p)^(4Q) exp(4N L_p) truncated; harmonic-sum valuation of [x^t] L_p^2 via the Wolstenholme-type lemma S1_D (adapted from lib/Jacobsthal.lean). -/
namespace A370102J
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- `D p e x` : the rational `x` lies in `p^e * ℤ_(p)`. -/
def D (p e : ℕ) (x : ℚ) : Prop :=
  ∃ a : ℤ, ∃ b : ℕ, ¬ p ∣ b ∧ x * (b : ℚ) = (p : ℚ) ^ e * (a : ℚ)

lemma D.zero (e : ℕ) : D p e 0 := ⟨0, 1, hp.out.not_dvd_one, by simp⟩

omit hp in
lemma D.neg {e : ℕ} {x : ℚ} (hx : D p e x) : D p e (-x) := by
  obtain ⟨a, b, hb, h⟩ := hx
  exact ⟨-a, b, hb, by push_cast; linear_combination -h⟩

lemma D.add {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p e y) : D p e (x + y) := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨a', b', hb', h'⟩ := hy
  refine ⟨a * b' + a' * b, b * b', ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · exact hb h1
    · exact hb' h1
  · push_cast
    linear_combination (b' : ℚ) * h + (b : ℚ) * h'

lemma D.sub {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p e y) : D p e (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

lemma D.mul {e f : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p f y) : D p (e + f) (x * y) := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨a', b', hb', h'⟩ := hy
  refine ⟨a * a', b * b', ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · exact hb h1
    · exact hb' h1
  · push_cast
    rw [pow_add]
    linear_combination (y * (b' : ℚ)) * h + ((p : ℚ) ^ e * (a : ℚ)) * h'

omit hp in
lemma D.le {e f : ℕ} {x : ℚ} (hx : D p e x) (hfe : f ≤ e) : D p f x := by
  obtain ⟨a, b, hb, h⟩ := hx
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hfe
  exact ⟨(p : ℤ) ^ c * a, b, hb, by push_cast; rw [h, pow_add]; ring⟩

lemma D.int (z : ℤ) : D p 0 (z : ℚ) := ⟨z, 1, hp.out.not_dvd_one, by simp⟩

lemma D.nat (n : ℕ) : D p 0 (n : ℚ) := ⟨(n : ℤ), 1, hp.out.not_dvd_one, by simp⟩

lemma D.one : D p 0 (1 : ℚ) := ⟨1, 1, hp.out.not_dvd_one, by simp⟩

lemma D.ppow (e : ℕ) : D p e ((p : ℚ) ^ e) := ⟨1, 1, hp.out.not_dvd_one, by simp⟩

lemma D.mul0 {e : ℕ} {x y : ℚ} (hx : D p e x) (hy : D p 0 y) : D p e (x * y) :=
  (hx.mul hy).le (by omega)

lemma D.mul0' {e : ℕ} {x y : ℚ} (hy : D p 0 y) (hx : D p e x) : D p e (y * x) :=
  (hy.mul hx).le (by omega)

omit hp in
lemma D.inv {u : ℕ} (hu : ¬ p ∣ u) : D p 0 ((u : ℚ)⁻¹) := by
  have hu0 : (u : ℚ) ≠ 0 := by
    intro h
    apply hu
    have h0 : u = 0 := by exact_mod_cast h
    rw [h0]; exact dvd_zero p
  exact ⟨1, u, hu, by rw [inv_mul_cancel₀ hu0]; simp⟩

lemma D.sum {ι : Type*} {e : ℕ} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, D p e (f i)) :
    D p e (∑ i ∈ s, f i) :=
  Finset.sum_induction f (D p e) (fun _ _ ha hb => ha.add hb) (D.zero e) h

lemma D.prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, D p 0 (f i)) :
    D p 0 (∏ i ∈ s, f i) :=
  Finset.prod_induction f (D p 0) (fun _ _ ha hb => (ha.mul hb).le (by omega)) D.one h

lemma D.pow {e : ℕ} {x : ℚ} (hx : D p e x) (n : ℕ) : D p (e * n) (x ^ n) := by
  induction n with
  | zero => simpa using (D.one (p := p))
  | succ n ih => rw [pow_succ, Nat.mul_succ]; exact ih.mul hx

lemma D.cancel {e c : ℕ} {x : ℚ} (h : D p (e + c) ((p : ℚ) ^ c * x)) : D p e x := by
  obtain ⟨a, b, hb, h⟩ := h
  refine ⟨a, b, hb, ?_⟩
  have hpc : ((p : ℚ) ^ c) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  apply mul_left_cancel₀ hpc
  rw [pow_add] at h
  linear_combination h

lemma D.ucancel {e u : ℕ} {x : ℚ} (hu : ¬ p ∣ u) (h : D p e ((u : ℚ) * x)) : D p e x := by
  obtain ⟨a, b, hb, h⟩ := h
  refine ⟨a, u * b, ?_, by push_cast; linear_combination h⟩
  intro hd
  rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
  · exact hu h1
  · exact hb h1

lemma D.dvd {e : ℕ} {z : ℤ} (h : D p e (z : ℚ)) : (p : ℤ) ^ e ∣ z := by
  obtain ⟨a, b, hb, h⟩ := h
  have h2 : z * (b : ℤ) = (p : ℤ) ^ e * a := by exact_mod_cast h
  have hc : IsCoprime ((p : ℤ) ^ e) (b : ℤ) := by
    have h3 : Nat.Coprime (p ^ e) b :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hb)
    have h4 := Nat.isCoprime_iff_coprime.mpr h3
    simpa using h4
  exact hc.dvd_of_dvd_mul_right ⟨a, h2⟩

/-! ### index sets -/

/-- the integers `0 < i < L` prime to `p` -/
def U (p L : ℕ) : Finset ℕ := (Finset.range L).filter (fun i => ¬ p ∣ i)

lemma mem_U {p L i : ℕ} : i ∈ U p L ↔ i < L ∧ ¬ p ∣ i := by
  simp [U]

omit hp in
lemma sum_U_blocks {q : ℕ} (hpq : p ∣ q) (f : ℕ → ℚ) (t : ℕ) :
    ∑ i ∈ U p (t * q), f i = ∑ h ∈ Finset.range t, ∑ u ∈ U p q, f (h * q + u) := by
  induction t with
  | zero => simp [U]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold U
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, add_one_mul,
      Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : p ∣ t * q + x ↔ p ∣ x := Nat.dvd_add_right (dvd_mul_of_dvd_right hpq t)
    simp only [h1]

lemma sum_range_mul_split {M : Type*} [AddCommMonoid M] (m n : ℕ) (hm : 0 < m)
    (f : ℕ → M) :
    ∑ k ∈ Finset.range (m * n), f k =
      ∑ k ∈ (Finset.range (m * n)).filter (fun k => ¬ m ∣ k), f k +
        ∑ c ∈ Finset.range n, f (m * c) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (m * n)) (fun k => m ∣ k), add_comm]
  congr 1
  have h1 : (Finset.range (m * n)).filter (fun k => m ∣ k) =
      (Finset.range n).image (fun c => m * c) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, c, rfl⟩
      exact ⟨c, lt_of_mul_lt_mul_left hk (Nat.zero_le m), rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by nlinarith, dvd_mul_right m c⟩
  rw [h1, Finset.sum_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left hm h

lemma prod_range_mul_split {M : Type*} [CommMonoid M] (m n : ℕ) (hm : 0 < m)
    (f : ℕ → M) :
    ∏ k ∈ Finset.range (m * n), f k =
      (∏ k ∈ (Finset.range (m * n)).filter (fun k => ¬ m ∣ k), f k) *
        ∏ c ∈ Finset.range n, f (m * c) := by
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.range (m * n)) (fun k => m ∣ k), mul_comm]
  congr 1
  have h1 : (Finset.range (m * n)).filter (fun k => m ∣ k) =
      (Finset.range n).image (fun c => m * c) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, c, rfl⟩
      exact ⟨c, lt_of_mul_lt_mul_left hk (Nat.zero_le m), rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by nlinarith, dvd_mul_right m c⟩
  rw [h1, Finset.prod_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left hm h

/-! ### binomials as products -/

/-- `Gp n m = ∏_{0 < i < m} (1 - n / i)` (the factor `i = 0` is `1`). -/
def Gp (n : ℚ) (m : ℕ) : ℚ := ∏ i ∈ Finset.range m, (1 - n / (i : ℚ))

omit hp in
lemma choose_mul_eq (n k : ℕ) :
    (n.choose (k + 1) : ℚ) * ((k : ℚ) + 1) = (n : ℚ) * (-1) ^ k * Gp n (k + 1) := by
  induction k with
  | zero => simp [Gp]
  | succ k ih =>
    have h1 : (n.choose (k + 1 + 1) : ℚ) * ((k : ℚ) + 1 + 1) =
        (n.choose (k + 1) : ℚ) * ((n : ℚ) - ((k : ℚ) + 1)) := by
      rcases le_or_gt (k + 1) n with h | h
      · have h2 := congrArg (Nat.cast (R := ℚ)) (Nat.choose_succ_right_eq n (k + 1))
        push_cast [Nat.cast_sub h] at h2
        linarith
      · rw [Nat.choose_eq_zero_of_lt (by omega : n < k + 1 + 1), Nat.choose_eq_zero_of_lt h]
        simp
    have hG : Gp n (k + 1 + 1) = Gp n (k + 1) * (1 - (n : ℚ) / ((k : ℚ) + 1)) := by
      unfold Gp
      rw [Finset.prod_range_succ]
      push_cast
      ring
    have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
    have h3 : (n : ℚ) * (-1) ^ (k + 1) * (Gp n (k + 1) * (1 - (n : ℚ) / ((k : ℚ) + 1))) =
        ((n : ℚ) * (-1) ^ k * Gp n (k + 1)) * (((n : ℚ) - ((k : ℚ) + 1)) / ((k : ℚ) + 1)) := by
      field_simp
      ring
    have h4 : ((n.choose (k + 1) : ℚ) * ((k : ℚ) + 1)) * (((n : ℚ) - ((k : ℚ) + 1)) / ((k : ℚ) + 1)) =
        (n.choose (k + 1) : ℚ) * ((n : ℚ) - ((k : ℚ) + 1)) := by
      field_simp
    push_cast
    rw [hG, h3, ← ih, h4, ← h1]

omit hp in
lemma choose_mul_eq' (n k : ℕ) (hk : 1 ≤ k) :
    (n.choose k : ℚ) * (k : ℚ) = -((n : ℚ) * (-1) ^ k * Gp n k) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := choose_mul_eq n k'
  push_cast
  rw [h, pow_succ]
  ring

/-- `R p x L = ∏_{0 < i < L, p ∤ i} (1 - x / i)` -/
def R (p : ℕ) (x : ℚ) (L : ℕ) : ℚ := ∏ i ∈ U p L, (1 - x / (i : ℚ))

omit hp in
lemma Gp_split (hp0 : 0 < p) (x : ℚ) (j : ℕ) :
    Gp x (p * j) = R p x (p * j) * Gp (x / p) j := by
  unfold Gp R U
  rw [prod_range_mul_split p j hp0]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  push_cast
  rw [div_div]

lemma choose_ratio (hp2 : p ≠ 2) (n j : ℕ) :
    ((p * n).choose (p * j) : ℚ) = (n.choose j : ℚ) * R p ((p * n : ℕ) : ℚ) (p * j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [R, U]
  have hp0 : 0 < p := hp.out.pos
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have h1 := choose_mul_eq' (p * n) (p * j) (by nlinarith)
  have h2 := choose_mul_eq' n j hj
  have h3 := Gp_split hp0 ((p * n : ℕ) : ℚ) j
  have h4 : ((p * n : ℕ) : ℚ) / (p : ℚ) = (n : ℚ) := by
    push_cast
    field_simp
  have h5 : (-1 : ℚ) ^ (p * j) = (-1) ^ j := by
    rw [pow_mul, hodd.neg_one_pow]
  rw [h3, h4, h5] at h1
  have hpj : ((p * j : ℕ) : ℚ) ≠ 0 := by
    have : 0 < p * j := Nat.mul_pos hp0 hj
    positivity
  have hj0 : (j : ℚ) ≠ 0 := by positivity
  have hpq : (p : ℚ) ≠ 0 := by positivity
  apply mul_right_cancel₀ hpj
  rw [h1]
  push_cast
  have h6 : (n : ℚ) * (-1) ^ j * Gp n j = -((n.choose j : ℚ) * (j : ℚ)) := by rw [h2]; ring
  linear_combination (-(p : ℚ) * R p ((p : ℚ) * (n : ℚ)) (p * j)) * h6

/-! ### expansions of `1/(u+a)^j` -/

lemma D.pow0 {x : ℚ} (hx : D p 0 x) (n : ℕ) : D p 0 (x ^ n) :=
  (hx.pow n).le (Nat.zero_le _)

lemma D.two : D p 0 (2 : ℚ) := by simpa using D.nat (p := p) 2

lemma D.three : D p 0 (3 : ℚ) := by simpa using D.nat (p := p) 3

lemma exp1_D {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hv : D p 0 v⁻¹) (ha : D p s a) :
    D p (4 * s) (v⁻¹ - (u⁻¹ - a * u⁻¹ ^ 2 + a ^ 2 * u⁻¹ ^ 3 - a ^ 3 * u⁻¹ ^ 4)) := by
  have h1 : v⁻¹ - (u⁻¹ - a * u⁻¹ ^ 2 + a ^ 2 * u⁻¹ ^ 3 - a ^ 3 * u⁻¹ ^ 4) =
      a ^ 4 * u⁻¹ ^ 4 * v⁻¹ := by
    subst h
    field_simp
    ring
  rw [h1]
  exact (((ha.pow 4).mul0 (hu.pow0 4)).mul0 hv).le (by omega)

lemma exp2_D {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hu' : D p 0 u) (hv : D p 0 v⁻¹) (ha : D p s a) :
    D p (2 * s) (v⁻¹ ^ 2 - (u⁻¹ ^ 2 - 2 * a * u⁻¹ ^ 3)) := by
  have h1 : v⁻¹ ^ 2 - (u⁻¹ ^ 2 - 2 * a * u⁻¹ ^ 3) =
      a ^ 2 * ((3 * u + 2 * a) * u⁻¹ ^ 3 * v⁻¹ ^ 2) := by
    subst h
    field_simp
    ring
  rw [h1]
  have ha0 : D p 0 a := ha.le (Nat.zero_le _)
  have h2 : D p 0 (3 * u + 2 * a) := (D.three.mul0 hu').add (D.two.mul0 ha0)
  exact ((ha.pow 2).mul0 ((h2.mul0 (hu.pow0 3)).mul0 (hv.pow0 2))).le (by omega)

lemma exp3_D {s : ℕ} {u v a : ℚ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : v = u + a)
    (hu : D p 0 u⁻¹) (hu' : D p 0 u) (hv : D p 0 v⁻¹) (ha : D p s a) :
    D p (2 * s) (v⁻¹ ^ 3 - (u⁻¹ ^ 3 - 3 * a * u⁻¹ ^ 4)) := by
  have h1 : v⁻¹ ^ 3 - (u⁻¹ ^ 3 - 3 * a * u⁻¹ ^ 4) =
      a ^ 2 * ((2 * (3 * u ^ 2) + 2 * (2 * (2 * (u * a))) + 3 * a ^ 2) * u⁻¹ ^ 4 * v⁻¹ ^ 3) := by
    subst h
    field_simp
    ring
  rw [h1]
  have ha0 : D p 0 a := ha.le (Nat.zero_le _)
  have h2 : D p 0 (2 * (3 * u ^ 2) + 2 * (2 * (2 * (u * a))) + 3 * a ^ 2) :=
    ((D.two.mul0 (D.three.mul0 (hu'.pow0 2))).add
      (D.two.mul0 (D.two.mul0 (D.two.mul0 (hu'.mul0 ha0))))).add (D.three.mul0 (ha0.pow0 2))
  exact ((ha.pow 2).mul0 ((h2.mul0 (hu.pow0 4)).mul0 (hv.pow0 3))).le (by omega)

/-! ### products -/

lemma prod_congr_D {ι : Type*} [DecidableEq ι] {e : ℕ} (s : Finset ι) (f g : ι → ℚ)
    (hf : ∀ i ∈ s, D p 0 (f i)) (hg : ∀ i ∈ s, D p 0 (g i)) (h : ∀ i ∈ s, D p e (f i - g i)) :
    D p e (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using D.zero (p := p) e
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        (f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by ring
    rw [h1]
    have hs : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    exact ((h a (Finset.mem_insert_self a s)).mul0 (D.prod s f fun i hi => hf i (hs i hi))).add
      ((hg a (Finset.mem_insert_self a s)).mul0'
        (ih (fun i hi => hf i (hs i hi)) (fun i hi => hg i (hs i hi)) (fun i hi => h i (hs i hi))))

lemma prod_expand2 {ι : Type*} [DecidableEq ι] (hp2 : ¬ p ∣ 2) (s : Finset ι)
    (a : ι → ℚ) (x : ℚ) (hx : D p 0 x) (ha : ∀ i ∈ s, D p 0 (a i)) :
    ∃ W : ℚ, D p 0 W ∧ ∏ i ∈ s, (1 - x * a i) =
      1 - x * (∑ i ∈ s, a i) + x ^ 2 * (((∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) / 2) +
        x ^ 3 * W := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, D.zero 0, by simp⟩
  | insert b s hb ih =>
    obtain ⟨W, hW, hprod⟩ := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    have hab := ha b (Finset.mem_insert_self b s)
    have hS1 : D p 0 (∑ i ∈ s, a i) :=
      D.sum s a fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hS2 : D p 0 (∑ i ∈ s, a i ^ 2) :=
      D.sum s _ fun i hi => (ha i (Finset.mem_insert_of_mem hi)).pow0 2
    have h2 : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
    have hE : D p 0 (((∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) / 2) := by
      rw [div_eq_mul_inv]
      exact ((hS1.pow0 2).sub hS2).mul0 h2
    refine ⟨W - a b * (((∑ i ∈ s, a i) ^ 2 - ∑ i ∈ s, a i ^ 2) / 2) - x * a b * W, ?_, ?_⟩
    · exact (hW.sub (hab.mul0 hE)).sub ((hx.mul0 hab).mul0 hW)
    · rw [Finset.prod_insert hb, Finset.sum_insert hb, Finset.sum_insert hb, hprod]
      ring

/-! ### symmetries of `U p q` -/

omit hp in
lemma sum_U_reflect {q : ℕ} (hpq : p ∣ q) (f : ℕ → ℚ) :
    ∑ u ∈ U p q, f u = ∑ u ∈ U p q, f (q - u) := by
  symm
  have hmem : ∀ u ∈ U p q, q - u ∈ U p q := by
    intro u hu
    obtain ⟨hlt, hnd⟩ := mem_U.mp hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hnd (dvd_zero p)
    refine mem_U.mpr ⟨by omega, ?_⟩
    intro hd
    have h1 : q - u + u = q := Nat.sub_add_cancel (le_of_lt hlt)
    have h2 : p ∣ q - u + u := by rw [h1]; exact hpq
    exact hnd ((Nat.dvd_add_right hd).mp h2)
  have hinv : ∀ u ∈ U p q, q - (q - u) = u := by
    intro u hu
    obtain ⟨hlt, _⟩ := mem_U.mp hu
    omega
  exact Finset.sum_nbij' (fun u => q - u) (fun u => q - u) hmem hmem hinv hinv
    (fun u _ => rfl)

omit hp in
lemma sum_U_double {q : ℕ} (hp' : p.Prime) (hp2 : ¬ p ∣ 2) (hpq : p ∣ q)
    (hq : Nat.Coprime q 2) (f : ℕ → ℚ) :
    ∑ u ∈ U p q, f (2 * u % q) = ∑ u ∈ U p q, f u := by
  have hinj : Set.InjOn (fun u => 2 * u % q) (U p q : Set ℕ) := by
    intro u hu v hv h
    have hu' := mem_U.mp (Finset.mem_coe.mp hu)
    have hv' := mem_U.mp (Finset.mem_coe.mp hv)
    have h1 : 2 * u ≡ 2 * v [MOD q] := h
    have h2 : u ≡ v [MOD q] := Nat.ModEq.cancel_left_of_coprime hq h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 hu'.1 hv'.1
  have himg : (U p q).image (fun u => 2 * u % q) = U p q := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      have hu' := mem_U.mp hu
      have hq0 : 0 < q := by omega
      refine mem_U.mpr ⟨Nat.mod_lt _ hq0, ?_⟩
      intro hd
      have h3 : p ∣ 2 * u := (Nat.dvd_mod_iff hpq).mp hd
      rcases (Nat.Prime.dvd_mul hp').mp h3 with h4 | h4
      · exact hp2 h4
      · exact hu'.2 h4
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ u ∈ U p q, f (2 * u % q)
      = ∑ w ∈ (U p q).image (fun u => 2 * u % q), f w := by
        rw [Finset.sum_image hinj]
    _ = ∑ u ∈ U p q, f u := by rw [himg]

lemma D_inv_pow_congr {s x y : ℕ} (hx : ¬ p ∣ x) (hy : ¬ p ∣ y)
    (h : D p s ((x : ℚ) - (y : ℚ))) (j : ℕ) :
    D p s (((x : ℚ)⁻¹) ^ j - ((y : ℚ)⁻¹) ^ j) := by
  have hx0 : (x : ℚ) ≠ 0 := by
    intro h0
    apply hx
    have h1 : x = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have hy0 : (y : ℚ) ≠ 0 := by
    intro h0
    apply hy
    have h1 : y = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  have hxx : (x : ℚ) * (x : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hyy : (y : ℚ) * (y : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hy0
  have h1 : D p s ((x : ℚ)⁻¹ - (y : ℚ)⁻¹) := by
    have h2 : (x : ℚ)⁻¹ - (y : ℚ)⁻¹ = -(((x : ℚ) - (y : ℚ)) * ((x : ℚ)⁻¹ * (y : ℚ)⁻¹)) := by
      linear_combination (y : ℚ)⁻¹ * hxx - (x : ℚ)⁻¹ * hyy
    rw [h2]
    exact (h.mul0 (((D.inv hx).mul (D.inv hy)).le (by omega))).neg
  induction j with
  | zero => simpa using D.zero (p := p) s
  | succ j ih =>
    have h3 : ((x : ℚ)⁻¹) ^ (j + 1) - ((y : ℚ)⁻¹) ^ (j + 1) =
        (x : ℚ)⁻¹ * (((x : ℚ)⁻¹) ^ j - ((y : ℚ)⁻¹) ^ j) +
          ((x : ℚ)⁻¹ - (y : ℚ)⁻¹) * ((y : ℚ)⁻¹) ^ j := by ring
    rw [h3]
    exact ((D.inv hx).mul0' ih).add (h1.mul0 ((D.inv hy).pow0 j))

/-! ### power sums over the units below `p^s` -/

/-- `sg p q j = ∑_{0<u<q, p ∤ u} u^(-j)` -/
def sg (p q j : ℕ) : ℚ := ∑ u ∈ U p q, ((u : ℚ)⁻¹) ^ j

lemma sg_scale (hp2 : ¬ p ∣ 2) {s : ℕ} (hs : 1 ≤ s) (j : ℕ) :
    D p s (((2 : ℚ) ^ j - 1) * sg p (p ^ s) j) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hq2 : Nat.Coprime (p ^ s) 2 :=
    Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hp2)
  have h1 : sg p (p ^ s) j = ∑ u ∈ U p (p ^ s), (((2 * u % p ^ s : ℕ) : ℚ)⁻¹) ^ j := by
    unfold sg
    exact (sum_U_double hp.out hp2 hpq hq2 (fun w => ((w : ℚ)⁻¹) ^ j)).symm
  have h2 : D p s (∑ u ∈ U p (p ^ s),
      ((((2 * u % p ^ s : ℕ) : ℚ)⁻¹) ^ j - (((2 * u : ℕ) : ℚ)⁻¹) ^ j)) := by
    apply D.sum
    intro u hu
    have hu' := mem_U.mp hu
    have h2u : ¬ p ∣ 2 * u := by
      intro hd
      rcases (Nat.Prime.dvd_mul hp.out).mp hd with h4 | h4
      · exact hp2 h4
      · exact hu'.2 h4
    have hmod : ¬ p ∣ 2 * u % p ^ s := fun hd => h2u ((Nat.dvd_mod_iff hpq).mp hd)
    apply D_inv_pow_congr hmod h2u
    have h5 : ((2 * u % p ^ s : ℕ) : ℚ) - ((2 * u : ℕ) : ℚ) =
        -((p : ℚ) ^ s * ((2 * u / p ^ s : ℕ) : ℚ)) := by
      have h6 := Nat.div_add_mod (2 * u) (p ^ s)
      have h7 : ((p ^ s * (2 * u / p ^ s) + 2 * u % p ^ s : ℕ) : ℚ) = ((2 * u : ℕ) : ℚ) := by
        rw [h6]
      push_cast at h7 ⊢
      linarith
    rw [h5]
    exact ((D.ppow s).mul0 (D.nat _)).neg
  rw [Finset.sum_sub_distrib, ← h1] at h2
  have h3 : ∑ u ∈ U p (p ^ s), (((2 * u : ℕ) : ℚ)⁻¹) ^ j = ((2 : ℚ)⁻¹) ^ j * sg p (p ^ s) j := by
    unfold sg
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    push_cast
    rw [mul_inv, mul_pow]
  rw [h3] at h2
  have h4 : ((2 : ℚ) ^ j - 1) * sg p (p ^ s) j =
      (2 : ℚ) ^ j * (sg p (p ^ s) j - ((2 : ℚ)⁻¹) ^ j * sg p (p ^ s) j) := by
    have h5 : (2 : ℚ) ^ j * ((2 : ℚ)⁻¹) ^ j = 1 := by
      rw [← mul_pow]; norm_num
    linear_combination (sg p (p ^ s) j) * h5
  rw [h4]
  exact (D.two.pow0 j).mul0' h2

/-- generic shifted sums: `v = u + a` with `a ∈ p^s ℤ_(p)` -/
lemma shift_sums {s : ℕ} (a : ℚ) (ha : D p s a) (v : ℕ → ℚ)
    (hv : ∀ u ∈ U p (p ^ s), v u = (u : ℚ) + a ∧ v u ≠ 0 ∧ D p 0 (v u)⁻¹) :
    D p (4 * s) (∑ u ∈ U p (p ^ s), (v u)⁻¹ -
      (sg p (p ^ s) 1 - a * sg p (p ^ s) 2 + a ^ 2 * sg p (p ^ s) 3 - a ^ 3 * sg p (p ^ s) 4)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 2 -
      (sg p (p ^ s) 2 - 2 * a * sg p (p ^ s) 3)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 3 -
      (sg p (p ^ s) 3 - 3 * a * sg p (p ^ s) 4)) := by
  have hu : ∀ u ∈ U p (p ^ s), (u : ℚ) ≠ 0 ∧ D p 0 ((u : ℚ)⁻¹) := by
    intro u hu
    obtain ⟨_, hnd⟩ := mem_U.mp hu
    refine ⟨?_, D.inv hnd⟩
    intro h0
    apply hnd
    have h1 : u = 0 := by exact_mod_cast h0
    rw [h1]; exact dvd_zero p
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ∑ u ∈ U p (p ^ s), (v u)⁻¹ -
        (sg p (p ^ s) 1 - a * sg p (p ^ s) 2 + a ^ 2 * sg p (p ^ s) 3 - a ^ 3 * sg p (p ^ s) 4) =
        ∑ u ∈ U p (p ^ s), ((v u)⁻¹ - ((u : ℚ)⁻¹ - a * (u : ℚ)⁻¹ ^ 2 + a ^ 2 * (u : ℚ)⁻¹ ^ 3 -
          a ^ 3 * (u : ℚ)⁻¹ ^ 4)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, pow_one]
    rw [h1]
    apply D.sum
    intro u hmem
    obtain ⟨h2, h3, h4⟩ := hv u hmem
    exact exp1_D (hu u hmem).1 h3 h2 (hu u hmem).2 h4 ha
  · have h1 : ∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 2 - (sg p (p ^ s) 2 - 2 * a * sg p (p ^ s) 3) =
        ∑ u ∈ U p (p ^ s), ((v u)⁻¹ ^ 2 - ((u : ℚ)⁻¹ ^ 2 - 2 * a * (u : ℚ)⁻¹ ^ 3)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [h1]
    apply D.sum
    intro u hmem
    obtain ⟨h2, h3, h4⟩ := hv u hmem
    exact exp2_D (hu u hmem).1 h3 h2 (hu u hmem).2 (D.nat u) h4 ha
  · have h1 : ∑ u ∈ U p (p ^ s), (v u)⁻¹ ^ 3 - (sg p (p ^ s) 3 - 3 * a * sg p (p ^ s) 4) =
        ∑ u ∈ U p (p ^ s), ((v u)⁻¹ ^ 3 - ((u : ℚ)⁻¹ ^ 3 - 3 * a * (u : ℚ)⁻¹ ^ 4)) := by
      simp only [sg, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [h1]
    apply D.sum
    intro u hmem
    obtain ⟨h2, h3, h4⟩ := hv u hmem
    exact exp3_D (hu u hmem).1 h3 h2 (hu u hmem).2 (D.nat u) h4 ha
/-! ### derived power sum facts -/

omit hp in
lemma D.congr {e : ℕ} {x y : ℚ} (h : D p e x) (hxy : x = y) : D p e y := hxy ▸ h

lemma sg_D0 (q j : ℕ) : D p 0 (sg p q j) :=
  D.sum _ _ fun _ hu => (D.inv (mem_U.mp hu).2).pow0 j

/-- `Eps p ε`: `ε = 0` and `p ∤ 15`, or `ε = 1` and `p = 5`. -/
def Eps (p ε : ℕ) : Prop := (ε = 0 ∧ ¬ p ∣ 15) ∨ (ε = 1 ∧ p = 5)

omit hp in
lemma Eps.le_one {ε : ℕ} (h : Eps p ε) : ε ≤ 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

lemma sg2 (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) : D p s (sg p (p ^ s) 2) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hp3 : ¬ p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h := sg_scale hp2 hs 2
  exact D.ucancel hp3 (h.congr (by push_cast; ring))

lemma sg4 (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) :
    D p s ((p : ℚ) ^ ε * sg p (p ^ s) 4) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hp3 : ¬ p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h := sg_scale hp2 hs 4
  rcases hε with ⟨rfl, h15⟩ | ⟨rfl, h55⟩
  · have h6 : D p s (sg p (p ^ s) 4) := D.ucancel h15 (h.congr (by push_cast; ring))
    exact h6.congr (by ring)
  · have h6 : D p s (((3 : ℕ) : ℚ) * ((p : ℚ) ^ 1 * sg p (p ^ s) 4)) := by
      refine h.congr ?_
      rw [h55]
      push_cast
      ring
    exact D.ucancel hp3 h6

lemma refl_sums {s : ℕ} (hs : 1 ≤ s) :
    D p (4 * s) (2 * sg p (p ^ s) 1 + (p : ℚ) ^ s * sg p (p ^ s) 2 +
      ((p : ℚ) ^ s) ^ 2 * sg p (p ^ s) 3 + ((p : ℚ) ^ s) ^ 3 * sg p (p ^ s) 4) ∧
    D p (2 * s) (2 * sg p (p ^ s) 3 + 3 * (p : ℚ) ^ s * sg p (p ^ s) 4) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hv : ∀ u ∈ U p (p ^ s), (-(((p ^ s - u : ℕ) : ℚ))) = (u : ℚ) + (-(p : ℚ) ^ s) ∧
      (-(((p ^ s - u : ℕ) : ℚ))) ≠ 0 ∧ D p 0 (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ := by
    intro u hu
    obtain ⟨hlt, hnd⟩ := mem_U.mp hu
    have hw : ¬ p ∣ p ^ s - u := by
      intro hd
      have h1 : p ^ s - u + u = p ^ s := Nat.sub_add_cancel (le_of_lt hlt)
      have h2 : p ∣ p ^ s - u + u := by rw [h1]; exact hpq
      exact hnd ((Nat.dvd_add_right hd).mp h2)
    have hw0 : ((p ^ s - u : ℕ) : ℚ) ≠ 0 := by
      have h1 : p ^ s - u ≠ 0 := by omega
      exact_mod_cast h1
    refine ⟨?_, neg_ne_zero.mpr hw0, ?_⟩
    · rw [Nat.cast_sub (le_of_lt hlt)]
      push_cast
      ring
    · rw [inv_neg]
      exact (D.inv hw).neg
  obtain ⟨h1, _, h3⟩ :=
    shift_sums (-(p : ℚ) ^ s) (D.ppow s).neg (fun u => -(((p ^ s - u : ℕ) : ℚ))) hv
  have hr1 : ∑ u ∈ U p (p ^ s), (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ = -sg p (p ^ s) 1 := by
    have h := sum_U_reflect hpq (fun w => (w : ℚ)⁻¹ ^ 1)
    simp only [sg]
    rw [h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [inv_neg, pow_one]
  have hr3 : ∑ u ∈ U p (p ^ s), (-(((p ^ s - u : ℕ) : ℚ)))⁻¹ ^ 3 = -sg p (p ^ s) 3 := by
    have h := sum_U_reflect hpq (fun w => (w : ℚ)⁻¹ ^ 3)
    simp only [sg]
    rw [h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [inv_neg]
    ring
  rw [hr1] at h1
  rw [hr3] at h3
  exact ⟨h1.neg.congr (by ring), h3.neg.congr (by ring)⟩

lemma sg3 (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) :
    D p s (sg p (p ^ s) 3) ∧ D p (2 * s) ((p : ℚ) ^ ε * sg p (p ^ s) 3) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨_, h3⟩ := refl_sums (p := p) hs
  have h4 := sg4 h5 hε hs
  have hσ4 : D p 0 (sg p (p ^ s) 4) := sg_D0 _ _
  constructor
  · have h6 : D p s (((2 : ℕ) : ℚ) * sg p (p ^ s) 3) := by
      have h7 := (h3.le (by omega : s ≤ 2 * s)).sub (D.three.mul0' ((D.ppow s).mul0 hσ4))
      exact h7.congr (by push_cast; ring)
    exact D.ucancel hp2 h6
  · have h6 : D p (2 * s) (((2 : ℕ) : ℚ) * ((p : ℚ) ^ ε * sg p (p ^ s) 3)) := by
      have h7 := (((D.ppow (p := p) ε).le (Nat.zero_le _)).mul0' h3).sub
        (D.three.mul0' (((D.ppow s).mul h4).le (by omega : 2 * s ≤ s + s)))
      exact h7.congr (by push_cast; ring)
    exact D.ucancel hp2 h6

lemma sg1 (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) :
    D p (4 * s) ((p : ℚ) ^ ε * (2 * sg p (p ^ s) 1 + (p : ℚ) ^ s * sg p (p ^ s) 2)) := by
  obtain ⟨h1, _⟩ := refl_sums (p := p) hs
  obtain ⟨_, h3⟩ := sg3 h5 hε hs
  have h4 := sg4 h5 hε hs
  have h7 := ((((D.ppow (p := p) ε).le (Nat.zero_le _)).mul0' h1).sub
    ((((D.ppow s).pow 2).mul h3).le (by omega : 4 * s ≤ s * 2 + 2 * s))).sub
    ((((D.ppow s).pow 3).mul h4).le (by omega : 4 * s ≤ s * 3 + s))
  exact h7.congr (by ring)

lemma trans_sums {s : ℕ} (hs : 1 ≤ s) (h : ℕ) :
    D p (4 * s) (∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ -
      (sg p (p ^ s) 1 - ((h : ℚ) * (p : ℚ) ^ s) * sg p (p ^ s) 2 +
        ((h : ℚ) * (p : ℚ) ^ s) ^ 2 * sg p (p ^ s) 3 -
        ((h : ℚ) * (p : ℚ) ^ s) ^ 3 * sg p (p ^ s) 4)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 2 -
      (sg p (p ^ s) 2 - 2 * ((h : ℚ) * (p : ℚ) ^ s) * sg p (p ^ s) 3)) ∧
    D p (2 * s) (∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 3 -
      (sg p (p ^ s) 3 - 3 * ((h : ℚ) * (p : ℚ) ^ s) * sg p (p ^ s) 4)) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  apply shift_sums ((h : ℚ) * (p : ℚ) ^ s) ((D.nat h).mul0' (D.ppow s))
    (fun u => ((h * p ^ s + u : ℕ) : ℚ))
  intro u hu
  obtain ⟨hlt, hnd⟩ := mem_U.mp hu
  have hw : ¬ p ∣ h * p ^ s + u :=
    fun hd => hnd ((Nat.dvd_add_right (dvd_mul_of_dvd_right hpq h)).mp hd)
  refine ⟨by push_cast; ring, ?_, D.inv hw⟩
  intro h0
  have h1 : h * p ^ s + u = 0 := by exact_mod_cast h0
  apply hw
  rw [h1]
  exact dvd_zero p

/-- `h_1(t q) = -(q t^2 / 2) H_2(q)` to precision `4s - ε` -/
lemma hs1_blocks (h5 : 5 ≤ p) {ε : ℕ} (hε : Eps p ε) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) :
    D p (4 * s) ((p : ℚ) ^ ε *
      (2 * sg p (t * p ^ s) 1 + (p : ℚ) ^ s * (t : ℚ) ^ 2 * sg p (p ^ s) 2)) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have h1 := sg1 h5 hε hs
  obtain ⟨_, h3⟩ := sg3 h5 hε hs
  have h4 := sg4 h5 hε hs
  have hb : sg p (t * p ^ s) 1 =
      ∑ h ∈ Finset.range t, ∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ := by
    unfold sg
    rw [sum_U_blocks hpq]
    simp only [pow_one]
  rw [hb]
  clear hb
  induction t with
  | zero => exact (D.zero _).congr (by simp)
  | succ t ih =>
    obtain ⟨hT, _, _⟩ := trans_sums (p := p) hs t
    have hpe : D p 0 ((p : ℚ) ^ ε) := (D.ppow ε).le (Nat.zero_le _)
    have htq : D p s ((t : ℚ) * (p : ℚ) ^ s) := (D.nat t).mul0' (D.ppow s)
    have h7 := ih.add ((((D.two.mul0' (hpe.mul0' hT)).add h1).add
      (D.two.mul0' (((htq.pow 2).mul h3).le (by omega : 4 * s ≤ s * 2 + 2 * s)))).sub
      (D.two.mul0' (((htq.pow 3).mul h4).le (by omega : 4 * s ≤ s * 3 + s))))
    refine h7.congr ?_
    rw [Finset.sum_range_succ]
    push_cast
    ring

/-- `h_2(t q) = t H_2(q)` to precision `2s` -/
lemma hs2_blocks (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) :
    D p (2 * s) (sg p (t * p ^ s) 2 - (t : ℚ) * sg p (p ^ s) 2) := by
  have hpq : p ∣ p ^ s := dvd_pow_self p (by omega)
  have hε : Eps p (if p = 5 then 1 else 0) := by
    by_cases h : p = 5
    · right; simp [h]
    · left
      refine ⟨by simp [h], ?_⟩
      intro hd
      have h15 : (15 : ℕ) = 3 * 5 := by norm_num
      rw [h15] at hd
      rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
      · have := Nat.le_of_dvd (by norm_num) h1; omega
      · have := Nat.le_of_dvd (by norm_num) h1; omega
  obtain ⟨h3, _⟩ := sg3 h5 hε hs
  have hb : sg p (t * p ^ s) 2 =
      ∑ h ∈ Finset.range t, ∑ u ∈ U p (p ^ s), (((h * p ^ s + u : ℕ) : ℚ))⁻¹ ^ 2 := by
    unfold sg
    rw [sum_U_blocks hpq]
  rw [hb]
  clear hb
  induction t with
  | zero => exact (D.zero _).congr (by simp)
  | succ t ih =>
    obtain ⟨_, hT, _⟩ := trans_sums (p := p) hs t
    have h7 := ih.add (hT.sub (D.two.mul0' (((D.nat t).mul0' ((D.ppow s).mul h3)).le
      (by omega : 2 * s ≤ s + s))))
    refine h7.congr ?_
    rw [Finset.sum_range_succ]
    push_cast
    ring

/-! ### the non-unit part: auxiliary sums -/

lemma exists_eps (h5 : 5 ≤ p) : ∃ ε, Eps p ε := by
  by_cases h : p = 5
  · exact ⟨1, Or.inr ⟨rfl, h⟩⟩
  · refine ⟨0, Or.inl ⟨rfl, ?_⟩⟩
    intro hd
    have h15 : (15 : ℕ) = 3 * 5 := by norm_num
    rw [h15] at hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
    · have := Nat.le_of_dvd (by norm_num) h1
      omega
    · have := Nat.le_of_dvd (by norm_num) h1
      omega

lemma sg1' (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) : D p (2 * s) (sg p (p ^ s) 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨ε, hε⟩ := exists_eps (p := p) h5
  have hε1 := hε.le_one
  have h1 := sg1 h5 hε hs
  have h2 : D p (4 * s - ε) (2 * sg p (p ^ s) 1 + (p : ℚ) ^ s * sg p (p ^ s) 2) := by
    apply D.cancel (c := ε)
    rw [show 4 * s - ε + ε = 4 * s by omega]
    exact h1
  have h6 : D p (2 * s) (((2 : ℕ) : ℚ) * sg p (p ^ s) 1) := by
    have h7 := (h2.le (by omega : 2 * s ≤ 4 * s - ε)).sub
      (((D.ppow s).mul (sg2 h5 hs)).le (by omega : 2 * s ≤ s + s))
    exact h7.congr (by push_cast; ring)
  exact D.ucancel hp2 h6
/-! ### Wolstenholme type sums below `t p^s` -/

lemma S1_D (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) : D p (2 * s) (sg p (t * p ^ s) 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨ε, hε⟩ := exists_eps (p := p) h5
  have hε1 := hε.le_one
  have h1 := hs1_blocks h5 hε hs t
  have h2 : D p (4 * s - ε)
      (2 * sg p (t * p ^ s) 1 + (p : ℚ) ^ s * (t : ℚ) ^ 2 * sg p (p ^ s) 2) := by
    apply D.cancel (c := ε)
    rw [show 4 * s - ε + ε = 4 * s by omega]
    exact h1
  have h6 : D p (2 * s) (((2 : ℕ) : ℚ) * sg p (t * p ^ s) 1) := by
    have h7 := (h2.le (by omega : 2 * s ≤ 4 * s - ε)).sub
      ((((D.ppow s).mul0 ((D.nat t).pow0 2)).mul (sg2 h5 hs)).le (by omega : 2 * s ≤ s + s))
    exact h7.congr (by push_cast; ring)
  exact D.ucancel hp2 h6

lemma S2_D (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (t : ℕ) : D p s (sg p (t * p ^ s) 2) := by
  have h := (hs2_blocks h5 hs t).le (by omega : s ≤ 2 * s)
  exact (h.add ((D.nat t).mul0' (sg2 h5 hs))).congr (by ring)

end A370102J

namespace A370102P
open PowerSeries Finset

noncomputable def th (f : ℚ⟦X⟧) : ℚ⟦X⟧ := mk fun n => (n : ℚ) * coeff n f

lemma coeff_th (f : ℚ⟦X⟧) (n : ℕ) : coeff n (th f) = (n : ℚ) * coeff n f := by
  simp [th]

lemma th_add (f g : ℚ⟦X⟧) : th (f + g) = th f + th g := by
  ext n; simp [coeff_th]; ring

lemma th_sub (f g : ℚ⟦X⟧) : th (f - g) = th f - th g := by
  ext n; simp [coeff_th]; ring

lemma th_Cmul (c : ℚ) (f : ℚ⟦X⟧) : th (C c * f) = C c * th f := by
  ext n; simp [coeff_th]; ring

lemma th_one : th (1 : ℚ⟦X⟧) = 0 := by
  ext n; rw [coeff_th, coeff_one]; split_ifs with h <;> simp [h]

lemma th_X : th (X : ℚ⟦X⟧) = X := by
  ext n; rw [coeff_th, coeff_X]; split_ifs with h <;> simp [h]

lemma th_mul (f g : ℚ⟦X⟧) : th (f * g) = th f * g + f * th g := by
  ext n
  rw [coeff_th, map_add, coeff_mul, coeff_mul, coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.1 + x.2 = n := by simpa using hx
  rw [coeff_th, coeff_th, ← hx']; push_cast; ring

lemma th_pow (f : ℚ⟦X⟧) (k : ℕ) : th (f ^ (k + 1)) = C ((k + 1 : ℕ) : ℚ) * f ^ k * th f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, th_mul, ih]
    have : C (((k + 1 + 1 : ℕ)) : ℚ) = C ((k + 1 : ℕ) : ℚ) + 1 := by
      rw [← map_one C, ← map_add]; push_cast; ring_nf
    rw [this]; ring

/-- the odd indicator series `x + x^3 + x^5 + ...` -/
noncomputable def S : ℚ⟦X⟧ := mk fun n => if n % 2 = 1 then 1 else 0

lemma hS : (1 - X ^ 2) * S = X := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_X]
  rcases n with _ | _ | n
  · simp [S]
  · simp [S]
  · have h2 : (n + 1 + 1) % 2 = n % 2 := by omega
    simp [S, h2]

noncomputable def G0 : ℚ⟦X⟧ := mk 1

noncomputable def F : ℚ⟦X⟧ := (1 + X) * G0

lemma hG : G0 * (1 - X) = 1 := by unfold G0; exact mk_one_mul_one_sub_eq_one ℚ

lemma ne0 (f : ℚ⟦X⟧) (h : constantCoeff f ≠ 0) : f ≠ 0 := by
  intro h0; apply h; rw [h0]; simp

lemma thF : th F = C (2 : ℚ) * S * F := by
  have hdG : th G0 * (1 - X) = X * G0 := by
    have := congrArg th hG
    rw [th_mul, th_sub, th_one, th_X] at this
    linear_combination this
  have hthF : th F = X * G0 + (1 + X) * th G0 := by
    rw [show F = (1 + X) * G0 from rfl, th_mul, th_add, th_one, th_X]; ring
  have key : ((1 - X) ^ 2 * (1 + X)) * (th F - C (2 : ℚ) * S * F) = 0 := by
    have h2 : (C (2 : ℚ) : ℚ⟦X⟧) = 2 := by rw [map_ofNat]
    have hFdef : F = (1 + X) * G0 := rfl
    rw [h2]
    linear_combination (1 - X) ^ 2 * (1 + X) * hthF + (1 - X) * (1 + X) ^ 2 * hdG
      - 2 * (1 - X) ^ 2 * (1 + X) * S * hFdef - 2 * (1 - X) * (1 + X) * G0 * hS
  rcases mul_eq_zero.mp key with h | h
  · exfalso; revert h; apply ne0; simp
  · exact sub_eq_zero.mp h

lemma thFpow (k : ℕ) : th (F ^ k) = C (2 * (k : ℚ)) * S * F ^ k := by
  rcases k with _ | k
  · simp [th_one]
  · rw [th_pow, thF, pow_succ]
    have : C (2 * ((k + 1 : ℕ) : ℚ)) = C ((k + 1 : ℕ) : ℚ) * C (2 : ℚ) := by
      rw [← map_mul]; ring_nf
    rw [this]; ring

lemma coeff_one_add_X_pow (k n : ℕ) : coeff n ((1 + X : ℚ⟦X⟧) ^ k) = (k.choose n : ℚ) := by
  induction k generalizing n with
  | zero => rw [pow_zero, coeff_one]; rcases n with _ | n <;> simp
  | succ k ih =>
    rw [show (1 + X : ℚ⟦X⟧) ^ (k + 1) = (1 + X) ^ k + X * (1 + X) ^ k by ring, map_add]
    rcases n with _ | n
    · simp [ih]
    · rw [coeff_succ_X_mul, ih, ih, Nat.choose_succ_succ']; push_cast; ring

lemma coeffA (m : ℕ) (hm : 1 ≤ m) : coeff m (F ^ (4 * m)) = (A370102Old.a m : ℚ) := by
  have h1 : F ^ (4 * m) = (1 + X) ^ (4 * m) * (PowerSeries.mk fun n => ((4 * m - 1 + n).choose (4 * m - 1) : ℚ)) := by
    rw [show F = (1 + X) * PowerSeries.mk 1 from rfl, mul_pow, ← mk_one_pow_eq_mk_choose_add]
    congr 2; omega
  rw [h1, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
    coeff i ((1 + X : ℚ⟦X⟧) ^ (4 * m)) * coeff j (PowerSeries.mk fun n => ((4 * m - 1 + n).choose (4 * m - 1) : ℚ)))]
  unfold A370102Old.a
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [coeff_one_add_X_pow, coeff_mk]
  congr 2
  rw [show 5 * m - k - 1 = (4 * m - 1) + (m - k) by omega, Nat.choose_symm_add]

/-! ### part 2 -/

lemma constF : constantCoeff F = 1 := by
  simp [F, G0]

noncomputable def Lp (p : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if n % 2 = 1 ∧ ¬ p ∣ n then 2 / (n : ℚ) else 0

lemma th_expand (p : ℕ) (hp : p ≠ 0) (f : ℚ⟦X⟧) :
    th (expand p hp f) = C (p : ℚ) * expand p hp (th f) := by
  ext n
  rw [coeff_th, coeff_C_mul, coeff_expand, coeff_expand]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp), coeff_th]; push_cast; ring
  · simp

lemma thL (p : ℕ) (hp : p ≠ 0) (hp2 : p % 2 = 1) :
    th (Lp p) = C (2 : ℚ) * (S - expand p hp S) := by
  ext n
  rw [coeff_th, coeff_C_mul, map_sub, coeff_expand]
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    rw [if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]
    have h1 : p * m % 2 = m % 2 := by rw [Nat.mul_mod, hp2]; simp
    simp [Lp, S, h1]
  · rw [if_neg hpn]
    by_cases ho : n % 2 = 1
    · have hn0 : (n : ℚ) ≠ 0 := by
        have : n ≠ 0 := by omega
        exact_mod_cast this
      simp [Lp, S, ho, hpn]; field_simp
    · simp [Lp, S, ho]

noncomputable def cc (lam : ℚ) (j : ℕ) : ℚ := lam ^ j / (j.factorial : ℚ)

noncomputable def E (lam : ℚ) (L : ℚ⟦X⟧) (K : ℕ) : ℚ⟦X⟧ :=
  ∑ j ∈ range (K + 1), C (cc lam j) * L ^ j

lemma E_succ (lam : ℚ) (L : ℚ⟦X⟧) (K : ℕ) :
    E lam L (K + 1) = E lam L K + C (cc lam (K + 1)) * L ^ (K + 1) := by
  unfold E; rw [Finset.sum_range_succ]

lemma thE (lam : ℚ) (L : ℚ⟦X⟧) (K : ℕ) :
    th (E lam L K) = C lam * th L * (E lam L K - C (cc lam K) * L ^ K) := by
  induction K with
  | zero => simp [E, cc, th_one]
  | succ K ih =>
    have hc : C (cc lam (K + 1)) * C (((K + 1 : ℕ)) : ℚ) = C lam * C (cc lam K) := by
      rw [← map_mul, ← map_mul]; congr 1; unfold cc; rw [Nat.factorial_succ]; push_cast
      field_simp; ring
    rw [E_succ, th_add, th_Cmul, th_pow, ih]
    linear_combination (L ^ K * th L) * hc

lemma uniq (M R D : ℚ⟦X⟧) (K : ℕ) (hD0 : coeff 0 D = 0) (hM : coeff 0 M = 0)
    (hth : th D = M * D + R) (hR : ∀ n ≤ K, coeff n R = 0) : ∀ n ≤ K, coeff n D = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]; exact hD0
    · have h1 := congrArg (coeff n) hth
      rw [coeff_th, map_add, hR n hn, add_zero, coeff_mul] at h1
      have h2 : ∑ x ∈ antidiagonal n, coeff x.1 M * coeff x.2 D = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hx' : x.1 + x.2 = n := by simpa using hx
        by_cases hx1 : x.1 = 0
        · rw [hx1, hM, zero_mul]
        · rw [ih x.2 (by omega) (by omega), mul_zero]
      rw [h2] at h1
      have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
      exact (mul_eq_zero.mp h1).resolve_left hn0

lemma coeff_low (R : ℚ⟦X⟧) (K : ℕ) (h : X ^ (K + 1) ∣ R) : ∀ n ≤ K, coeff n R = 0 := by
  intro n hn
  obtain ⟨g, rfl⟩ := h
  rw [coeff_X_pow_mul', if_neg (by omega)]

lemma X_dvd_of (f : ℚ⟦X⟧) (h : coeff 0 f = 0) : X ∣ f := by
  rw [X_dvd_iff]; simpa using h

/-- the exp identity, truncated -/
lemma main_id (p Q N : ℕ) (hp : p ≠ 0) (hp2 : p % 2 = 1) (hN : N = p * Q) :
    coeff N (F ^ (4 * N)) =
      coeff N (expand p hp (F ^ (4 * Q)) * E (4 * (N : ℚ)) (Lp p) N) := by
  set B := expand p hp (F ^ (4 * Q))
  set lam : ℚ := 4 * (N : ℚ)
  set EE := E lam (Lp p) N
  set Sp := expand p hp S
  set r := C (cc lam N) * (Lp p) ^ N
  set k8 : ℚ := 2 * ((4 * N : ℕ) : ℚ)
  have hA : th (F ^ (4 * N)) = C k8 * S * F ^ (4 * N) := thFpow (4 * N)
  have hB : th B = C k8 * Sp * B := by
    simp only [B, Sp]
    rw [th_expand, thFpow, map_mul, map_mul, expand_C]
    have : C (p : ℚ) * C (2 * ((4 * Q : ℕ) : ℚ)) = (C k8 : ℚ⟦X⟧) := by
      rw [← map_mul]; congr 1; simp only [k8]; rw [hN]; push_cast; ring
    rw [← this]; ring
  have hE : th EE = C lam * th (Lp p) * (EE - r) := thE lam (Lp p) N
  have hL : th (Lp p) = C (2 : ℚ) * (S - Sp) := thL p hp hp2
  have hc : C lam * C (2 : ℚ) = (C k8 : ℚ⟦X⟧) := by
    rw [← map_mul]; congr 1; simp only [lam, k8]; push_cast; ring
  have hth : th (F ^ (4 * N) - B * EE) =
      C k8 * S * (F ^ (4 * N) - B * EE) + C k8 * (S - Sp) * B * r := by
    rw [th_sub, th_mul, hA, hB, hE, hL]
    linear_combination (-(S - Sp) * B * (EE - r)) * hc
  have hR : ∀ n ≤ N, coeff n (C k8 * (S - Sp) * B * r) = 0 := by
    apply coeff_low
    obtain ⟨g2, hg2⟩ : X ∣ (S - Sp) := X_dvd_of _ (by simp [Sp, S])
    have h2 : X ∣ Lp p := X_dvd_of _ (by simp [Lp])
    obtain ⟨g1, hg1⟩ : X ^ N ∣ (Lp p) ^ N := pow_dvd_pow_of_dvd h2 N
    refine ⟨C k8 * B * C (cc lam N) * g1 * g2, ?_⟩
    simp only [r]; rw [hg1, hg2]; ring
  have hD0 : coeff 0 (F ^ (4 * N) - B * EE) = 0 := by
    have hE0 : constantCoeff EE = 1 := by
      simp only [EE, E, map_sum, map_mul, constantCoeff_C, map_pow]
      rw [Finset.sum_range_succ']
      have : constantCoeff (Lp p) = 0 := by simp [Lp]
      simp [this, cc]
    rw [coeff_zero_eq_constantCoeff_apply, map_sub, map_mul, map_pow, constF, hE0]
    simp only [B]
    rw [constantCoeff_expand, map_pow, constF]; simp
  have hM : coeff 0 (C k8 * S) = 0 := by simp [S]
  have := uniq _ _ _ N hD0 hM hth hR N le_rfl
  rw [map_sub] at this
  exact sub_eq_zero.mp this


/-! ### part 3: valuations -/
open A370102J

section V
variable {p : ℕ} [hp : Fact p.Prime]

def I0 (p : ℕ) (f : ℚ⟦X⟧) : Prop := ∀ n, D p 0 (coeff n f)

lemma I0.mul {f g : ℚ⟦X⟧} (hf : I0 p f) (hg : I0 p g) : I0 p (f * g) := by
  intro n; rw [coeff_mul]
  exact D.sum _ _ fun x _ => (hf x.1).mul0 (hg x.2)

lemma I0.pow {f : ℚ⟦X⟧} (hf : I0 p f) (k : ℕ) : I0 p (f ^ k) := by
  induction k with
  | zero =>
    intro n; rw [pow_zero, coeff_one]
    split_ifs
    · exact D.one
    · exact D.zero 0
  | succ k ih => rw [pow_succ]; exact ih.mul hf

lemma I0F : I0 p F := by
  have h1 : I0 p (1 + X) := by
    intro n; rw [map_add, coeff_one, coeff_X]
    split_ifs <;> norm_num <;> first | exact D.one | exact D.zero 0 | exact D.two
  have h2 : I0 p G0 := by intro n; rw [G0, coeff_mk]; exact D.one
  exact h1.mul h2

lemma I0S : I0 p S := by
  intro n; simp only [S, coeff_mk]; split_ifs
  · exact D.one
  · exact D.zero 0

lemma I0exp {f : ℚ⟦X⟧} (hf : I0 p f) (h0 : p ≠ 0) : I0 p (expand p h0 f) := by
  intro n; rw [coeff_expand]; split_ifs
  · exact hf _
  · exact D.zero 0

lemma I0L : I0 p (Lp p) := by
  intro n; simp only [Lp, coeff_mk]; split_ifs with h
  · rw [div_eq_mul_inv]; exact D.two.mul0 (D.inv h.2)
  · exact D.zero 0

lemma L4 {Q α : ℕ} (hQ : p ^ α ∣ Q) (i : ℕ) : D p α ((i : ℚ) * coeff i (F ^ (4 * Q))) := by
  have h := congrArg (coeff i) (thFpow (4 * Q))
  simp only [coeff_th, mul_assoc, coeff_C_mul] at h
  rw [h]
  obtain ⟨m, rfl⟩ := hQ
  exact ((D.ppow α).mul0 ((D.nat (8 * m)).mul0 ((I0S.mul (I0F.pow _)) i))).congr
    (by push_cast; ring)

lemma podd (h5 : 5 ≤ p) : p % 2 = 1 := by
  rcases Nat.Prime.eq_two_or_odd hp.out with h | h
  · omega
  · exact h

lemma coeff_SSp (h5 : 5 ≤ p) (k : ℕ) :
    coeff k (S - expand p hp.out.ne_zero S) = if k % 2 = 1 ∧ ¬ p ∣ k then 1 else 0 := by
  rw [map_sub, coeff_expand]
  by_cases hpn : p ∣ k
  · obtain ⟨m, rfl⟩ := hpn
    rw [if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left _ hp.out.pos]
    have h1 : p * m % 2 = m % 2 := by rw [Nat.mul_mod, podd h5]; simp
    simp [S, h1]
  · rw [if_neg hpn]
    simp [S, hpn]

lemma sum_range_double (g : ℕ → ℚ) (m : ℕ) :
    ∑ i ∈ range (2 * m), g i = ∑ j ∈ range m, (g (2 * j) + g (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

lemma sg_eq (q : ℕ) : sg p q 1 = ∑ i ∈ range q, (if ¬ p ∣ i then (i : ℚ)⁻¹ else 0) := by
  simp [sg, U, Finset.sum_filter]

lemma dval (h5 : 5 ≤ p) {t e q : ℕ} (ht : t = p ^ e * q) (hq : ¬ p ∣ q) (he : 1 ≤ e) :
    D p e (coeff t (Lp p ^ 2)) := by
  have hp2 := podd (p := p) h5
  have hLe : ∀ n, n % 2 = 0 → coeff n (Lp p) = 0 := by
    intro n hn; simp [Lp, hn]
  rcases Nat.mod_two_eq_zero_or_one t with hte | hto
  · -- even case
    have hpe : (p ^ e) % 2 = 1 := by rw [Nat.pow_mod, hp2]; simp
    have hqe : q % 2 = 0 := by
      have := hte; rw [ht, Nat.mul_mod, hpe] at this; omega
    obtain ⟨q', rfl⟩ : 2 ∣ q := Nat.dvd_of_mod_eq_zero hqe
    set m := q' * p ^ e with hm
    have htm : t = 2 * m := by rw [ht, hm]; ring
    have hpt : p ∣ t := by
      rw [ht]; exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
    -- t * d_t via th
    have h1 := congrArg (coeff t) (th_pow (Lp p) 1)
    rw [thL p hp.out.ne_zero hp2, coeff_th] at h1
    have h2 : coeff t (C (((1 + 1 : ℕ)) : ℚ) * Lp p ^ 1 * (C (2 : ℚ) * (S - expand p hp.out.ne_zero S)))
        = 4 * ∑ i ∈ range (t + 1), coeff i (Lp p) := by
      rw [show (C (((1 + 1 : ℕ)) : ℚ) * Lp p ^ 1 * (C (2 : ℚ) * (S - expand p hp.out.ne_zero S)))
          = C (4 : ℚ) * (Lp p * (S - expand p hp.out.ne_zero S)) by
          rw [pow_one, show (4 : ℚ) = ((1 + 1 : ℕ) : ℚ) * 2 by norm_num, map_mul]; ring]
      rw [coeff_C_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i k => coeff i (Lp p) * coeff k (S - expand p hp.out.ne_zero S))]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [coeff_SSp h5]
      by_cases hc : i % 2 = 1 ∧ ¬ p ∣ i
      · have h3 : (t - i) % 2 = 1 := by omega
        have h4 : ¬ p ∣ (t - i) := by
          intro h; apply hc.2
          have := Nat.dvd_sub hpt h
          rwa [show t - (t - i) = i by omega] at this
        rw [if_pos ⟨h3, h4⟩, mul_one]
      · have : coeff i (Lp p) = 0 := by simp [Lp, hc]
        rw [this, zero_mul]
    rw [h2] at h1
    -- the sum of L_i
    have h5' : ∑ i ∈ range (t + 1), coeff i (Lp p) = 2 * sg p t 1 - sg p m 1 := by
      rw [sum_range_succ, hLe t hte, add_zero, htm, sum_range_double, sg_eq, sg_eq,
        sum_range_double, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hL1 : coeff (2 * j) (Lp p) = 0 := hLe _ (by omega)
      have hdj : p ∣ 2 * j ↔ p ∣ j := by
        constructor
        · intro h
          rcases (Nat.Prime.dvd_mul hp.out).mp h with h' | h'
          · exfalso; have := Nat.le_of_dvd (by norm_num) h'; omega
          · exact h'
        · intro h; exact dvd_mul_of_dvd_right h 2
      rw [hL1]
      simp only [Lp, coeff_mk]
      have ho : (2 * j + 1) % 2 = 1 := by omega
      by_cases hj : p ∣ j
      · have hj2 : p ∣ 2 * j := hdj.mpr hj
        by_cases hj1 : p ∣ 2 * j + 1
        · simp [hj, hj2, hj1]
        · simp [hj, hj2, hj1, ho]; push_cast; ring
      · have hj2 : ¬ p ∣ 2 * j := fun h => hj (hdj.mp h)
        by_cases hj1 : p ∣ 2 * j + 1
        · simp [hj, hj2, hj1]; push_cast; ring
        · simp [hj, hj2, hj1, ho]; push_cast; ring
    rw [h5'] at h1
    -- valuations
    have hs1 : D p (2 * e) (sg p t 1) := by
      rw [show t = (2 * q') * p ^ e by rw [ht]; ring]; exact S1_D h5 he _
    have hs2 : D p (2 * e) (sg p m 1) := S1_D h5 he _
    have h6 : D p (e + e) ((p : ℚ) ^ e * ((2 * q' : ℕ) * coeff t (Lp p ^ 2))) := by
      have := (D.nat 4).mul0' ((D.two.mul0' hs1).sub hs2)
      refine (this.le (by omega)).congr ?_
      have htc : ((t : ℕ) : ℚ) = (p : ℚ) ^ e * ((2 * q' : ℕ) : ℚ) := by rw [ht]; push_cast; ring
      rw [htc] at h1
      push_cast at h1 ⊢
      linear_combination -h1
    exact D.ucancel hq (D.cancel h6)
  · -- odd case
    have : coeff t (Lp p ^ 2) = 0 := by
      rw [pow_two, coeff_mul]
      refine Finset.sum_eq_zero fun x hx => ?_
      have hx' : x.1 + x.2 = t := by simpa using hx
      rcases Nat.mod_two_eq_zero_or_one x.1 with h | h
      · rw [hLe _ h, zero_mul]
      · rw [hLe x.2 (by omega), mul_zero]
    rw [this]; exact D.zero e

lemma L5term (h5 : 5 ≤ p) {Q r i s : ℕ} (hr : 1 ≤ r) (hQ : p ^ (r - 1) ∣ Q) (his : i + s = Q) :
    D p r (coeff i (F ^ (4 * Q)) * coeff (p * s) (Lp p ^ 2)) := by
  rcases Nat.eq_zero_or_pos s with hs0 | hs
  · have : coeff (p * s) (Lp p ^ 2) = 0 := by
      rw [hs0, mul_zero, coeff_zero_eq_constantCoeff, map_pow]
      have : constantCoeff (Lp p) = 0 := by simp [Lp]
      rw [this]; simp
    rw [this, mul_zero]; exact D.zero r
  · obtain ⟨β, w, hw, hsw⟩ := Nat.exists_eq_pow_mul_and_not_dvd hs.ne' p hp.out.ne_one
    have hd : D p (β + 1) (coeff (p * s) (Lp p ^ 2)) :=
      dval h5 (by rw [hsw, pow_succ]; ring) hw (by omega)
    by_cases hβ : r - 1 ≤ β
    · exact (((I0F.pow _) i).mul hd).le (by omega)
    · push_neg at hβ
      have hQ1 : p ^ (β + 1) ∣ Q := (pow_dvd_pow p (by omega)).trans hQ
      have hpβs : p ^ β ∣ s := ⟨w, hsw⟩
      have hpβi : p ^ β ∣ i := by
        have := Nat.dvd_sub ((pow_dvd_pow p (Nat.le_succ β)).trans hQ1) hpβs
        rwa [show Q - s = i by omega] at this
      obtain ⟨w', hw'⟩ := hpβi
      have hpw' : ¬ p ∣ w' := by
        intro h
        have h1 : p ^ (β + 1) ∣ i := by rw [hw', pow_succ]; exact mul_dvd_mul_left _ h
        have h2 := Nat.dvd_sub hQ1 h1
        rw [show Q - i = s by omega, hsw, pow_succ] at h2
        exact hw (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos β) h2)
      have h4 := L4 (p := p) hQ i
      rw [hw'] at h4
      have h5' : D p ((r - 1 - β) + β) ((p : ℚ) ^ β * ((w' : ℚ) * coeff (p ^ β * w') (F ^ (4 * Q)))) :=
        (h4.le (by omega)).congr (by push_cast; ring)
      have h6 := D.ucancel hpw' (D.cancel h5')
      rw [hw']
      exact (h6.mul hd).le (by omega)

lemma L5 (h5 : 5 ≤ p) {Q r : ℕ} (hr : 1 ≤ r) (hQ : p ^ (r - 1) ∣ Q) :
    D p r (coeff (p * Q) (expand p hp.out.ne_zero (F ^ (4 * Q)) * Lp p ^ 2)) := by
  rw [coeff_mul]
  refine D.sum _ _ fun x hx => ?_
  have hx' : x.1 + x.2 = p * Q := by simpa using hx
  rw [coeff_expand]
  split_ifs with h1
  · obtain ⟨i, hi⟩ := h1
    have h2 : p ∣ x.2 := (Nat.dvd_add_right (hi ▸ dvd_mul_right p i)).mp (hx' ▸ dvd_mul_right p Q)
    obtain ⟨s, hs⟩ := h2
    have his : i + s = Q := by
      apply Nat.eq_of_mul_eq_mul_left hp.out.pos
      rw [mul_add, ← hi, ← hs]; exact hx'
    rw [hi, Nat.mul_div_cancel_left _ hp.out.pos, hs]
    exact L5term h5 hr hQ his
  · rw [zero_mul]; exact D.zero r

lemma L1zero (Q : ℕ) :
    coeff (p * Q) (expand p hp.out.ne_zero (F ^ (4 * Q)) * Lp p ^ 1) = 0 := by
  rw [pow_one, coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' : x.1 + x.2 = p * Q := by simpa using hx
  rw [coeff_expand]
  split_ifs with h1
  · have h2 : p ∣ x.2 := (Nat.dvd_add_right h1).mp (hx' ▸ dvd_mul_right p Q)
    have : coeff x.2 (Lp p) = 0 := by simp [Lp, h2]
    rw [this, mul_zero]
  · rw [zero_mul]

lemma ccD (h5 : 5 ≤ p) {N r j : ℕ} (hr : 1 ≤ r) (hN : p ^ r ∣ N) (hj : 3 ≤ j) :
    D p (3 * r) (cc (4 * (N : ℚ)) j) := by
  obtain ⟨m, rfl⟩ := hN
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
  set v := padicValNat p (k + 3).factorial with hvdef
  have hv : (p - 1) * v < k + 3 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega)
  have hv2 : v ≤ k := by
    have : 4 * v ≤ (p - 1) * v := Nat.mul_le_mul_right _ (by omega)
    omega
  have hkr : k ≤ r * k := Nat.le_mul_of_pos_left k hr
  obtain ⟨w, hw⟩ : ∃ w, r * (k + 3) = v + 3 * r + w := ⟨r * k - v, by rw [mul_add]; omega⟩
  obtain ⟨u, hu⟩ : p ^ v ∣ (k + 3).factorial := pow_padicValNat_dvd
  have hpu : ¬ p ∣ u := by
    intro h
    apply pow_succ_padicValNat_not_dvd (Nat.factorial_ne_zero (k + 3)) (p := p)
    rw [← hvdef, hu, pow_succ]; exact mul_dvd_mul_left _ h
  refine ⟨((4 * m : ℕ) : ℤ) ^ (k + 3) * (p : ℤ) ^ w, u, hpu, ?_⟩
  have hu0 : (u : ℚ) ≠ 0 := by
    have : u ≠ 0 := by rintro rfl; simp at hu; exact Nat.factorial_ne_zero _ hu
    exact_mod_cast this
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hfac : ((k + 3).factorial : ℚ) = (p : ℚ) ^ v * u := by rw [hu]; push_cast; ring
  have e1 : ((p : ℚ) ^ r) ^ (k + 3) = (p : ℚ) ^ v * (p : ℚ) ^ (3 * r) * (p : ℚ) ^ w := by
    rw [← pow_mul, hw, pow_add, pow_add]
  have hnum : (4 * (((p ^ r * m : ℕ)) : ℚ)) ^ (k + 3) =
      (p : ℚ) ^ v * ((p : ℚ) ^ (3 * r) * (((4 * m : ℕ) : ℚ) ^ (k + 3) * (p : ℚ) ^ w)) := by
    push_cast
    calc (4 * ((p : ℚ) ^ r * m)) ^ (k + 3) = ((p : ℚ) ^ r) ^ (k + 3) * (4 * m) ^ (k + 3) := by ring
      _ = _ := by rw [e1]; ring
  unfold cc
  rw [hnum, hfac]
  push_cast
  field_simp

lemma coeffBE (B L : ℚ⟦X⟧) (lam : ℚ) (K N : ℕ) :
    coeff N (B * E lam L K) = ∑ j ∈ range (K + 1), cc lam j * coeff N (B * L ^ j) := by
  unfold E
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_left_comm, coeff_C_mul]

theorem final (p n r : ℕ) (hpp : p.Prime) (h5 : 5 ≤ p) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    ((p : ℤ) ^ (3 * r)) ∣
      (A370102Old.a (n * p ^ r) - A370102Old.a (n * p ^ (r - 1))) := by
  have : Fact p.Prime := ⟨hpp⟩
  have hp0 : p ≠ 0 := hpp.ne_zero
  have hp2 : p % 2 = 1 := podd h5
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  set Q := n * p ^ r' with hQdef
  set N := n * p ^ (r' + 1) with hNdef
  have hN : N = p * Q := by rw [hNdef, hQdef, pow_succ]; ring
  have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (pow_ne_zero _ hp0))
  have hN5 : 5 ≤ N := by rw [hN]; nlinarith
  apply D.dvd (p := p)
  push_cast
  rw [← coeffA N (by omega), ← coeffA Q hQ1, main_id p Q N hp0 hp2 hN,
    ← coeff_expand_mul p hp0 (F ^ (4 * Q)) Q, ← hN, coeffBE,
    show N + 1 = (N - 2) + 1 + 1 + 1 by omega, sum_range_succ', sum_range_succ', sum_range_succ']
  set B := expand p hp0 (F ^ (4 * Q))
  set lam : ℚ := 4 * (N : ℚ)
  have hpN : p ^ (r' + 1) ∣ N := ⟨n, by rw [hNdef]; ring⟩
  have ht : D p (3 * (r' + 1))
      (∑ j ∈ range (N - 2), cc lam (j + 1 + 1 + 1) * coeff N (B * Lp p ^ (j + 1 + 1 + 1))) :=
    D.sum _ _ fun j _ => (ccD h5 (by omega) hpN (by omega)).mul0
      (((I0exp (I0F.pow _) hp0).mul (I0L.pow _)) N)
  have hc2 : D p (2 * (r' + 1)) (cc lam (0 + 1 + 1)) := by
    refine ((D.ppow (2 * (r' + 1))).mul0 (D.nat (8 * n ^ 2))).congr ?_
    simp only [cc, lam, hNdef]
    rw [show (0 + 1 + 1 : ℕ) = 2 from rfl, Nat.factorial_two]
    push_cast; ring
  have h2 : D p (3 * (r' + 1)) (cc lam (0 + 1 + 1) * coeff N (B * Lp p ^ (0 + 1 + 1))) := by
    have := L5 (p := p) h5 (Q := Q) (r := r' + 1) (by omega)
      ⟨n, by rw [Nat.add_sub_cancel, hQdef]; ring⟩
    rw [← hN] at this
    exact (hc2.mul this).le (by omega)
  have h1 : coeff N (B * Lp p ^ (0 + 1)) = 0 := by
    have := L1zero (p := p) Q; rw [← hN] at this; exact this
  have h0 : cc lam 0 * coeff N (B * Lp p ^ 0) = coeff N B := by simp [cc]
  rw [h1, h0, mul_zero, add_zero, add_sub_cancel_right]
  exact ht.add h2

end V

end A370102P

theorem OMA.solution : type_of% @OMA.S_oeis_a370102.main := by
  intro p hp h5 n r hn hr
  apply Nat.ModEq.symm
  rw [Nat.modEq_iff_dvd]
  push_cast
  rw [A370102Old.a_eq, A370102Old.a_eq]
  exact A370102P.final p n r hp h5 hn hr
