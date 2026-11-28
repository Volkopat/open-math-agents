import OMAStatements.S_oeis_a182960
import Mathlib

/-! Jacobsthal-Kazandzidis type congruence C(a p^r, b p^r) = C(a p^(r-1), b p^(r-1)) mod p^(3r), p >= 5. Base lemmas adapted from proofs/oeis-a375180.R1.H4.lean. -/

namespace LtsJacobsthal
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

/-- `∏_{0<i<t p^s, p ∤ i} (1 - A p^s / i) ≡ 1 mod p^(3s)` -/
lemma R_D (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (A t : ℕ) :
    D p (3 * s) (R p ((A : ℚ) * (p : ℚ) ^ s) (t * p ^ s) - 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨W, hW, hprod⟩ := prod_expand2 hp2 (U p (t * p ^ s)) (fun i => (A : ℚ) * ((i : ℚ)⁻¹))
    ((p : ℚ) ^ s) ((D.ppow s).le (Nat.zero_le _))
    (fun i hi => (D.nat A).mul0 (D.inv (mem_U.mp hi).2))
  have hR : R p ((A : ℚ) * (p : ℚ) ^ s) (t * p ^ s) =
      ∏ i ∈ U p (t * p ^ s), (1 - (p : ℚ) ^ s * ((A : ℚ) * ((i : ℚ)⁻¹))) := by
    unfold R
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_eq_mul_inv]; ring
  have h1 : ∑ i ∈ U p (t * p ^ s), (A : ℚ) * ((i : ℚ)⁻¹) = (A : ℚ) * sg p (t * p ^ s) 1 := by
    unfold sg; rw [Finset.mul_sum]; simp only [pow_one]
  have h2 : ∑ i ∈ U p (t * p ^ s), ((A : ℚ) * ((i : ℚ)⁻¹)) ^ 2 =
      (A : ℚ) ^ 2 * sg p (t * p ^ s) 2 := by
    unfold sg; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hR, hprod, h1, h2]
  have hS1 := S1_D h5 hs t
  have hS2 := S2_D h5 hs t
  have hi2 : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
  have e1 : D p (3 * s) ((p : ℚ) ^ s * ((A : ℚ) * sg p (t * p ^ s) 1)) :=
    ((D.ppow s).mul ((D.nat A).mul0' hS1)).le (by omega)
  have e2 : D p (3 * s) (((p : ℚ) ^ s) ^ 2 *
      (((A : ℚ) * sg p (t * p ^ s) 1) ^ 2 - (A : ℚ) ^ 2 * sg p (t * p ^ s) 2)) := by
    have hin : D p s (((A : ℚ) * sg p (t * p ^ s) 1) ^ 2 - (A : ℚ) ^ 2 * sg p (t * p ^ s) 2) :=
      ((((D.nat A).mul0' hS1).pow 2).le (by omega)).sub (((D.nat A).pow0 2).mul0' hS2)
    exact (((D.ppow s).pow 2).mul hin).le (by omega)
  have e3 : D p (3 * s) (((p : ℚ) ^ s) ^ 3 * W) :=
    (((D.ppow s).pow 3).mul0 hW).le (by omega)
  exact ((e1.neg.add (e2.mul0 hi2)).add e3).congr (by ring)

/-! ### the main theorem -/

/-- Jacobsthal-Kazandzidis type: `C(a p^r, b p^r) ≡ C(a p^(r-1), b p^(r-1)) mod p^(3r)`. -/
theorem jacobsthal (h5 : 5 ≤ p) (a b r : ℕ) (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * r) ∣ (Nat.choose (a * p ^ r) (b * p ^ r) : ℤ) -
      (Nat.choose (a * p ^ (r - 1)) (b * p ^ (r - 1)) : ℤ) := by
  have hp2 : p ≠ 2 := by omega
  have hc := choose_ratio (p := p) hp2 (a * p ^ (r - 1)) (b * p ^ (r - 1))
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hc ⊢
  have e1 : p * (a * p ^ k) = a * p ^ (k + 1) := by ring
  have e2 : p * (b * p ^ k) = b * p ^ (k + 1) := by ring
  rw [e1, e2] at hc
  have e3 : ((a * p ^ (k + 1) : ℕ) : ℚ) = (a : ℚ) * (p : ℚ) ^ (k + 1) := by push_cast; ring
  rw [e3] at hc
  apply D.dvd
  have hR := R_D h5 (by omega : 1 ≤ k + 1) a b
  refine ((D.nat ((a * p ^ k).choose (b * p ^ k))).mul0' hR).congr ?_
  push_cast
  rw [hc]
  ring

/-- the same with an explicit primality hypothesis -/
theorem jacobsthal' {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (a b r : ℕ) (hr : 1 ≤ r) :
    (q : ℤ) ^ (3 * r) ∣ (Nat.choose (a * q ^ r) (b * q ^ r) : ℤ) -
      (Nat.choose (a * q ^ (r - 1)) (b * q ^ (r - 1)) : ℤ) := by
  have : Fact q.Prime := ⟨hq⟩
  exact jacobsthal h5 a b r hr

end LtsJacobsthal


namespace A182960P
open PowerSeries Finset

def eta (n m : ℕ) : ℤ := (Nat.choose (3 * m + n) m : ℤ)

def beta (n m : ℕ) : ℤ := if m = 0 then 1 else eta n m - 3 * eta (n + 2) (m - 1)

lemma eta_pascal (n m : ℕ) : eta (n + 1) (m + 1) = eta n (m + 1) + eta (n + 3) m := by
  unfold eta
  have h1 : 3 * (m + 1) + (n + 1) = (3 * (m + 1) + n) + 1 := by ring
  have h2 : 3 * m + (n + 3) = 3 * (m + 1) + n := by ring
  rw [h1, h2, Nat.choose_succ_succ', add_comm (Nat.choose _ m)]
  push_cast; ring

lemma beta_rec (n m : ℕ) : beta (n + 1) (m + 1) = beta n (m + 1) + beta (n + 3) m := by
  rcases m with _ | k
  · simp [beta, eta]
  · simp only [beta, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    have e1 := eta_pascal n (k + 1)
    have e2 := eta_pascal (n + 2) k
    have e3 : n + 2 + 3 = n + 3 + 2 := by ring
    have e4 : n + 2 + 1 = n + 3 := by ring
    rw [e3, e4] at e2
    linear_combination e1 - 3 * e2

lemma beta_zero (m : ℕ) (hm : m ≠ 0) : beta 0 m = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [beta, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, eta]
  have h := Nat.add_one_mul_choose_eq (3 * k + 2) k
  have e1 : 3 * k + 2 + 1 = 3 * (k + 1) + 0 := by ring
  have e2 : 3 * k + (0 + 2) = 3 * k + 2 := by ring
  rw [e1] at h
  rw [e2]
  have h' : ((3 * k + 2 + 1 : ℕ) : ℤ) * ((3 * k + 2).choose k : ℤ)
      = ((3 * (k + 1) + 0).choose (k + 1) : ℤ) * ((k + 1 : ℕ) : ℤ) := by
    rw [← e1]; exact_mod_cast h
  have hk : ((k + 1 : ℕ) : ℤ) ≠ 0 := by positivity
  apply mul_right_cancel₀ hk
  push_cast at h' ⊢
  linear_combination -h'

noncomputable def Qs (n : ℕ) : PowerSeries ℚ := mk fun m => (beta n m : ℚ)
noncomputable def Gs (n : ℕ) : PowerSeries ℚ := mk fun m => (eta n m : ℚ)

def IsRec (F : ℕ → PowerSeries ℚ) : Prop := ∀ n, F (n + 1) = F n + X * F (n + 3)

lemma Qs_rec : IsRec Qs := by
  intro n; ext m
  rcases m with _ | k
  · simp [Qs, beta]
  · rw [map_add, coeff_succ_X_mul]
    simp only [Qs, coeff_mk]
    rw [beta_rec]; push_cast; ring

lemma Gs_rec : IsRec Gs := by
  intro n; ext m
  rcases m with _ | k
  · simp [Gs, eta]
  · rw [map_add, coeff_succ_X_mul]
    simp only [Gs, coeff_mk]
    rw [eta_pascal]; push_cast; ring

lemma rec_unique (F G : ℕ → PowerSeries ℚ) (hF : IsRec F) (hG : IsRec G) (h0 : F 0 = G 0) :
    ∀ n, F n = G n := by
  have key : ∀ m n, coeff m (F n) = coeff m (G n) := by
    intro m
    induction m with
    | zero =>
      intro n
      induction n with
      | zero => rw [h0]
      | succ n ih => rw [hF, hG, map_add, map_add, coeff_zero_X_mul, coeff_zero_X_mul, ih]
    | succ k ihk =>
      intro n
      induction n with
      | zero => rw [h0]
      | succ n ih => rw [hF, hG, map_add, map_add, coeff_succ_X_mul, coeff_succ_X_mul, ih, ihk]
  intro n; ext m; exact key m n

lemma rec_mul (F : ℕ → PowerSeries ℚ) (hF : IsRec F) (S : PowerSeries ℚ) :
    IsRec (fun n => F n * S) := by
  intro n; simp only; rw [hF]; ring

lemma rec_shift (F : ℕ → PowerSeries ℚ) (hF : IsRec F) : IsRec (fun n => F (n + 1)) := by
  intro n; exact hF (n + 1)

lemma Qs_zero : Qs 0 = 1 := by
  ext m
  rw [Qs, coeff_mk, coeff_one]
  by_cases hm : m = 0
  · subst hm; simp [beta]
  · rw [if_neg hm, beta_zero m hm]; simp

noncomputable def B : PowerSeries ℚ := Qs 1
noncomputable def H : PowerSeries ℚ := Gs 0

lemma Qs_pow (n : ℕ) : Qs n = B ^ n := by
  have hs : ∀ n, Qs (n + 1) = Qs n * Qs 1 := by
    have := rec_unique (fun n => Qs (n + 1)) (fun n => Qs n * Qs 1) (rec_shift _ Qs_rec)
      (rec_mul _ Qs_rec _) (by simp [Qs_zero])
    exact this
  induction n with
  | zero => simp [Qs_zero]
  | succ n ih => rw [hs, ih, pow_succ, B]

lemma B_eq : B = 1 + X * B ^ 3 := by
  have h := Qs_rec 0
  rw [Qs_zero, Qs_pow 3] at h
  exact h

lemma Gs_eq (n : ℕ) : Gs n = H * B ^ n := by
  have := rec_unique Gs (fun n => Gs 0 * Qs n) Gs_rec
    (by intro n; simp only; rw [Qs_rec]; ring) (by simp [Qs_zero])
  rw [this n, Qs_pow, H]

lemma H_eq : H * (1 - 3 * X * B ^ 2) = 1 := by
  have h : Qs 0 = Gs 0 - 3 * X * Gs 2 := by
    ext m
    rcases m with _ | k
    · simp [Qs, Gs, beta, eta]
    · rw [map_sub, show (3 : PowerSeries ℚ) * X * Gs 2 = X * (C (3 : ℚ) * Gs 2) by
          rw [map_ofNat]; ring, coeff_succ_X_mul, coeff_C_mul]
      simp only [Qs, Gs, coeff_mk, beta, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      push_cast; ring
  rw [Qs_zero, Gs_eq 2, ← H] at h
  linear_combination -h

/-! theta = X d/dX -/

noncomputable def th (f : PowerSeries ℚ) : PowerSeries ℚ := X * d⁄dX ℚ f

lemma coeff_th (f : PowerSeries ℚ) (m : ℕ) : coeff m (th f) = (m : ℚ) * coeff m f := by
  rcases m with _ | k
  · simp [th]
  · rw [th, coeff_succ_X_mul, coeff_derivative]; push_cast; ring

lemma th_mul (f g : PowerSeries ℚ) : th (f * g) = th f * g + f * th g := by
  simp only [th, Derivation.leibniz, smul_eq_mul]; ring

lemma th_add (f g : PowerSeries ℚ) : th (f + g) = th f + th g := by
  simp only [th, map_add]; ring

lemma th_X : th X = X := by simp [th]

lemma th_one : th 1 = 0 := by simp [th]

lemma th_B : th B = (B - 1) * H := by
  have h1 : th B = X * B ^ 3 + 3 * X * B ^ 2 * th B := by
    conv_lhs => rw [B_eq]
    rw [th_add, th_one, th_mul, th_X, pow_succ, pow_two, th_mul, th_mul]
    ring
  have h2 := H_eq
  have h3 := B_eq
  linear_combination H * h1 - th B * h2 - H * h3

lemma th_B3 : 3 * th B = B * (H - 1) := by
  rw [th_B]
  have h2 := H_eq
  have h3 := B_eq
  linear_combination (-B) * h2 + (3 * H) * h3

noncomputable def sg : PowerSeries ℚ →+* PowerSeries ℚ := rescale (-1 : ℚ)

lemma th_sg (f : PowerSeries ℚ) : th (sg f) = sg (th f) := by
  ext m; simp only [sg, coeff_th, coeff_rescale]; ring

noncomputable def P : PowerSeries ℚ := B * sg B

lemma th_P : 3 * th P = P * (H + sg H - 2) := by
  rw [P, th_mul, th_sg]
  have h1 := th_B3
  have h2 : 3 * sg (th B) = sg B * (sg H - 1) := by
    have := congrArg sg h1
    simpa [map_mul, map_sub, map_one, map_ofNat] using this
  linear_combination sg B * h1 + B * h2

/-- the series sum_{n>=1} C(6n-1,2n-1) x^n -/
noncomputable def Cs : PowerSeries ℚ := mk fun n => match n with
  | 0 => 0
  | k + 1 => ((Nat.choose (6 * k + 5) (2 * k + 1) : ℕ) : ℚ)

lemma choose_six (k : ℕ) :
    ((Nat.choose (6 * k + 6) (2 * k + 2) : ℕ) : ℚ) = 3 * ((Nat.choose (6 * k + 5) (2 * k + 1) : ℕ) : ℚ) := by
  have h := Nat.add_one_mul_choose_eq (6 * k + 5) (2 * k + 1)
  have h' : ((6 * k + 5 + 1 : ℕ) : ℚ) * ((6 * k + 5).choose (2 * k + 1) : ℚ)
      = ((6 * k + 5 + 1).choose (2 * k + 1 + 1) : ℚ) * ((2 * k + 1 + 1 : ℕ) : ℚ) := by
    exact_mod_cast h
  have hk : ((2 * k + 1 + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  apply mul_right_cancel₀ hk
  have e1 : 6 * k + 5 + 1 = 6 * k + 6 := by ring
  have e2 : 2 * k + 1 + 1 = 2 * k + 2 := by ring
  rw [e1, e2] at h'
  push_cast at h' ⊢
  linear_combination -h'

lemma W_eq : H + sg H - 2 = 6 * expand 2 (by norm_num) Cs := by
  ext m
  rw [map_sub, map_add, show (6 : PowerSeries ℚ) = C (6 : ℚ) by rw [map_ofNat], coeff_C_mul,
    coeff_expand, show (2 : PowerSeries ℚ) = C (2 : ℚ) by rw [map_ofNat], coeff_C]
  simp only [H, sg, Gs, coeff_rescale, coeff_mk, eta]
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · rcases k with _ | j
    · subst hk; simp [Cs]; norm_num
    · have hm : m = 2 * (j + 1) := by omega
      subst hm
      have hd : 2 * (j + 1) / 2 = j + 1 := by omega
      rw [if_pos (dvd_mul_right 2 _), hd, if_neg (by omega)]
      simp only [Cs, coeff_mk]
      have e : 3 * (2 * (j + 1)) + 0 = 6 * j + 6 := by ring
      have e2 : 2 * (j + 1) = 2 * j + 2 := by ring
      have hpow : ((-1 : ℚ)) ^ (2 * j + 2) = 1 := by rw [pow_add, pow_mul]; norm_num
      rw [e, e2, hpow]
      push_cast
      rw [choose_six]
      ring
  · have hm : ¬ 2 ∣ m := by omega
    rw [if_neg hm, if_neg (by omega), hk, pow_succ, pow_mul]
    norm_num

lemma th_P' : th P = P * (2 * expand 2 (by norm_num) Cs) := by
  have h := th_P
  rw [W_eq] at h
  have h3 : (3 : PowerSeries ℚ) ≠ 0 := by
    intro h0
    have := congrArg (coeff 0) h0
    rw [show (3 : PowerSeries ℚ) = C (3 : ℚ) by rw [map_ofNat], coeff_C] at this
    norm_num at this
  have h4 : (3 : PowerSeries ℚ) * (th P - P * (2 * expand 2 (by norm_num) Cs)) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact absurd h5 h3
  · exact sub_eq_zero.mp h5

/-! the generating function of the statement -/

open OMA.S_oeis_a182960 in
lemma th_A : th OMA.S_oeis_a182960.A = OMA.S_oeis_a182960.A * Cs := by
  ext m
  rw [coeff_th, mul_comm OMA.S_oeis_a182960.A Cs, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i Cs * coeff j OMA.S_oeis_a182960.A)]
  rcases m with _ | n
  · simp [Cs]
  · rw [Finset.sum_range_succ']
    simp only [OMA.S_oeis_a182960.A, Cs, coeff_mk]
    rw [OMA.S_oeis_a182960.a]
    rw [Fin.sum_univ_eq_sum_range (fun k => ((Nat.choose (6 * k + 5) (2 * k + 1) : ℕ) : ℚ) *
      OMA.S_oeis_a182960.a (n - k)) (n + 1)]
    simp only [Nat.add_sub_add_right, zero_mul, add_zero]
    push_cast
    field_simp


/-! ### integrality -/

lemma coeff_zero_mul' (f g : PowerSeries ℚ) : coeff 0 (f * g) = coeff 0 f * coeff 0 g := by
  rw [coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]

lemma ode_unique (F G V : PowerSeries ℚ) (hF : th F = F * V) (hG : th G = G * V)
    (hF0 : coeff 0 F = 1) (hG0 : coeff 0 G = 1) : F = G := by
  have hGc : constantCoeff G ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hG0]; norm_num
  set K := F * G⁻¹ with hKdef
  have hFK : F = K * G := by rw [hKdef, mul_assoc, PowerSeries.inv_mul_cancel _ hGc, mul_one]
  have hm := th_mul K G
  rw [← hFK, hF, hG] at hm
  have hth : th K * G = 0 := by linear_combination (-1 : PowerSeries ℚ) * hm + V * hFK
  have hGne : G ≠ 0 := by
    intro h0; rw [h0] at hG0; simp at hG0
  have hK : th K = 0 := (mul_eq_zero.mp hth).resolve_right hGne
  have hK0 : coeff 0 K = 1 := by
    have := congrArg (coeff 0) hFK
    rw [coeff_zero_mul', hF0, hG0, mul_one] at this
    exact this.symm
  have hK1 : K = 1 := by
    ext m
    by_cases hm0 : m = 0
    · subst hm0; rw [hK0, coeff_one, if_pos rfl]
    · have := congrArg (coeff m) hK
      rw [coeff_th, map_zero] at this
      rw [coeff_one, if_neg hm0]
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by exact_mod_cast hm0)
      · exact h
  rw [hFK, hK1, one_mul]

lemma th_expand (f : PowerSeries ℚ) :
    th (expand 2 (by norm_num) f) = 2 * expand 2 (by norm_num) (th f) := by
  ext m
  rw [show (2 : PowerSeries ℚ) = C (2 : ℚ) by rw [map_ofNat], coeff_C_mul, coeff_th,
    coeff_expand, coeff_expand]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (by norm_num), coeff_th]
    push_cast; ring
  · simp

lemma coeff_A (n : ℕ) : coeff n OMA.S_oeis_a182960.A = OMA.S_oeis_a182960.a n := by
  simp [OMA.S_oeis_a182960.A]

lemma a_zero : OMA.S_oeis_a182960.a 0 = 1 := by
  rw [OMA.S_oeis_a182960.a]

lemma E_eq_P : expand 2 (by norm_num) OMA.S_oeis_a182960.A = P := by
  apply ode_unique _ _ (2 * expand 2 (by norm_num) Cs)
  · rw [th_expand, th_A, map_mul]; ring
  · exact th_P'
  · simp [coeff_expand, coeff_A, a_zero]
  · rw [P, coeff_zero_mul', sg, coeff_rescale, B, Qs, coeff_mk]; simp [beta]

def IntS (f : PowerSeries ℚ) : Prop := ∀ n, ∃ z : ℤ, coeff n f = (z : ℚ)

lemma IntS.mul {f g : PowerSeries ℚ} (hf : IntS f) (hg : IntS g) : IntS (f * g) := by
  intro n
  choose zf hzf using hf
  choose zg hzg using hg
  refine ⟨∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, zf x.1 * zg x.2, ?_⟩
  rw [coeff_mul]; push_cast
  exact Finset.sum_congr rfl (fun x _ => by rw [hzf, hzg])

lemma IntS.one : IntS 1 := by
  intro n; rw [coeff_one]; split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

lemma IntS.pow {f : PowerSeries ℚ} (hf : IntS f) (n : ℕ) : IntS (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact IntS.one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

lemma IntS_P : IntS P := by
  have h1 : IntS B := fun n => ⟨beta 1 n, by rw [B, Qs, coeff_mk]⟩
  have h2 : IntS (sg B) := fun n => ⟨(-1) ^ n * beta 1 n, by
    rw [sg, coeff_rescale, B, Qs, coeff_mk]; push_cast; ring⟩
  exact h1.mul h2

lemma IntS_A : IntS OMA.S_oeis_a182960.A := by
  intro n
  obtain ⟨z, hz⟩ := IntS_P (2 * n)
  refine ⟨z, ?_⟩
  rw [← E_eq_P, coeff_expand_mul] at hz
  exact hz

lemma b_int (n : ℕ) : ∃ z : ℤ, OMA.S_oeis_a182960.b n = (z : ℚ) := by
  exact (IntS_A.pow n) n

/-! ### the congruence -/

section cong
open LtsJacobsthal

variable {p : ℕ} [hp : Fact p.Prime]

noncomputable def ell (n : ℕ) : ℚ := coeff n Cs / (n : ℚ)
noncomputable def L : PowerSeries ℚ := mk ell

lemma th_L : th L = Cs := by
  ext m
  rw [coeff_th, L, coeff_mk, ell]
  by_cases hm : m = 0
  · subst hm; simp [Cs]
  · have : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    field_simp

lemma th_C (r : ℚ) (f : PowerSeries ℚ) : th (C r * f) = C r * th f := by
  rw [th_mul]; simp [th]

lemma th_pow_A (n : ℕ) : th (OMA.S_oeis_a182960.A ^ n)
    = C (n : ℚ) * OMA.S_oeis_a182960.A ^ n * Cs := by
  induction n with
  | zero => simp [th]
  | succ n ih =>
    rw [pow_succ, th_mul, ih, th_A]
    push_cast; rw [map_add, map_one]; ring

lemma th_L3 : th (L ^ 3) = 3 * L ^ 2 * Cs := by
  rw [pow_succ, pow_two, th_mul, th_mul, th_L]; ring

lemma coeff_Cs_succ (k : ℕ) : coeff (k + 1) Cs = ((Nat.choose (6 * k + 5) (2 * k + 1) : ℕ) : ℚ) := by
  simp [Cs]

lemma D_Cs (i : ℕ) : D p 0 (coeff i Cs) := by
  rcases i with _ | k
  · simp [Cs]; exact D.zero 0
  · rw [coeff_Cs_succ]; exact D.nat _

def Pr (p : ℕ) (f : PowerSeries ℚ) : Prop := coeff 0 f = 0 ∧ ∀ i < p, D p 0 (coeff i f)

lemma Pr_mul {f g : PowerSeries ℚ} (hf : Pr p f) (hg : Pr p g) :
    coeff 0 (f * g) = 0 ∧ ∀ i ≤ p, D p 0 (coeff i (f * g)) := by
  refine ⟨by rw [coeff_zero_mul', hf.1, zero_mul], fun i hi => ?_⟩
  rw [coeff_mul]
  apply D.sum
  intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases h1 : x.1 = 0
  · rw [h1, hf.1, zero_mul]; exact D.zero 0
  by_cases h2 : x.2 = 0
  · rw [h2, hg.1, mul_zero]; exact D.zero 0
  exact (hf.2 _ (by omega)).mul (hg.2 _ (by omega))

lemma Pr_L : Pr p L := by
  refine ⟨by simp [L, ell], fun i hi => ?_⟩
  rw [L, coeff_mk, ell]
  by_cases h0 : i = 0
  · subst h0; simp; exact D.zero 0
  · have hpi : ¬ p ∣ i := fun h => by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h; omega
    rw [div_eq_mul_inv]
    exact (D_Cs i).mul (D.inv hpi)

lemma Pr_L2 : Pr p (L ^ 2) := by
  have h := Pr_mul (Pr_L (p := p)) (Pr_L (p := p))
  rw [← pow_two] at h
  exact ⟨h.1, fun i hi => h.2 i hi.le⟩

lemma D_L3 (i : ℕ) (hi : i ≤ p) : D p 0 (coeff i (L ^ 3)) := by
  have h := Pr_mul (Pr_L2 (p := p)) (Pr_L (p := p))
  rw [← pow_succ] at h
  exact h.2 i hi

lemma coeff_L2Cs (m : ℕ) : coeff m (L ^ 2 * Cs) = (m : ℚ) / 3 * coeff m (L ^ 3) := by
  have h := congrArg (coeff m) th_L3
  rw [coeff_th, show (3 : PowerSeries ℚ) * L ^ 2 * Cs = C (3 : ℚ) * (L ^ 2 * Cs) by
    rw [map_ofNat]; ring, coeff_C_mul] at h
  linear_combination -h / 3

noncomputable def E2 (p : ℕ) : PowerSeries ℚ :=
  1 + C (p : ℚ) * L + C ((p : ℚ) ^ 2 / 2) * L ^ 2

noncomputable def hh (p : ℕ) : PowerSeries ℚ := OMA.S_oeis_a182960.A ^ p - E2 p

lemma hh_ode : th (hh p) - C (p : ℚ) * (Cs * hh p) = C ((p : ℚ) ^ 3 / 2) * (L ^ 2 * Cs) := by
  have hc1 : C ((p : ℚ) ^ 2 / 2) * 2 = C (p : ℚ) * C (p : ℚ) := by
    rw [show (2 : PowerSeries ℚ) = C (2 : ℚ) by rw [map_ofNat], ← map_mul, ← map_mul]
    congr 1; ring
  have hc2 : C (p : ℚ) * C ((p : ℚ) ^ 2 / 2) = C ((p : ℚ) ^ 3 / 2) := by
    rw [← map_mul]; congr 1; ring
  have hE : th (E2 p) = C (p : ℚ) * Cs + C ((p : ℚ) ^ 2 / 2) * (2 * L * Cs) := by
    have hL2 : th (L ^ 2) = 2 * L * Cs := by rw [pow_two, th_mul, th_L]; ring
    rw [E2, th_add, th_add, th_one, th_C, th_C, th_L, hL2]; ring
  have hsub : th (OMA.S_oeis_a182960.A ^ p - E2 p) = th (OMA.S_oeis_a182960.A ^ p) - th (E2 p) := by
    simp only [th, map_sub]; ring
  rw [hh, hsub, hE, th_pow_A]
  rw [E2]
  linear_combination (-1 : PowerSeries ℚ) * L * Cs * hc1 + Cs * L ^ 2 * hc2

lemma hh_coeff (m : ℕ) : (m : ℚ) * coeff m (hh p)
    = (p : ℚ) * ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, coeff x.1 Cs * coeff x.2 (hh p)
      + (p : ℚ) ^ 3 / 2 * ((m : ℚ) / 3 * coeff m (L ^ 3)) := by
  have h := congrArg (coeff m) (hh_ode (p := p))
  rw [map_sub, coeff_th, coeff_C_mul, coeff_C_mul, coeff_L2Cs, coeff_mul] at h
  linear_combination h

lemma coeff0_pow (f : PowerSeries ℚ) (n : ℕ) : coeff 0 (f ^ n) = (coeff 0 f) ^ n := by
  rw [coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply]

lemma hh_zero : coeff 0 (hh p) = 0 := by
  rw [hh, map_sub, coeff0_pow, coeff_A, a_zero, one_pow, E2, map_add, map_add, coeff_C_mul,
    coeff_C_mul, (Pr_L (p := p)).1, (Pr_L2 (p := p)).1, coeff_one, if_pos rfl]
  ring

lemma hh_sum_D3 (m : ℕ) (hm : m ≤ p) (ih : ∀ j < m, D p 3 (coeff j (hh p))) :
    D p 3 (∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, coeff x.1 Cs * coeff x.2 (hh p)) := by
  apply D.sum
  intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases h1 : x.1 = 0
  · rw [h1]; simp [Cs]; exact D.zero 3
  · exact (D_Cs x.1).mul0' (ih _ (by omega))

lemma hh_small (h5 : 5 ≤ p) : ∀ m < p, D p 3 (coeff m (hh p)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases h0 : m = 0
    · subst h0; rw [hh_zero]; exact D.zero 3
    have hpm : ¬ p ∣ m := fun h => by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h; omega
    apply D.ucancel hpm
    rw [hh_coeff]
    have hS := hh_sum_D3 (p := p) m hm.le (fun j hj => ih j hj (by omega))
    refine D.add ((((D.ppow 1).mul hS)).le (by omega) |>.congr (by ring)) ?_
    have h3 := D_L3 (p := p) m hm.le
    refine ((D.ppow 3).mul0 ((D.inv (u := 2) ?_).mul0 ((D.nat m).mul0 ((D.inv (u := 3) ?_).mul0 h3)))).congr
      (by ring)
    · intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    · intro h; have := Nat.le_of_dvd (by norm_num) h; omega


lemma hh_at_p (h5 : 5 ≤ p) : D p 3 (coeff p (hh p)) := by
  have hc := hh_coeff (p := p) p
  have hS := hh_sum_D3 (p := p) p le_rfl (fun j hj => hh_small h5 j hj)
  have h3 := D_L3 (p := p) p le_rfl
  have hR : D p (3 + 1) ((p : ℚ) ^ 1 * coeff p (hh p)) := by
    rw [pow_one, hc]
    refine D.add (((D.ppow 1).mul hS).congr (by ring)) ?_
    refine ((D.ppow 4).mul0 ((D.inv (u := 2) ?_).mul0 ((D.inv (u := 3) ?_).mul0 h3))).congr
      (by ring)
    · intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    · intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  exact D.cancel hR

def cc (n : ℕ) : ℕ := Nat.choose (6 * n - 1) (2 * n - 1)

lemma three_cc (n : ℕ) (hn : 1 ≤ n) : 3 * cc n = Nat.choose (6 * n) (2 * n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [cc, show 6 * (k + 1) - 1 = 6 * k + 5 by omega, show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
    show 6 * (k + 1) = 6 * k + 6 by ring, show 2 * (k + 1) = 2 * k + 2 by ring]
  exact_mod_cast (choose_six k).symm

lemma coeff_Cs (n : ℕ) (hn : 1 ≤ n) : coeff n Cs = (cc n : ℚ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [coeff_Cs_succ, cc, show 6 * (k + 1) - 1 = 6 * k + 5 by omega,
    show 2 * (k + 1) - 1 = 2 * k + 1 by omega]

lemma kummer1 (a b : ℕ) (h : p ≤ b % p + a % p) : p ∣ Nat.choose (a + b) b := by
  have hlog : 0 < Nat.log p (a + b) := Nat.log_pos hp.out.one_lt
    (by have := Nat.mod_le b p; have := Nat.mod_le a p; omega)
  have hv := padicValNat_choose' (p := p) (n := a) (k := b) (b := Nat.log p (a + b) + 1) (by omega)
  apply dvd_of_one_le_padicValNat
  rw [hv]
  apply Finset.card_pos.mpr
  exact ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩, by rw [pow_one]; exact h⟩⟩

lemma mod_pair {x y : ℕ} (hx : ¬ p ∣ x) (hxy : p ∣ x + y) : x % p + y % p = p := by
  have h1 : 0 < x % p := Nat.pos_of_ne_zero (fun h => hx (Nat.dvd_of_mod_eq_zero h))
  have h2 : x % p < p := Nat.mod_lt _ hp.out.pos
  have h3 : y % p < p := Nat.mod_lt _ hp.out.pos
  have h4 : (x % p + y % p) % p = 0 := by
    rw [← Nat.add_mod]; exact Nat.dvd_iff_mod_eq_zero.mp hxy
  obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero h4
  rcases t with _ | _ | t
  · omega
  · omega
  · nlinarith

lemma dvd_cc (h5 : 5 ≤ p) (n : ℕ) (hn : 1 ≤ n) (h : p ≤ (2 * n) % p + (4 * n) % p) : p ∣ cc n := by
  have := kummer1 (p := p) (4 * n) (2 * n) h
  rw [show 4 * n + 2 * n = 6 * n by ring, ← three_cc n hn] at this
  exact ((Nat.Prime.dvd_mul hp.out).mp this).resolve_left
    (fun h3 => by have := Nat.le_of_dvd (by norm_num) h3; omega)

lemma not_dvd_mul (h5 : 5 ≤ p) {c i : ℕ} (hc : c = 2 ∨ c = 4) (hi1 : 1 ≤ i) (hi : i < p) :
    ¬ p ∣ c * i := by
  intro h
  rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
  · have := Nat.le_of_dvd (by omega) h; omega
  · have := Nat.le_of_dvd (by omega) h; omega

lemma lemma4 (h5 : 5 ≤ p) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < p) : p ∣ cc i * cc (p - i) := by
  have e2 := mod_pair (p := p) (x := 2 * i) (y := 2 * (p - i))
    (not_dvd_mul h5 (Or.inl rfl) h1 h2) ⟨2, by omega⟩
  have e4 := mod_pair (p := p) (x := 4 * i) (y := 4 * (p - i))
    (not_dvd_mul h5 (Or.inr rfl) h1 h2) ⟨4, by omega⟩
  by_cases hA : p ≤ (2 * i) % p + (4 * i) % p
  · exact Dvd.dvd.mul_right (dvd_cc h5 i h1 hA) _
  · exact Dvd.dvd.mul_left (dvd_cc h5 (p - i) (by omega) (by omega)) _

lemma D_of_dvd {n : ℕ} (h : p ∣ n) : D p 1 (n : ℚ) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨w, 1, hp.out.not_dvd_one, by push_cast; ring⟩

lemma L2_p (h5 : 5 ≤ p) : D p 1 (coeff p (L ^ 2)) := by
  rw [pow_two, coeff_mul]
  apply D.sum
  intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases h1 : x.1 = 0
  · rw [h1]; simp [L, ell]; exact D.zero 1
  by_cases h2 : x.2 = 0
  · rw [h2]; simp [L, ell]; exact D.zero 1
  have hx2 : x.2 = p - x.1 := by omega
  have hpa : ¬ p ∣ x.1 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hpb : ¬ p ∣ x.2 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hd := lemma4 h5 x.1 (by omega) (by omega)
  rw [← hx2] at hd
  rw [L, coeff_mk, coeff_mk, ell, ell, coeff_Cs _ (by omega), coeff_Cs _ (by omega)]
  refine ((D_of_dvd hd).mul0 ((D.inv hpa).mul0 (D.inv hpb))).congr ?_
  push_cast; ring

lemma cp_cong (h5 : 5 ≤ p) : D p 3 ((cc p : ℚ) - 5) := by
  have hj := LtsJacobsthal.jacobsthal' hp.out h5 6 2 1 le_rfl
  simp only [pow_one, Nat.sub_self, pow_zero, mul_one] at hj
  rw [← three_cc p (by omega), show Nat.choose 6 2 = 15 by rfl] at hj
  obtain ⟨w, hw⟩ := hj
  apply D.ucancel (u := 3) (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  refine ⟨w, 1, hp.out.not_dvd_one, ?_⟩
  have := congrArg (Int.cast (R := ℚ)) hw
  push_cast at this
  linear_combination this

lemma main' (h5 : 5 ≤ p) : ∃ c : ℤ, OMA.S_oeis_a182960.b p - OMA.S_oeis_a182960.b 1
    = ((p : ℚ) ^ 3) * (c : ℚ) := by
  obtain ⟨z, hz⟩ := b_int p
  have hb1 : OMA.S_oeis_a182960.b 1 = 5 := by
    rw [OMA.S_oeis_a182960.b, pow_one, coeff_A, OMA.S_oeis_a182960.a]
    simp [a_zero]
  have hsplit : OMA.S_oeis_a182960.b p
      = coeff p (hh p) + (cc p : ℚ) + (p : ℚ) ^ 2 / 2 * coeff p (L ^ 2) := by
    have hp0 : p ≠ 0 := hp.out.ne_zero
    have e : OMA.S_oeis_a182960.A ^ p = hh p + E2 p := by rw [hh]; ring
    rw [OMA.S_oeis_a182960.b, e, map_add, E2, map_add, map_add, coeff_C_mul, coeff_C_mul,
      coeff_one, if_neg hp0, L, coeff_mk, ell, coeff_Cs p (by omega)]
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
    field_simp
    ring
  have hD : D p 3 ((z : ℚ) - 5) := by
    rw [← hz, hsplit]
    have t3 : D p 3 ((p : ℚ) ^ 2 / 2 * coeff p (L ^ 2)) :=
      ((((D.ppow 2).mul (L2_p h5)).mul0 (D.inv (u := 2) (fun h => by
        have := Nat.le_of_dvd (by norm_num) h; omega))).le (by norm_num)).congr (by ring)
    exact (((hh_at_p h5).add (cp_cong h5)).add t3).congr (by ring)
  obtain ⟨c, hc⟩ := D.dvd (p := p) (e := 3) (z := z - 5) (by push_cast; exact hD)
  refine ⟨c, ?_⟩
  rw [hz, hb1]
  have := congrArg (Int.cast (R := ℚ)) hc
  push_cast at this
  linear_combination this

end cong

end A182960P

theorem OMA.solution : type_of% @OMA.S_oeis_a182960.main := by
  intro p hpp h5
  haveI := Fact.mk hpp
  exact A182960P.main' h5
