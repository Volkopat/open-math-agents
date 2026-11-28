import OMAStatements.S_oeis_a275654
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

/-!
Dixon-type identity via a Zeilberger certificate (recurrence in n, x fixed).

  S x n = Sum_{j <= n} C(x,j)^2 C(x-n-1-j, n-j)
  n!^2 S x n = Prod_{i < n} (x-2i-1)(x+2i+2)      for x >= 2n+1.

Certificate: G j = -j^2 C(x,j)^2 C(x-n-1-j, n+1-j),
  (n+1)^2 F(n+1,j) - (x-2n-1)(x+2n+2) F(n,j) = G(j+1) - G(j).
A364517: x = 7n-1 (reindex j = n-k). A275654: x = 5n.
-/

namespace LtsDixon

open Finset

/-- The two-parameter family. -/
def S (x n : ℕ) : ℚ :=
  ∑ j ∈ range (n + 1), ((x.choose j : ℚ)) ^ 2 * ((x - n - 1 - j).choose (n - j) : ℚ)

/-- The closed product. -/
def P (x n : ℕ) : ℚ :=
  ∏ i ∈ range n, (((x : ℚ) - 2 * i - 1) * ((x : ℚ) + 2 * i + 2))

theorem term (x n j : ℕ) (hj : j ≤ n) (hx : 2 * n + 3 ≤ x) :
    ((n : ℚ) + 1) ^ 2 * ((x.choose j : ℚ) ^ 2 * ((x - (n + 1) - 1 - j).choose (n + 1 - j) : ℚ))
      - ((x : ℚ) - 2 * n - 1) * ((x : ℚ) + 2 * n + 2)
          * ((x.choose j : ℚ) ^ 2 * ((x - n - 1 - j).choose (n - j) : ℚ))
    = (-(((j + 1 : ℕ) : ℚ)) ^ 2 * (x.choose (j + 1) : ℚ) ^ 2
          * ((x - n - 1 - (j + 1)).choose (n + 1 - (j + 1)) : ℚ))
      - (-((j : ℚ)) ^ 2 * (x.choose j : ℚ) ^ 2 * ((x - n - 1 - j).choose (n + 1 - j) : ℚ)) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = j + d := ⟨n - j, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, x = 2 * j + 2 * d + e + 3 := ⟨x - 2 * j - 2 * d - 3, by omega⟩
  have r1 : 2 * j + 2 * d + e + 3 - (j + d + 1) - 1 - j = d + e + 1 := by omega
  have r2 : j + d + 1 - j = d + 1 := by omega
  have r3 : 2 * j + 2 * d + e + 3 - (j + d) - 1 - j = d + e + 2 := by omega
  have r4 : j + d - j = d := by omega
  have r5 : 2 * j + 2 * d + e + 3 - (j + d) - 1 - (j + 1) = d + e + 1 := by omega
  have r6 : j + d + 1 - (j + 1) = d := by omega
  rw [r1, r2, r3, r4, r5, r6]
  have h1 := Nat.choose_succ_right_eq (d + e + 1) d
  have h2 := Nat.add_one_mul_choose_eq (d + e + 1) d
  have h3 := Nat.choose_mul_succ_eq (d + e + 1) d
  have h4 := Nat.choose_succ_right_eq (2 * j + 2 * d + e + 3) j
  have s1 : d + e + 1 - d = e + 1 := by omega
  have s3 : d + e + 1 + 1 - d = e + 2 := by omega
  have s4 : 2 * j + 2 * d + e + 3 - j = j + 2 * d + e + 3 := by omega
  rw [s1] at h1
  rw [s3] at h3
  rw [s4] at h4
  have q1 : ((d + e + 1).choose (d + 1) : ℚ) = ((d + e + 1).choose d : ℚ) * (e + 1) / (d + 1) := by
    rw [eq_div_iff (by positivity)]; exact_mod_cast h1
  have q2 : ((d + e + 1 + 1).choose (d + 1) : ℚ) = (d + e + 1 + 1) * ((d + e + 1).choose d : ℚ) / (d + 1) := by
    rw [eq_div_iff (by positivity)]; exact_mod_cast h2.symm
  have q3 : ((d + e + 1 + 1).choose d : ℚ) = ((d + e + 1).choose d : ℚ) * (d + e + 1 + 1) / (e + 2) := by
    rw [eq_div_iff (by positivity)]; exact_mod_cast h3.symm
  have q4 : ((2 * j + 2 * d + e + 3).choose (j + 1) : ℚ)
      = ((2 * j + 2 * d + e + 3).choose j : ℚ) * (j + 2 * d + e + 3) / (j + 1) := by
    rw [eq_div_iff (by positivity)]; exact_mod_cast h4
  have e2 : d + e + 2 = d + e + 1 + 1 := rfl
  rw [e2, q1, q2, q3, q4]
  push_cast
  field_simp
  ring

theorem step (x n : ℕ) (hx : 2 * n + 3 ≤ x) :
    ((n : ℚ) + 1) ^ 2 * S x (n + 1) = ((x : ℚ) - 2 * n - 1) * ((x : ℚ) + 2 * n + 2) * S x n := by
  set G : ℕ → ℚ := fun j =>
    -((j : ℚ)) ^ 2 * (x.choose j : ℚ) ^ 2 * ((x - n - 1 - j).choose (n + 1 - j) : ℚ) with hG
  have tel : ∑ j ∈ range (n + 1),
      (((n : ℚ) + 1) ^ 2 * ((x.choose j : ℚ) ^ 2 * ((x - (n + 1) - 1 - j).choose (n + 1 - j) : ℚ))
        - ((x : ℚ) - 2 * n - 1) * ((x : ℚ) + 2 * n + 2)
          * ((x.choose j : ℚ) ^ 2 * ((x - n - 1 - j).choose (n - j) : ℚ)))
      = G (n + 1) - G 0 := by
    rw [← Finset.sum_range_sub G]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [hG]
    exact term x n j (by omega) hx
  have g0 : G 0 = 0 := by simp [hG]
  have g1 : G (n + 1) = -((n : ℚ) + 1) ^ 2 * (x.choose (n + 1) : ℚ) ^ 2 := by
    simp only [hG]
    have : n + 1 - (n + 1) = 0 := by omega
    rw [this, Nat.choose_zero_right]; push_cast; ring
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, g0, g1] at tel
  unfold S
  rw [Finset.sum_range_succ (fun j => (x.choose j : ℚ) ^ 2 * ((x - (n + 1) - 1 - j).choose (n + 1 - j) : ℚ))]
  have : n + 1 - (n + 1) = 0 := by omega
  rw [this, Nat.choose_zero_right]
  push_cast
  linear_combination tel

theorem closed (x n : ℕ) (hx : 2 * n + 1 ≤ x) :
    S x n * ((n.factorial : ℚ)) ^ 2 = P x n := by
  induction n with
  | zero =>
    simp [S, P]
  | succ n ih =>
    have h := step x n (by omega)
    have ih' := ih (by omega)
    rw [P, Finset.prod_range_succ, ← P, ← ih', Nat.factorial_succ]
    push_cast
    linear_combination ((n.factorial : ℚ)) ^ 2 * h

end LtsDixon

/-! Generic supercongruence for a(N) = C(c1 N, N) C(c2 N, N) κ ∏_{i<N} (α N + 2i)/(β N + 2i). -/

namespace LtsDixonApp
open Nat LtsJacobsthal Finset

/-- `Gg α β N = ∏_{i<N} (α N + 2 i) / (β N + 2 i)` -/
def Gg (α β N : ℕ) : ℚ := ∏ i ∈ range N, (((α : ℚ) * N + 2 * i) / ((β : ℚ) * N + 2 * i))

lemma fact2 (B j : ℕ) :
    (((B + 2 * j)! : ℕ) : ℚ) = (B ! : ℚ) * ∏ i ∈ range j, (((B : ℚ) + 2 * i + 1) * ((B : ℚ) + 2 * i + 2)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show B + 2 * (j + 1) = (B + 2 * j) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      prod_range_succ]
    push_cast
    rw [ih]; ring

lemma lin_shift (a N : ℕ) :
    (∏ i ∈ range N, ((a : ℚ) * N + 2 * i + 2)) * ((a : ℚ) * N)
      = (∏ i ∈ range N, ((a : ℚ) * N + 2 * i)) * ((a : ℚ) * N + 2 * N) := by
  set h : ℕ → ℚ := fun i => (a : ℚ) * N + 2 * i with hh
  have e1 := prod_range_succ' h N
  have e2 := prod_range_succ h N
  have e := e1.symm.trans e2
  simp only [hh, Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero] at e
  have hs : ∏ i ∈ range N, ((a : ℚ) * N + 2 * i + 2) = ∏ i ∈ range N, ((a : ℚ) * N + 2 * ((i : ℚ) + 1)) :=
    prod_congr rfl fun i _ => by ring
  rw [hs]
  linear_combination e

lemma Gg_shift (α β N : ℕ) (hα : 1 ≤ α) (hβ : 1 ≤ β) (hN : 1 ≤ N) :
    Gg α β N * (((α : ℚ) + 2) * (β : ℚ)) =
      (∏ i ∈ range N, ((α : ℚ) * N + 2 * i + 2)) / (∏ i ∈ range N, ((β : ℚ) * N + 2 * i + 2))
        * ((α : ℚ) * ((β : ℚ) + 2)) := by
  have hN0 : (0 : ℚ) < N := by exact_mod_cast hN
  have ha0 : (0 : ℚ) < α := by exact_mod_cast hα
  have hb0 : (0 : ℚ) < β := by exact_mod_cast hβ
  have s1 := lin_shift α N
  have s2 := lin_shift β N
  have hG : Gg α β N = (∏ i ∈ range N, ((α : ℚ) * N + 2 * i)) / ∏ i ∈ range N, ((β : ℚ) * N + 2 * i) := by
    unfold Gg; rw [prod_div_distrib]
  have p1 : (∏ i ∈ range N, ((β : ℚ) * N + 2 * i)) ≠ 0 := by
    rw [prod_ne_zero_iff]; intro i _; positivity
  have p2 : (∏ i ∈ range N, ((β : ℚ) * N + 2 * i + 2)) ≠ 0 := by
    rw [prod_ne_zero_iff]; intro i _; positivity
  rw [hG, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff p1 p2]
  have hN' : (N : ℚ) ≠ 0 := hN0.ne'
  apply mul_left_cancel₀ hN'
  linear_combination (-(β : ℚ) * (∏ i ∈ range N, ((β : ℚ) * N + 2 * i + 2))) * s1
    + (α : ℚ) * (∏ i ∈ range N, ((α : ℚ) * N + 2 * i + 2)) * s2

variable {p : ℕ} [hp : Fact p.Prime]

lemma G_split (hp0 : 0 < p) (α β M : ℕ) :
    Gg α β (p * M) = Gg α β M * (R p (-((α : ℚ) / 2 * (p : ℚ) * (M : ℚ))) (p * M) /
      R p (-((β : ℚ) / 2 * (p : ℚ) * (M : ℚ))) (p * M)) := by
  unfold Gg
  rw [prod_range_mul_split p M hp0]
  have hA : ∏ k ∈ (range (p * M)).filter (fun k => ¬ p ∣ k),
      (((α : ℚ) * ((p * M : ℕ) : ℚ) + 2 * (k : ℚ)) / ((β : ℚ) * ((p * M : ℕ) : ℚ) + 2 * (k : ℚ))) =
      R p (-((α : ℚ) / 2 * (p : ℚ) * (M : ℚ))) (p * M) /
        R p (-((β : ℚ) / 2 * (p : ℚ) * (M : ℚ))) (p * M) := by
    unfold R U
    rw [← prod_div_distrib]
    refine prod_congr rfl fun i hi => ?_
    have hi0 : (i : ℚ) ≠ 0 := by
      have : i ≠ 0 := by
        rintro rfl
        simp at hi
      exact_mod_cast this
    have e1 : 1 - (-((α : ℚ) / 2 * (p : ℚ) * (M : ℚ))) / (i : ℚ) =
        ((α : ℚ) * ((p * M : ℕ) : ℚ) + 2 * (i : ℚ)) / (2 * (i : ℚ)) := by
      push_cast; field_simp; ring
    have e2 : 1 - (-((β : ℚ) / 2 * (p : ℚ) * (M : ℚ))) / (i : ℚ) =
        ((β : ℚ) * ((p * M : ℕ) : ℚ) + 2 * (i : ℚ)) / (2 * (i : ℚ)) := by
      push_cast; field_simp; ring
    rw [e1, e2, div_div_div_cancel_right₀ (mul_ne_zero two_ne_zero hi0)]
  have hB : ∏ c ∈ range M,
      (((α : ℚ) * ((p * M : ℕ) : ℚ) + 2 * ((p * c : ℕ) : ℚ)) /
        ((β : ℚ) * ((p * M : ℕ) : ℚ) + 2 * ((p * c : ℕ) : ℚ))) =
      ∏ c ∈ range M, (((α : ℚ) * (M : ℚ) + 2 * (c : ℚ)) / ((β : ℚ) * (M : ℚ) + 2 * (c : ℚ))) := by
    refine prod_congr rfl fun c _ => ?_
    push_cast
    have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
    rw [show (α : ℚ) * ((p : ℚ) * M) + 2 * (p * c) = p * (α * M + 2 * c) by ring,
      show (β : ℚ) * ((p : ℚ) * M) + 2 * (p * c) = p * (β * M + 2 * c) by ring, mul_div_mul_left _ _ hp']
  rw [hA, hB]; ring

/-- `R_D` with a `p`-integral rational coefficient -/
lemma R_D' (h5 : 5 ≤ p) {s : ℕ} (hs : 1 ≤ s) (A : ℚ) (hA : D p 0 A) (t : ℕ) :
    D p (3 * s) (R p (A * (p : ℚ) ^ s) (t * p ^ s) - 1) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨W, hW, hprod⟩ := prod_expand2 hp2 (U p (t * p ^ s)) (fun i => A * ((i : ℚ)⁻¹))
    ((p : ℚ) ^ s) ((D.ppow s).le (Nat.zero_le _))
    (fun i hi => hA.mul0 (D.inv (mem_U.mp hi).2))
  have hR : R p (A * (p : ℚ) ^ s) (t * p ^ s) =
      ∏ i ∈ U p (t * p ^ s), (1 - (p : ℚ) ^ s * (A * ((i : ℚ)⁻¹))) := by
    unfold R
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_eq_mul_inv]; ring
  have h1 : ∑ i ∈ U p (t * p ^ s), A * ((i : ℚ)⁻¹) = A * sg p (t * p ^ s) 1 := by
    unfold sg; rw [Finset.mul_sum]; simp only [pow_one]
  have h2 : ∑ i ∈ U p (t * p ^ s), (A * ((i : ℚ)⁻¹)) ^ 2 =
      A ^ 2 * sg p (t * p ^ s) 2 := by
    unfold sg; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hR, hprod, h1, h2]
  have hS1 := S1_D h5 hs t
  have hS2 := S2_D h5 hs t
  have hi2 : D p 0 ((2 : ℚ)⁻¹) := by simpa using D.inv (p := p) hp2
  have e1 : D p (3 * s) ((p : ℚ) ^ s * (A * sg p (t * p ^ s) 1)) :=
    ((D.ppow s).mul (hA.mul0' hS1)).le (by omega)
  have e2 : D p (3 * s) (((p : ℚ) ^ s) ^ 2 *
      ((A * sg p (t * p ^ s) 1) ^ 2 - A ^ 2 * sg p (t * p ^ s) 2)) := by
    have hin : D p s ((A * sg p (t * p ^ s) 1) ^ 2 - A ^ 2 * sg p (t * p ^ s) 2) :=
      (((hA.mul0' hS1).pow 2).le (by omega)).sub ((hA.pow0 2).mul0' hS2)
    exact (((D.ppow s).pow 2).mul hin).le (by omega)
  have e3 : D p (3 * s) (((p : ℚ) ^ s) ^ 3 * W) :=
    (((D.ppow s).pow 3).mul0 hW).le (by omega)
  exact ((e1.neg.add (e2.mul0 hi2)).add e3).congr (by ring)

lemma rho (h5 : 5 ≤ p) (a b r : ℕ) (hr : 1 ≤ r) :
    ∃ ρ : ℚ, D p (3 * r) (ρ - 1) ∧ ((a * p ^ r).choose (b * p ^ r) : ℚ) =
      ((a * p ^ (r - 1)).choose (b * p ^ (r - 1)) : ℚ) * ρ := by
  have hp2 : p ≠ 2 := by omega
  have hc := choose_ratio (p := p) hp2 (a * p ^ (r - 1)) (b * p ^ (r - 1))
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hc ⊢
  have e1 : p * (a * p ^ k) = a * p ^ (k + 1) := by ring
  have e2 : p * (b * p ^ k) = b * p ^ (k + 1) := by ring
  rw [e1, e2] at hc
  have e3 : ((a * p ^ (k + 1) : ℕ) : ℚ) = (a : ℚ) * (p : ℚ) ^ (k + 1) := by push_cast; ring
  rw [e3] at hc
  exact ⟨_, R_D h5 (by omega : 1 ≤ k + 1) a b, hc⟩

lemma D_inv_unit {e : ℕ} {x : ℚ} (he : 1 ≤ e) (h : D p e (x - 1)) : D p 0 x⁻¹ := by
  obtain ⟨a, b, hb, hab⟩ := h
  set c : ℤ := (b : ℤ) + (p : ℤ) ^ e * a with hcdef
  have hpc : ¬ (p : ℤ) ∣ c := by
    intro hd
    apply hb
    have h2 : (p : ℤ) ∣ (p : ℤ) ^ e * a := Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
    exact Int.natCast_dvd_natCast.mp ((dvd_add_left h2).mp hd)
  have hc0 : c ≠ 0 := fun h0 => hpc (h0 ▸ dvd_zero _)
  have hxc : x * (b : ℚ) = (c : ℚ) := by
    rw [hcdef]; push_cast; linear_combination hab
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hxc; exact hc0 (by exact_mod_cast hxc.symm)
  have hinv : x⁻¹ * (c : ℚ) = (b : ℚ) := by rw [← hxc]; field_simp
  have hpn : ¬ p ∣ c.natAbs := by
    intro hd; apply hpc
    exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hd)
  rcases Int.natAbs_eq c with hc | hc
  · refine ⟨(b : ℤ), c.natAbs, hpn, ?_⟩
    have h' : (c : ℚ) = ((c.natAbs : ℕ) : ℚ) := by rw [← Int.cast_natCast, ← hc]
    rw [pow_zero, one_mul, Int.cast_natCast]
    linear_combination -x⁻¹ * h' + hinv
  · refine ⟨-(b : ℤ), c.natAbs, hpn, ?_⟩
    have h' : (c : ℚ) = -((c.natAbs : ℕ) : ℚ) := by rw [← Int.cast_natCast, ← Int.cast_neg, ← hc]
    rw [pow_zero, one_mul, Int.cast_neg, Int.cast_natCast]
    linear_combination x⁻¹ * h' - hinv

lemma D_one_add {e : ℕ} {x : ℚ} (h : D p e (x - 1)) : D p 0 x :=
  ((h.le (Nat.zero_le _)).add D.one).congr (by ring)

lemma D_ne_zero {e : ℕ} {x : ℚ} (he : 1 ≤ e) (h : D p e (x - 1)) : x ≠ 0 := by
  intro hx
  obtain ⟨a, b, hb, h⟩ := h
  rw [hx] at h
  have h2 : (b : ℤ) = (p : ℤ) ^ e * (-a) := by
    have : ((b : ℚ)) = (p : ℚ) ^ e * (-(a : ℚ)) := by linear_combination -h
    exact_mod_cast this
  apply hb
  have : (p : ℤ) ∣ (b : ℤ) := by
    rw [h2]; exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
  exact Int.natCast_dvd_natCast.mp this

theorem main_gen (h5 : 5 ≤ p) (c1 c2 α β : ℕ) (κ : ℚ) (f : ℕ → ℚ)
    (hf : ∀ N, 1 ≤ N → f N = ((c1 * N).choose N : ℚ) * ((c2 * N).choose N : ℚ) * κ * Gg α β N)
    (hint : ∀ M, D p 0 (f M)) (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    D p (3 * r) (f (n * p ^ r) - f (n * p ^ (r - 1))) := by
  have hp0 : 0 < p := hp.out.pos
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hM : 1 ≤ n * p ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hNM : n * p ^ (k + 1) = p * (n * p ^ k) := by ring
  have hN1 : 1 ≤ p * (n * p ^ k) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  obtain ⟨ρ1, d1, h1⟩ := rho h5 (c1 * n) n (k + 1) (by omega)
  obtain ⟨ρ2, d2, h2⟩ := rho h5 (c2 * n) n (k + 1) (by omega)
  simp only [Nat.add_sub_cancel] at h1 h2
  have hA1 : D p 0 (-((α : ℚ) / 2 * (n : ℚ))) :=
    ((((D.nat α).mul0 (D.inv hp2)).mul0 (D.nat n)).neg).congr (by push_cast; ring)
  have hA2 : D p 0 (-((β : ℚ) / 2 * (n : ℚ))) :=
    ((((D.nat β).mul0 (D.inv hp2)).mul0 (D.nat n)).neg).congr (by push_cast; ring)
  have dR1 := R_D' h5 (by omega : 1 ≤ k + 1) _ hA1 n
  have dR2 := R_D' h5 (by omega : 1 ≤ k + 1) _ hA2 n
  set R1 := R p (-((α : ℚ) / 2 * (n : ℚ)) * (p : ℚ) ^ (k + 1)) (n * p ^ (k + 1)) with hR1
  set R2 := R p (-((β : ℚ) / 2 * (n : ℚ)) * (p : ℚ) ^ (k + 1)) (n * p ^ (k + 1)) with hR2
  have eR1 : R p (-((α : ℚ) / 2 * (p : ℚ) * ((n * p ^ k : ℕ) : ℚ))) (p * (n * p ^ k)) = R1 := by
    rw [hR1]; congr 1
    · push_cast; ring
    · ring
  have eR2 : R p (-((β : ℚ) / 2 * (p : ℚ) * ((n * p ^ k : ℕ) : ℚ))) (p * (n * p ^ k)) = R2 := by
    rw [hR2]; congr 1
    · push_cast; ring
    · ring
  have hG := G_split hp0 α β (n * p ^ k)
  rw [eR1, eR2] at hG
  have hc1 : ((c1 * (p * (n * p ^ k))).choose (p * (n * p ^ k)) : ℚ) =
      ((c1 * (n * p ^ k)).choose (n * p ^ k) : ℚ) * ρ1 := by
    rw [show c1 * (p * (n * p ^ k)) = c1 * n * p ^ (k + 1) by ring,
      show p * (n * p ^ k) = n * p ^ (k + 1) by ring, h1,
      show c1 * n * p ^ k = c1 * (n * p ^ k) by ring]
  have hc2 : ((c2 * (p * (n * p ^ k))).choose (p * (n * p ^ k)) : ℚ) =
      ((c2 * (n * p ^ k)).choose (n * p ^ k) : ℚ) * ρ2 := by
    rw [show c2 * (p * (n * p ^ k)) = c2 * n * p ^ (k + 1) by ring,
      show p * (n * p ^ k) = n * p ^ (k + 1) by ring, h2,
      show c2 * n * p ^ k = c2 * (n * p ^ k) by ring]
  have hR2ne : R2 ≠ 0 := D_ne_zero (by omega) dR2
  have e123 : D p (3 * (k + 1)) (ρ1 * ρ2 * R1 - R2) :=
    ((((d1.mul0 ((D_one_add d2).mul0 (D_one_add dR1))).add (d2.mul0 (D_one_add dR1))).add dR1).sub
      dR2).congr (by ring)
  have key := (hint (n * p ^ k)).mul0' (e123.mul0 (D_inv_unit (by omega) dR2))
  refine key.congr ?_
  rw [hNM, hf (p * (n * p ^ k)) hN1, hf (n * p ^ k) hM, hG, hc1, hc2]
  field_simp

end LtsDixonApp

namespace A275654P
open Nat LtsJacobsthal LtsDixon LtsDixonApp Finset
open OMA.S_oeis_a275654

lemma a_eq (N : ℕ) (hN : 1 ≤ N) :
    ((a N : ℤ) : ℚ) = ((5 * N).choose N : ℚ) * ((4 * N).choose N : ℚ) * (21 / 25) * Gg 5 3 N := by
  have hS : ((a N : ℤ) : ℚ) = S (5 * N) N := by
    unfold a S
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [show 5 * N - N - 1 - j = 4 * N - j - 1 by omega]; ring
  have hc := closed (5 * N) N (by omega)
  set X := ∏ i ∈ range N, (3 * (N : ℚ) + 2 * i + 1) with hX
  set Y := ∏ i ∈ range N, (3 * (N : ℚ) + 2 * i + 2) with hY
  set Z := ∏ i ∈ range N, (5 * (N : ℚ) + 2 * i + 2) with hZ
  have hP : P (5 * N) N = X * Z := by
    unfold P
    rw [prod_mul_distrib]
    congr 1
    · rw [hX, ← prod_range_reflect (fun i => (3 * (N : ℚ) + 2 * i + 1)) N]
      refine prod_congr rfl fun i hi => ?_
      rw [mem_range] at hi
      have e : (N - 1 - i) + i + 1 = N := by omega
      have e' := congrArg (Nat.cast (R := ℚ)) e
      push_cast at e' ⊢
      linear_combination (-2 : ℚ) * e'
    · rw [hZ]; refine prod_congr rfl fun i _ => ?_
      push_cast; ring
  have hF := fact2 (3 * N) N
  rw [show 3 * N + 2 * N = 5 * N by ring, prod_mul_distrib] at hF
  push_cast at hF
  have hsh := Gg_shift 5 3 N (by norm_num) (by norm_num) hN
  push_cast at hsh
  have hYne : Y ≠ 0 := by rw [hY, prod_ne_zero_iff]; intro i _; positivity
  have hG : Gg 5 3 N = Z / Y * (25 / 21) := by
    rw [hZ, hY]; linear_combination hsh / 21
  have c1 := Nat.cast_choose ℚ (show N ≤ 5 * N by omega)
  have c2 := Nat.cast_choose ℚ (show N ≤ 4 * N by omega)
  rw [show 5 * N - N = 4 * N by omega] at c1
  rw [show 4 * N - N = 3 * N by omega] at c2
  have hS' : S (5 * N) N = X * Z / ((N ! : ℚ)) ^ 2 := by
    rw [eq_div_iff (by positivity), hc, hP]
  rw [hS, hS', hG, c1, c2, hF]
  have f1 : ((N ! : ℕ) : ℚ) ≠ 0 := by positivity
  have f3 : (((3 * N) ! : ℕ) : ℚ) ≠ 0 := by positivity
  have f4 : (((4 * N) ! : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp
  ring

end A275654P

theorem OMA.solution : type_of% @OMA.S_oeis_a275654.main := by
  intro p hp h5 n hn k hk
  have := Fact.mk hp
  have h := LtsDixonApp.main_gen h5 5 4 5 3 (21 / 25)
    (fun N => ((OMA.S_oeis_a275654.a N : ℤ) : ℚ)) (fun N hN => A275654P.a_eq N hN)
    (fun M => LtsJacobsthal.D.int _) n k hn hk
  have hd := LtsJacobsthal.D.dvd
    (z := OMA.S_oeis_a275654.a (n * p ^ k) - OMA.S_oeis_a275654.a (n * p ^ (k - 1)))
    (h.congr (by push_cast; ring))
  exact (Int.modEq_iff_dvd.mpr hd).symm
