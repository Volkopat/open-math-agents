import OMAStatements.S_oeis_a241023
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

end LtsJacobsthal

namespace A241023
open Finset LtsJacobsthal

/-- `cc m = 1 - (-1)^m`. -/
def cc (m : ℕ) : ℚ := if m % 2 = 0 then 0 else 2

/-- `CT p T = [x^T] L^2`, written as a sum over the units below `T`. -/
def CT (p T : ℕ) : ℚ := ∑ m ∈ U p T, cc m * cc (T - m) / ((m : ℚ) * ((T - m : ℕ) : ℚ))

variable {p : ℕ} [hp : Fact p.Prime]

lemma Dq (z : ℤ) (x : ℚ) (h : x = z) : D p 0 x := h ▸ D.int z

omit hp in
lemma U_pos {L m : ℕ} (hm : m ∈ U p L) : 0 < m ∧ m < L := by
  obtain ⟨h1, h2⟩ := mem_U.mp hm
  refine ⟨Nat.pos_of_ne_zero ?_, h1⟩
  rintro rfl; exact h2 (dvd_zero p)

lemma sum_evens (hp2 : p ≠ 2) (W : ℕ) :
    ∑ m ∈ U p (2 * W), (if m % 2 = 0 then ((m : ℚ))⁻¹ else 0) = (1 / 2) * sg p W 1 := by
  rw [← Finset.sum_filter]
  have himg : (U p (2 * W)).filter (fun m => m % 2 = 0) = (U p W).image (fun u => 2 * u) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_image, mem_U]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨m / 2, ⟨by omega, ?_⟩, by omega⟩
      intro hd; apply h2
      have : m = 2 * (m / 2) := by omega
      rw [this]; exact dvd_mul_of_dvd_right hd 2
    · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      intro hd
      rcases (Nat.Prime.dvd_mul hp.out).mp hd with h | h
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
      · exact h2 h
  rw [himg, Finset.sum_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left two_pos h)]
  unfold sg
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  push_cast; ring

omit hp in
lemma T_CT {T : ℕ} (hT : p ∣ T) :
    (T : ℚ) * CT p T = 2 * ∑ m ∈ U p T, cc m * cc (T - m) / (m : ℚ) := by
  have key : ∀ m ∈ U p T, (T : ℚ) * (cc m * cc (T - m) / ((m : ℚ) * ((T - m : ℕ) : ℚ)))
      = cc m * cc (T - m) / (m : ℚ) + cc (T - m) * cc (T - (T - m)) / ((T - m : ℕ) : ℚ) := by
    intro m hm
    obtain ⟨h0, h1⟩ := U_pos hm
    have e1 : T - (T - m) = m := by omega
    rw [e1]
    have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hc : ((T - m : ℕ) : ℚ) = (T : ℚ) - m := by rw [Nat.cast_sub h1.le]
    have hTm : (T : ℚ) - m ≠ 0 := by rw [← hc]; exact Nat.cast_ne_zero.mpr (by omega)
    rw [hc]
    field_simp
    ring
  unfold CT
  rw [Finset.mul_sum, Finset.sum_congr rfl key, Finset.sum_add_distrib]
  have h2 := sum_U_reflect hT (fun x => cc x * cc (T - x) / ((x : ℕ) : ℚ))
  rw [← h2]
  ring

lemma CT_D (h5 : 5 ≤ p) {e w : ℕ} (he : 1 ≤ e) (hw : ¬ p ∣ w) : D p e (CT p (w * p ^ e)) := by
  have hp2 : p ≠ 2 := by omega
  have hpT : p ∣ w * p ^ e := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) w
  have hmain : D p (2 * e) (((w * p ^ e : ℕ) : ℚ) * CT p (w * p ^ e)) := by
    rw [T_CT hpT]
    rcases Nat.even_or_odd w with ⟨W, hW⟩ | hodd
    · have hT2 : w * p ^ e = 2 * (W * p ^ e) := by rw [hW]; ring
      have hsum : ∑ m ∈ U p (w * p ^ e), cc m * cc (w * p ^ e - m) / (m : ℚ)
          = 4 * sg p (w * p ^ e) 1
            - 4 * ∑ m ∈ U p (w * p ^ e), (if m % 2 = 0 then ((m : ℚ))⁻¹ else 0) := by
        unfold sg
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun m hm => ?_
        obtain ⟨h0, h1⟩ := U_pos hm
        have hTe : (w * p ^ e) % 2 = 0 := by omega
        unfold cc
        split_ifs <;> first | omega | ring
      rw [hsum]
      rw [hT2, sum_evens hp2 (W * p ^ e), ← hT2]
      have hA := S1_D h5 he w
      have hB := S1_D h5 he W
      exact ((((Dq 4 (4 : ℚ) (by norm_num)).mul0' hA).sub
        ((Dq 2 (2 : ℚ) (by norm_num)).mul0' hB)).mul0 (Dq 2 (2 : ℚ) (by norm_num) : D p 0 (2 : ℚ))).congr
        (by ring)
    · have hTo : (w * p ^ e) % 2 = 1 :=
        Nat.odd_iff.mp (hodd.mul ((hp.out.odd_of_ne_two hp2).pow))
      have hsum : ∑ m ∈ U p (w * p ^ e), cc m * cc (w * p ^ e - m) / (m : ℚ)
          = 0 * sg p (w * p ^ e) 1 := by
        unfold sg
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        obtain ⟨h0, h1⟩ := U_pos hm
        unfold cc
        split_ifs <;> first | omega | ring
      rw [hsum]
      exact ((Dq 0 (0 : ℚ) (by norm_num)).mul0' (S1_D h5 he w)).mul0
        (Dq 2 (2 : ℚ) (by norm_num) : D p 0 (2 : ℚ)) |>.congr (by ring)
  have h3 : D p (e + e) ((p : ℚ) ^ e * ((w : ℚ) * CT p (w * p ^ e))) := by
    rw [← two_mul]
    exact hmain.congr (by push_cast; ring)
  exact D.ucancel hw (D.cancel h3)

lemma CT_D' (h5 : 5 ≤ p) {t g : ℕ} (ht : 0 < t) (hg : p ^ g ∣ t) :
    D p (g + 1) (CT p (p * t)) := by
  obtain ⟨e, w, hw, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd ht.ne' p hp.out.one_lt.ne'
  have hge : g ≤ e := by
    have h1 : p ^ g ∣ p ^ e :=
      (Nat.Coprime.pow_left g ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hw)).dvd_of_dvd_mul_right hg
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp h1
  have h := CT_D h5 (e := e + 1) (by omega) hw
  rw [show w * p ^ (e + 1) = p * (p ^ e * w) by ring] at h
  exact h.le (by omega)

end A241023

namespace A241023
open Finset PowerSeries LtsJacobsthal

lemma deriv_factor (Y A G : PowerSeries ℚ) (hY0 : constantCoeff Y = 0) (hA : (1 + Y) * A = 1)
    (hG : (1 - Y) * G = 1) :
    derivative ℚ ((1 + Y) * G) = derivative ℚ Y * (A + G) * ((1 + Y) * G) := by
  have hd1 : derivative ℚ ((1 + Y) * G)
      = derivative ℚ Y * G + (1 + Y) * derivative ℚ G := by
    rw [Derivation.leibniz, map_add, Derivation.map_one_eq_zero]
    simp only [smul_eq_mul, zero_add]
    ring
  have hGd : (1 - Y) * derivative ℚ G = derivative ℚ Y * G := by
    have h1 := congrArg (derivative ℚ) hG
    rw [Derivation.leibniz, map_sub, Derivation.map_one_eq_zero] at h1
    simp only [smul_eq_mul] at h1
    linear_combination h1
  have hne : (1 - Y) * (1 + Y) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp [hY0] at this
  apply mul_left_cancel₀ hne
  rw [hd1]
  linear_combination (-derivative ℚ Y * (1 + Y) * (1 - Y) * G) * hA
    + (-derivative ℚ Y * (1 + Y) ^ 2 * G) * hG + (1 + Y) ^ 2 * hGd

noncomputable def Gs : PowerSeries ℚ := mk 1
noncomputable def As : PowerSeries ℚ := mk fun n => (-1 : ℚ) ^ n
noncomputable def Fs : PowerSeries ℚ := (1 + X) * Gs
noncomputable def Phi : PowerSeries ℚ := mk fun n => cc (n + 1)
noncomputable def Ls (p : ℕ) : PowerSeries ℚ := mk fun m => if p ∣ m then 0 else cc m / (m : ℚ)
noncomputable def EK (p K : ℕ) (M : ℚ) : PowerSeries ℚ :=
  ∑ d ∈ range (K + 1), C (M ^ d / (d.factorial : ℚ)) * Ls p ^ d

lemma hGs : (1 - X) * Gs = 1 := by rw [mul_comm]; exact mk_one_mul_one_sub_eq_one ℚ

lemma hAs : (1 + X) * As = 1 := by
  ext n
  rw [add_mul, one_mul, map_add]
  rcases n with _ | n
  · simp [As]
  · rw [coeff_succ_X_mul]; simp [As, pow_succ]

lemma cc_succ (n : ℕ) : cc (n + 1) = (-1 : ℚ) ^ n + 1 := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow]
    have : (n + 1) % 2 = 1 := by rcases h with ⟨k, rfl⟩; omega
    simp [cc, this]; try norm_num
  · rw [h.neg_one_pow]
    have : (n + 1) % 2 = 0 := by rcases h with ⟨k, rfl⟩; omega
    simp [cc, this]

lemma Phi_eq : Phi = As + Gs := by
  ext n
  rw [map_add]
  simp only [Phi, As, Gs, coeff_mk, Pi.one_apply]
  exact cc_succ n

lemma deriv_Fs : derivative ℚ Fs = Phi * Fs := by
  have h := deriv_factor X As Gs (by simp) hAs hGs
  rw [derivative_X, one_mul, ← Phi_eq] at h
  exact h

lemma deriv_expand_Fs {p : ℕ} (hp0 : p ≠ 0) :
    derivative ℚ (expand p hp0 Fs)
      = (C (p : ℚ) * X ^ (p - 1)) * expand p hp0 Phi * expand p hp0 Fs := by
  have hA : (1 + X ^ p) * expand p hp0 As = 1 := by
    have := congrArg (expand p hp0) hAs
    rwa [map_mul, map_add, map_one, expand_X] at this
  have hG : (1 - X ^ p) * expand p hp0 Gs = 1 := by
    have := congrArg (expand p hp0) hGs
    rwa [map_mul, map_sub, map_one, expand_X] at this
  have h := deriv_factor (X ^ p) (expand p hp0 As) (expand p hp0 Gs)
    (by simp [zero_pow hp0]) hA hG
  have hF : expand p hp0 Fs = (1 + X ^ p) * expand p hp0 Gs := by
    rw [Fs, map_mul, map_add, map_one, expand_X]
  have hPhi : expand p hp0 Phi = expand p hp0 As + expand p hp0 Gs := by
    rw [Phi_eq, map_add]
  rw [hF, h, hPhi, Derivation.leibniz_pow, derivative_X]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_one]
  rw [show ((p : PowerSeries ℚ)) = C (p : ℚ) from (map_natCast C p).symm]

lemma cc_mul_odd {q k : ℕ} (hq : q % 2 = 1) : cc (q * k) = cc k := by
  unfold cc
  have : (q * k) % 2 = k % 2 := by rw [Nat.mul_mod, hq]; omega
  rw [this]

lemma deriv_Ls {p : ℕ} (hp0 : p ≠ 0) (hp2 : p % 2 = 1) :
    derivative ℚ (Ls p) = Phi - X ^ (p - 1) * expand p hp0 Phi := by
  ext n
  rw [coeff_derivative, map_sub, coeff_X_pow_mul', Ls, coeff_mk, Phi, coeff_mk]
  by_cases h : p ∣ n + 1
  · obtain ⟨k, hk⟩ := h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
      rcases k with _ | j
      · simp at hk
      · exact ⟨j, rfl⟩
    have hk' : n + 1 = p * j + p := by rw [hk]; ring
    have hle : p - 1 ≤ n := by
      have : p ≤ n + 1 := by rw [hk']; exact Nat.le_add_left p (p * j)
      omega
    have hsub : n - (p - 1) = p * j := by
      generalize p * j = P at hk'
      omega
    rw [if_pos ⟨j + 1, hk⟩, if_pos hle, hsub, coeff_expand_mul, coeff_mk, hk,
      cc_mul_odd hp2]
    ring
  · rw [if_neg h]
    have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
    have e1 : cc (n + 1) / ((n + 1 : ℕ) : ℚ) * ((n : ℚ) + 1) = cc (n + 1) := by
      push_cast; field_simp
    rw [e1]
    split_ifs with hle
    · rw [coeff_expand_of_not_dvd]
      · ring
      · intro hd
        apply h
        have : n + 1 = (n - (p - 1)) + p := by omega
        rw [this]
        exact Nat.dvd_add hd (dvd_refl p)
    · ring

lemma deriv_EK (p K : ℕ) (M : ℚ) :
    derivative ℚ (EK p K M) = C M * derivative ℚ (Ls p) *
      (EK p K M - C (M ^ K / (K.factorial : ℚ)) * Ls p ^ K) := by
  have hd : ∀ (r : ℚ) (f : PowerSeries ℚ), derivative ℚ (C r * f) = C r * derivative ℚ f := by
    intro r f
    rw [Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul]
  have hterm : ∀ d : ℕ, derivative ℚ (C (M ^ (d + 1) / ((d + 1).factorial : ℚ)) * Ls p ^ (d + 1))
      = C M * derivative ℚ (Ls p) * (C (M ^ d / (d.factorial : ℚ)) * Ls p ^ d) := by
    intro d
    rw [hd, derivative_pow, Nat.add_sub_cancel]
    have h1 : ((d + 1 : ℕ) : PowerSeries ℚ) = C ((d + 1 : ℕ) : ℚ) := (map_natCast C (d + 1)).symm
    have h2 : M ^ (d + 1) / ((d + 1).factorial : ℚ) * ((d + 1 : ℕ) : ℚ)
        = M * (M ^ d / (d.factorial : ℚ)) := by
      rw [Nat.factorial_succ]; push_cast
      have : (d.factorial : ℚ) ≠ 0 := by positivity
      field_simp
      ring
    rw [h1]
    calc C (M ^ (d + 1) / ((d + 1).factorial : ℚ)) * (C ((d + 1 : ℕ) : ℚ) * Ls p ^ d
          * derivative ℚ (Ls p))
        = C (M ^ (d + 1) / ((d + 1).factorial : ℚ) * ((d + 1 : ℕ) : ℚ)) * Ls p ^ d
          * derivative ℚ (Ls p) := by rw [map_mul]; ring
      _ = _ := by rw [h2, map_mul]; ring
  unfold EK
  conv_rhs => rw [Finset.sum_range_succ, add_sub_cancel_right]
  rw [map_sum, Finset.sum_range_succ', Finset.mul_sum]
  have h0 : derivative ℚ (C (M ^ 0 / ((Nat.factorial 0 : ℕ) : ℚ)) * Ls p ^ 0) = 0 := by
    simp
  rw [h0, add_zero]
  exact Finset.sum_congr rfl fun d _ => hterm d

lemma uniq (K : ℕ) (h ψ : PowerSeries ℚ) (h0 : constantCoeff h = 0)
    (hd : ∀ n < K, coeff n (derivative ℚ h - ψ * h) = 0) : ∀ n ≤ K, coeff n h = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | n
    · simpa using h0
    · have h1 := hd n (by omega)
      rw [map_sub, coeff_derivative, coeff_mul] at h1
      have h2 : ∑ x ∈ antidiagonal n, coeff x.1 ψ * coeff x.2 h = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
        rw [ih x.2 (by omega) (by omega), mul_zero]
      rw [h2, sub_zero] at h1
      have h3 : ((n : ℚ) + 1) ≠ 0 := by positivity
      exact (mul_eq_zero.mp h1).resolve_right h3

lemma constantCoeff_Ls (p : ℕ) : constantCoeff (Ls p) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Ls, coeff_mk]; simp

lemma constantCoeff_EK (p K : ℕ) (M : ℚ) : constantCoeff (EK p K M) = 1 := by
  rw [EK, map_sum, Finset.sum_range_succ']
  simp [constantCoeff_Ls]

lemma coeff_low (K k : ℕ) (hk : k < K) (A : PowerSeries ℚ) (p : ℕ) :
    coeff k (A * Ls p ^ K) = 0 := by
  obtain ⟨B, hB⟩ := X_dvd_iff.mpr (constantCoeff_Ls p)
  rw [hB, mul_pow, mul_left_comm, coeff_X_pow_mul', if_neg (by omega)]

lemma key_identity {p : ℕ} (hp0 : p ≠ 0) (hp2 : p % 2 = 1) (n : ℕ) :
    coeff (p * (n + 1)) (Fs ^ (p * (n + 1))) =
      coeff (p * (n + 1)) (expand p hp0 Fs ^ (n + 1) *
        EK p (p * (n + 1)) ((p * (n + 1) : ℕ) : ℚ)) := by
  obtain ⟨k, hk⟩ : ∃ k, p * (n + 1) = k + 1 :=
    ⟨p * (n + 1) - 1, by
      have : 0 < p * (n + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hp0) (Nat.succ_pos n)
      omega⟩
  set M : ℚ := ((p * (n + 1) : ℕ) : ℚ) with hM
  set E := EK p (p * (n + 1)) M with hE
  set Q := expand p hp0 Fs with hQ
  set R := C (M ^ (p * (n + 1)) / ((p * (n + 1)).factorial : ℚ)) with hR
  have hdE : derivative ℚ E = C M * derivative ℚ (Ls p) * (E - R * Ls p ^ (p * (n + 1))) :=
    deriv_EK p _ M
  have hdF := deriv_Fs
  have hdQ := deriv_expand_Fs hp0
  have hdL := deriv_Ls hp0 hp2
  have hCM : C M = C (p : ℚ) * C ((n + 1 : ℕ) : ℚ) := by rw [hM, ← map_mul]; push_cast; ring_nf
  have hzero := uniq (p * (n + 1)) (Fs ^ (p * (n + 1)) - Q ^ (n + 1) * E) (C M * Phi)
    (by
      rw [map_sub, map_mul, map_pow, map_pow, hE, constantCoeff_EK, hQ, constantCoeff_expand]
      simp [Fs, Gs])
    (by
      intro j hj
      have hid : derivative ℚ (Fs ^ (p * (n + 1)) - Q ^ (n + 1) * E)
          - C M * Phi * (Fs ^ (p * (n + 1)) - Q ^ (n + 1) * E)
          = (C M * derivative ℚ (Ls p) * Q ^ (n + 1) * R) * Ls p ^ (p * (n + 1)) := by
        rw [hk] at hdE
        rw [hk, map_sub, Derivation.leibniz, derivative_pow, derivative_pow, hdE, hdQ, hdF, hdL]
        simp only [smul_eq_mul, Nat.add_sub_cancel]
        rw [show ((k + 1 : ℕ) : PowerSeries ℚ) = C M by
          rw [hM, hk]; exact (map_natCast C (k + 1)).symm,
          show ((n + 1 : ℕ) : PowerSeries ℚ) = C ((n + 1 : ℕ) : ℚ) from
          (map_natCast C (n + 1)).symm, hCM]
        ring
      rw [hid]
      exact coeff_low _ j hj _ p)
    (p * (n + 1)) le_rfl
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

lemma sum_expand {p : ℕ} (hp0 : p ≠ 0) (f g : PowerSeries ℚ) (N : ℕ) :
    coeff (p * N) (expand p hp0 f * g)
      = ∑ k ∈ range (N + 1), coeff k f * coeff (p * N - p * k) g := by
  rw [coeff_mul]
  have hinj : Set.InjOn (fun k => (p * k, p * N - p * k)) (range (N + 1) : Set ℕ) := by
    intro a _ b _ h
    simp only [Prod.mk.injEq] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) h.1
  symm
  calc ∑ k ∈ range (N + 1), coeff k f * coeff (p * N - p * k) g
      = ∑ k ∈ range (N + 1), (fun x : ℕ × ℕ => coeff x.1 (expand p hp0 f) * coeff x.2 g)
          (p * k, p * N - p * k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [coeff_expand_mul]
    _ = ∑ x ∈ (range (N + 1)).image (fun k => (p * k, p * N - p * k)),
          coeff x.1 (expand p hp0 f) * coeff x.2 g :=
          (Finset.sum_image (f := fun x : ℕ × ℕ => coeff x.1 (expand p hp0 f) * coeff x.2 g) hinj).symm
    _ = _ := by
        apply Finset.sum_subset
        · intro x hx
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
          rw [Finset.HasAntidiagonal.mem_antidiagonal]
          have : p * k ≤ p * N := Nat.mul_le_mul_left p (by simp at hk; omega)
          omega
        · intro x hx hnot
          rw [coeff_expand_of_not_dvd, zero_mul]
          rintro ⟨k, hk⟩
          apply hnot
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
          refine Finset.mem_image.mpr ⟨k, ?_, ?_⟩
          · have : p * k ≤ p * N := by omega
            have := Nat.le_of_mul_le_mul_left this (Nat.pos_of_ne_zero hp0)
            simp; omega
          · ext <;> simp <;> omega

end A241023

namespace A241023
open Finset PowerSeries LtsJacobsthal

variable {p : ℕ} [hp : Fact p.Prime]

lemma D_cc (m : ℕ) : D p 0 (cc m) := by
  unfold cc
  split_ifs
  · exact Dq 0 (0 : ℚ) (by norm_num)
  · exact Dq 2 (2 : ℚ) (by norm_num)

lemma D_Ls (m : ℕ) : D p 0 (coeff m (Ls p)) := by
  rw [Ls, coeff_mk]
  split_ifs with h
  · exact D.zero 0
  · rw [div_eq_mul_inv]; exact (D_cc m).mul0 (D.inv h)

lemma D_Lpow (d j : ℕ) : D p 0 (coeff j (Ls p ^ d)) := by
  induction d generalizing j with
  | zero =>
    rw [pow_zero, coeff_one]
    split_ifs
    · exact D.one
    · exact D.zero 0
  | succ d ih =>
    rw [pow_succ, coeff_mul]
    exact D.sum _ _ fun x _ => (ih x.1).mul0 (D_Ls x.2)

lemma D_of_dvd {e z : ℕ} (h : p ^ e ∣ z) : D p e (z : ℚ) := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c, 1, hp.out.not_dvd_one, by push_cast; ring⟩

omit hp in
lemma coeff_L2 {T : ℕ} (hT : p ∣ T) : coeff T (Ls p ^ 2) = CT p T := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
  have hlast : coeff T (Ls p) * coeff (T - T) (Ls p) = 0 := by
    rw [Ls, coeff_mk, if_pos hT, zero_mul]
  rw [hlast, add_zero, CT, U, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmT := Finset.mem_range.mp hm
  rw [Ls, coeff_mk, coeff_mk]
  dsimp only
  by_cases h : p ∣ m
  · simp [h]
  · have h' : ¬ p ∣ T - m := by
      intro hd
      obtain ⟨d, hd'⟩ : ∃ d, T = m + d := ⟨T - m, by omega⟩
      rw [hd', Nat.add_sub_cancel_left] at hd
      rw [hd'] at hT
      exact h ((Nat.dvd_add_left hd).mp hT)
    rw [if_neg h, if_neg h', if_pos h]
    rw [div_mul_div_comm]

lemma D_tail (h5 : 5 ≤ p) {s M : ℕ} (hs : 1 ≤ s) (hM : p ^ s ∣ M) (d : ℕ) (lam : ℚ)
    (hl : D p 0 lam) :
    D p (3 * s) ((M : ℚ) ^ (d + 3) / ((d + 3).factorial : ℚ) * lam) := by
  obtain ⟨μ, rfl⟩ := hM
  obtain ⟨v, w, hw, hfw⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero (d + 3)) p hp.out.one_lt.ne'
  have hw0' : w ≠ 0 := by rintro rfl; exact hw (dvd_zero p)
  have hv : padicValNat p (d + 3).factorial = v := by
    rw [hfw, padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hw0',
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hw, add_zero]
  have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (show d + 3 ≠ 0 by omega)
  rw [hv] at hlt
  have h4v : 4 * v ≤ (p - 1) * v := Nat.mul_le_mul_right v (by omega)
  have hvd : v ≤ d := by omega
  have hsd0 : d ≤ s * d := Nat.le_mul_of_pos_left d (by omega)
  have e : s * (d + 3) = s * d + 3 * s := by ring
  have hsd : 3 * s ≤ s * (d + 3) - v := by omega
  have hD : D p (s * (d + 3) - v) ((((p ^ s * μ : ℕ) : ℚ)) ^ (d + 3) / ((d + 3).factorial : ℚ)) := by
    refine ⟨(μ : ℤ) ^ (d + 3), w, hw, ?_⟩
    rw [hfw]
    have hpv : ((p : ℚ) ^ v) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    have hw0 : (w : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hw0'
    have hsplit : (p : ℚ) ^ (s * (d + 3)) = (p : ℚ) ^ (s * (d + 3) - v) * (p : ℚ) ^ v := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    push_cast
    rw [mul_pow, ← pow_mul, hsplit]
    field_simp
  exact (hD.mul0 hl).le hsd

lemma D_coeffEK (h5 : 5 ≤ p) {s M t K : ℕ} (hs : 1 ≤ s) (hM : p ^ s ∣ M) (ht : 1 ≤ t)
    (hK : 2 ≤ K) :
    D p (3 * s) (coeff (p * t) (EK p K (M : ℚ)) - (M : ℚ) ^ 2 / 2 * CT p (p * t)) := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 2 := ⟨K - 2, by omega⟩
  rw [EK, map_sum, show K' + 2 + 1 = K' + 1 + 1 + 1 by ring, Finset.sum_range_succ',
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [coeff_C_mul]
  have hpt0 : p * t ≠ 0 := Nat.mul_ne_zero hp.out.ne_zero (by omega)
  have c0 : coeff (p * t) (Ls p ^ 0) = 0 := by rw [pow_zero, coeff_one, if_neg hpt0]
  have c1 : coeff (p * t) (Ls p ^ (0 + 1)) = 0 := by
    rw [zero_add, pow_one, Ls, coeff_mk, if_pos (dvd_mul_right p t)]
  have c2 : coeff (p * t) (Ls p ^ (0 + 1 + 1)) = CT p (p * t) := coeff_L2 (dvd_mul_right p t)
  rw [c0, c1, c2]
  have hA : D p (3 * s) (∑ i ∈ range K', (M : ℚ) ^ (i + 1 + 1 + 1) /
      (((i + 1 + 1 + 1).factorial : ℕ) : ℚ) * coeff (p * t) (Ls p ^ (i + 1 + 1 + 1))) :=
    D.sum _ _ fun d _ => D_tail h5 hs hM d _ (D_Lpow (d + 3) (p * t))
  have hB : (M : ℚ) ^ (0 + 1 + 1) / (((0 + 1 + 1).factorial : ℕ) : ℚ) = (M : ℚ) ^ 2 / 2 := by
    norm_num [Nat.factorial]
  refine hA.congr ?_
  rw [hB]
  ring

def bcoef (N k : ℕ) : ℕ := ∑ x ∈ antidiagonal k, N.choose x.1 * (N - 1 + x.2).choose (N - 1)

omit hp in
lemma coeff_Fs_pow (n k : ℕ) : coeff k (Fs ^ (n + 1)) = (bcoef (n + 1) k : ℚ) := by
  have hpoly : ((1 + X : PowerSeries ℚ)) ^ (n + 1) =
      ((((1 : Polynomial ℚ) + Polynomial.X) ^ (n + 1) : Polynomial ℚ) : PowerSeries ℚ) := by
    simp
  rw [Fs, Gs, mul_pow, mk_one_pow_eq_mk_choose_add, coeff_mul, bcoef]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hpoly, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
  try simp

lemma pow_dvd_of_mul {q a b' X : ℕ} (h : p ^ q ∣ X * (p ^ a * b')) (hb : ¬ p ∣ b') :
    p ^ (q - a) ∣ X := by
  have hcop : Nat.Coprime (p ^ (q - a)) b' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hb)
  by_cases hqa : a ≤ q
  · have h1 : p ^ a * p ^ (q - a) ∣ p ^ a * (X * b') := by
      rw [← pow_add, Nat.add_sub_cancel' hqa]
      have : p ^ a * (X * b') = X * (p ^ a * b') := by ring
      rw [this]; exact h
    exact hcop.dvd_of_dvd_mul_right (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos a) h1)
  · rw [show q - a = 0 by omega, pow_zero]; exact one_dvd X

lemma bcoef_dvd {N q j k' : ℕ} (hN : 1 ≤ N) (hq : p ^ q ∣ N) (hk : ¬ p ∣ k') :
    p ^ (q - j) ∣ bcoef N (p ^ j * k') := by
  apply Finset.dvd_sum
  intro x hx
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  by_cases h1 : p ^ (j + 1) ∣ x.1
  · apply Dvd.dvd.mul_left
    have h2 : ¬ p ^ (j + 1) ∣ x.2 := by
      intro h2
      have h3 : p ^ (j + 1) ∣ p ^ j * k' := by rw [← hsum]; exact Nat.dvd_add h1 h2
      rw [pow_succ] at h3
      exact hk (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos j) h3)
    have hx2 : x.2 ≠ 0 := by intro h; rw [h] at h2; exact h2 (dvd_zero _)
    obtain ⟨a, b', hb', hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hx2 p hp.out.one_lt.ne'
    have ha : a ≤ j := by
      by_contra hc
      apply h2; rw [hab]; exact Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) b'
    have key : (N - 1 + x.2).choose (N - 1) * x.2 = (N - 1 + x.2).choose (x.2 - 1) * N := by
      obtain ⟨m, hm⟩ : ∃ m, x.2 = m + 1 := ⟨x.2 - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel, Nat.choose_symm_add, Nat.choose_succ_right_eq]
      congr 1; omega
    have hdvd : p ^ q ∣ (N - 1 + x.2).choose (N - 1) * (p ^ a * b') := by
      rw [← hab, key]; exact Dvd.dvd.mul_left hq _
    exact (Nat.pow_dvd_pow p (by omega : q - j ≤ q - a)).trans (pow_dvd_of_mul hdvd hb')
  · apply Dvd.dvd.mul_right
    have hx1 : x.1 ≠ 0 := by intro h; rw [h] at h1; exact h1 (dvd_zero _)
    obtain ⟨a, b', hb', hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hx1 p hp.out.one_lt.ne'
    have ha : a ≤ j := by
      by_contra hc
      apply h1; rw [hab]; exact Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) b'
    have key := Nat.add_one_mul_choose_eq (N - 1) (x.1 - 1)
    rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)] at key
    have hdvd : p ^ q ∣ N.choose x.1 * (p ^ a * b') := by
      rw [← hab, ← key]; exact Dvd.dvd.mul_right hq _
    exact (Nat.pow_dvd_pow p (by omega : q - j ≤ q - a)).trans (pow_dvd_of_mul hdvd hb')

omit hp in
lemma term_id (M k : ℕ) (hk : k ≤ M + 1) :
    (((M + 1).choose k * (M + 1 + k).choose k : ℕ) : ℤ) + ((M.choose k * (M + k).choose k : ℕ) : ℤ)
      = 2 * (((M + 1).choose k * (M + k).choose M : ℕ) : ℤ) := by
  rcases Nat.lt_or_ge k (M + 1) with hlt | hge
  · obtain ⟨j, rfl⟩ : ∃ j, M = k + j := ⟨M - k, by omega⟩
    have e1 : ((k + j + 1).choose k : ℚ) = (k + (j + 1)).factorial / (k.factorial * (j + 1).factorial) := by
      rw [show k + j + 1 = k + (j + 1) by ring]; exact Nat.cast_add_choose ℚ
    have e2 : ((k + j + 1 + k).choose k : ℚ)
        = (k + (k + j + 1)).factorial / (k.factorial * (k + j + 1).factorial) := by
      rw [show k + j + 1 + k = k + (k + j + 1) by ring]; exact Nat.cast_add_choose ℚ
    have e3 : ((k + j).choose k : ℚ) = (k + j).factorial / (k.factorial * j.factorial) :=
      Nat.cast_add_choose ℚ
    have e4 : ((k + j + k).choose k : ℚ) = (k + (k + j)).factorial / (k.factorial * (k + j).factorial) := by
      rw [show k + j + k = k + (k + j) by ring]; exact Nat.cast_add_choose ℚ
    have e5 : ((k + j + k).choose (k + j) : ℚ)
        = (k + j + k).factorial / ((k + j).factorial * k.factorial) := Nat.cast_add_choose ℚ
    have hq : ((((k + j + 1).choose k * (k + j + 1 + k).choose k : ℕ) : ℤ) : ℚ)
        + ((((k + j).choose k * (k + j + k).choose k : ℕ) : ℤ) : ℚ)
        = ((2 * (((k + j + 1).choose k * (k + j + k).choose (k + j) : ℕ) : ℤ) : ℤ) : ℚ) := by
      push_cast
      rw [e1, e2, e3, e4, e5]
      rw [show k + (j + 1) = (k + j) + 1 by ring, show k + (k + j + 1) = (k + (k + j)) + 1 by ring,
        show k + j + k = k + (k + j) by ring]
      simp only [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    exact_mod_cast hq
  · have hkM : k = M + 1 := by omega
    subst hkM
    rw [Nat.choose_eq_zero_of_lt (by omega : M < M + 1), Nat.choose_self]
    have h1 : (M + 1 + (M + 1)).choose (M + 1) = 2 * (M + (M + 1)).choose M := by
      rw [show M + 1 + (M + 1) = (2 * M + 1) + 1 by ring, Nat.choose_succ_succ,
        show M + (M + 1) = 2 * M + 1 by ring, Nat.choose_symm_half]
      ring
    rw [h1]; push_cast; ring

omit hp in
lemma a_eq (M : ℕ) :
    OMA.S_oeis_a241023.a (M + 1) = 2 * ((bcoef (M + 1) (M + 1) : ℕ) : ℤ) := by
  rw [OMA.S_oeis_a241023.a, OMA.S_oeis_a241023.D, OMA.S_oeis_a241023.D, bcoef,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (M + 1).choose i * (M + 1 - 1 + j).choose (M + 1 - 1))]
  have hext : ∑ k ∈ Finset.range (M + 1), ((M.choose k * (M + k).choose k : ℕ) : ℤ)
      = ∑ k ∈ Finset.range (M + 1 + 1), ((M.choose k * (M + k).choose k : ℕ) : ℤ) := by
    rw [Finset.sum_range_succ _ (M + 1), Nat.choose_eq_zero_of_lt (by omega : M < M + 1)]
    simp
  have hr := Finset.sum_range_reflect
    (fun k => (((M + 1).choose k * (M + 1 - 1 + (M + 1 - k)).choose (M + 1 - 1) : ℕ) : ℤ)) (M + 1 + 1)
  rw [hext, ← Finset.sum_add_distrib, Nat.cast_sum, Nat.succ_eq_add_one, ← hr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [term_id M k (by omega)]
  have e : M + 1 + 1 - 1 - k = M + 1 - k := by omega
  rw [e, show M + 1 - (M + 1 - k) = k by omega, Nat.choose_symm (by omega : k ≤ M + 1),
    show M + 1 - 1 = M by omega]

omit hp in
lemma a_coeff (m : ℕ) (hm : 1 ≤ m) :
    ((OMA.S_oeis_a241023.a m : ℤ) : ℚ) = 2 * coeff m (Fs ^ m) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [a_eq, coeff_Fs_pow]
  push_cast; ring

lemma term_D (h5 : 5 ≤ p) {N q k : ℕ} (hN : 1 ≤ N) (hq : p ^ q ∣ N) (hk : k < N) :
    D p (3 * (q + 1)) ((bcoef N k : ℚ) * coeff (p * (N - k)) (EK p (p * N) ((p * N : ℕ) : ℚ))) := by
  have hM : p ^ (q + 1) ∣ p * N := by rw [pow_succ']; exact Nat.mul_dvd_mul_left p hq
  have hK : 2 ≤ p * N := by nlinarith
  have hE := D_coeffEK h5 (by omega) hM (show 1 ≤ N - k by omega) hK
  have hbD : D p 0 (bcoef N k : ℚ) := D.nat _
  -- the C_t part
  have hbC : D p (q + 1) ((bcoef N k : ℚ) * CT p (p * (N - k))) := by
    obtain ⟨d, hd⟩ : ∃ d, N = k + d := ⟨N - k, by omega⟩
    have hNk : N - k = d := by omega
    rw [hNk]
    by_cases hk0 : k = 0
    · subst hk0
      have hdN : d = N := by omega
      rw [hdN]
      exact hbD.mul0' (CT_D' h5 (by omega) hq)
    · obtain ⟨j, k', hk', hkj⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0 p hp.out.one_lt.ne'
      by_cases hjq : q ≤ j
      · have hqk : p ^ q ∣ k := by rw [hkj]; exact Dvd.dvd.mul_right (pow_dvd_pow p hjq) k'
        have hqd : p ^ q ∣ d := by rw [hd] at hq; exact (Nat.dvd_add_right hqk).mp hq
        exact hbD.mul0' (CT_D' h5 (by omega) hqd)
      · have hjk : p ^ j ∣ k := by rw [hkj]; exact Dvd.dvd.mul_right dvd_rfl k'
        have hjN : p ^ j ∣ N := (pow_dvd_pow p (by omega)).trans hq
        have hjd : p ^ j ∣ d := by rw [hd] at hjN; exact (Nat.dvd_add_right hjk).mp hjN
        have hb : D p (q - j) (bcoef N k : ℚ) := by
          rw [hkj]; exact D_of_dvd (bcoef_dvd hN hq hk')
        exact (hb.mul (CT_D' h5 (by omega) hjd)).le (by omega)
  have hMD : D p (q + 1) (((p * N : ℕ) : ℚ)) := D_of_dvd hM
  have h2 : D p (3 * (q + 1)) (((p * N : ℕ) : ℚ) * ((p * N : ℕ) : ℚ) *
      ((bcoef N k : ℚ) * CT p (p * (N - k))) * (1 / 2)) := by
    have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
    have hh : D p 0 ((1 : ℚ) / 2) := by
      rw [one_div]; exact_mod_cast (D.inv hp2 : D p 0 (((2 : ℕ) : ℚ))⁻¹)
    exact (((hMD.mul hMD).mul hbC).mul0 hh).le (by omega)
  exact ((hbD.mul0' hE).add h2).congr (by ring)

theorem main_congr (h5 : 5 ≤ p) (n q : ℕ) (hn : 1 ≤ n) :
    ((p : ℤ) ^ (3 * (q + 1))) ∣
      OMA.S_oeis_a241023.a (n * p ^ (q + 1)) - OMA.S_oeis_a241023.a (n * p ^ q) := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two (by omega))
  obtain ⟨n', hn'⟩ : ∃ n', n * p ^ q = n' + 1 :=
    ⟨n * p ^ q - 1, by have : 0 < n * p ^ q := Nat.mul_pos hn (pow_pos hp.out.pos q); omega⟩
  have hpN : n * p ^ (q + 1) = p * (n' + 1) := by rw [← hn']; ring
  have hq : p ^ q ∣ n' + 1 := by rw [← hn']; exact dvd_mul_left _ _
  rw [hpN, hn']
  apply D.dvd
  push_cast
  rw [a_coeff (p * (n' + 1)) (Nat.mul_pos hp.out.pos (Nat.succ_pos n')),
    a_coeff (n' + 1) (by omega), key_identity hp0 hp2 n', ← map_pow,
    sum_expand, Finset.sum_range_succ, Nat.sub_self, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_EK, mul_one, ← mul_sub, add_sub_cancel_right]
  refine D.mul0' (Dq 2 (2 : ℚ) (by norm_num)) ?_
  apply D.sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have he : p * (n' + 1) - p * k = p * (n' + 1 - k) := by
    obtain ⟨d, hd⟩ : ∃ d, n' + 1 = k + d := ⟨n' + 1 - k, by omega⟩
    rw [hd, Nat.mul_add, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  rw [he, coeff_Fs_pow]
  exact term_D h5 (by omega) hq hk'

end A241023

theorem OMA.solution : type_of% @OMA.S_oeis_a241023.main := by
  intro p n r hp hp5 hn hr
  have := Fact.mk hp
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  push_cast
  exact A241023.main_congr (p := p) hp5 n q hn
