import OMAStatements.S_oeis_a300386
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


namespace A300386
open Finset PowerSeries

noncomputable def cQ (k : ℕ) : ℚ := ((Nat.choose (7 * k) (2 * k) : ℕ) : ℚ) / 7
noncomputable def Phi : PowerSeries ℚ := mk fun n => cQ (n + 1)
noncomputable def As : PowerSeries ℚ := mk OMA.S_oeis_a300386.a

lemma a_succ (n : ℕ) : OMA.S_oeis_a300386.a (n + 1) * ((n : ℚ) + 1) =
    ∑ k ∈ range (n + 1), cQ (n - k + 1) * OMA.S_oeis_a300386.a k := by
  rw [OMA.S_oeis_a300386.a.eq_2]
  rw [Fin.sum_univ_eq_sum_range (fun k => (1 / 7 : ℚ) *
    ((Nat.choose (7 * (n + 1 - k)) (2 * (n + 1 - k)) : ℕ) : ℚ) *
      OMA.S_oeis_a300386.a k)]
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [show ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) by push_cast; ring]
  rw [one_div, mul_comm, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  rw [cQ, show n + 1 - k = n - k + 1 by omega]
  ring

lemma deriv_As : derivative ℚ As = Phi * As := by
  ext n
  rw [mul_comm Phi As, coeff_derivative, As, coeff_mk, a_succ, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun k hk => ?_
  simp only [Phi, coeff_mk]
  ring

/-- Lucas: carry lemma -/
lemma choose_dvd_of_mod {p n k : ℕ} [Fact p.Prime] (h : n % p < k % p) : p ∣ Nat.choose n k := by
  have := (Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := n) (k := k))
  rw [Nat.choose_eq_zero_of_lt h, zero_mul] at this
  exact Nat.modEq_zero_iff_dvd.mp this

lemma carry {p i : ℕ} [hp : Fact p.Prime] (h5 : 11 ≤ p) (hi0 : 0 < i) (hip : i < p) :
    p ∣ Nat.choose (7 * i) (2 * i) * Nat.choose (7 * (p - i)) (2 * (p - i)) := by
  have hp0 : 0 < p := by omega
  set u := 2 * i / p with hu
  set r := 2 * i % p with hr
  set v := 5 * i / p with hv
  set s := 5 * i % p with hs
  have e1 : 2 * i = p * u + r := (Nat.div_add_mod _ _).symm
  have e2 : 5 * i = p * v + s := (Nat.div_add_mod _ _).symm
  have hrp : r < p := Nat.mod_lt _ hp0
  have hsp : s < p := Nat.mod_lt _ hp0
  have hu1 : u ≤ 1 := by
    rw [hu]; apply Nat.lt_succ_iff.mp; apply (Nat.div_lt_iff_lt_mul hp0).mpr; omega
  have hv8 : v ≤ 4 := by
    rw [hv]; apply Nat.lt_succ_iff.mp; apply (Nat.div_lt_iff_lt_mul hp0).mpr; omega
  have hr0 : r ≠ 0 := by
    intro h0
    have : p ∣ 2 * i := Nat.dvd_of_mod_eq_zero (by rw [← hr]; exact h0)
    rcases (Nat.Prime.dvd_mul hp.out).mp this with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd hi0 h; omega
  have hs0 : s ≠ 0 := by
    intro h0
    have : p ∣ 5 * i := Nat.dvd_of_mod_eq_zero (by rw [← hs]; exact h0)
    rcases (Nat.Prime.dvd_mul hp.out).mp this with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd hi0 h; omega
  by_cases hc : p ≤ r + s
  · apply Dvd.dvd.mul_right
    apply choose_dvd_of_mod
    have h11 : 7 * i = p * (u + v + 1) + (r + s - p) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega
    rw [h11, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega), ← hr]
    omega
  · apply Dvd.dvd.mul_left
    apply choose_dvd_of_mod
    have h2 : 2 * (p - i) = p * (1 - u) + (p - r) := by
      interval_cases u <;> omega
    have h11 : 7 * (p - i) = p * (6 - u - v) + (p - r - s) := by
      interval_cases u <;> interval_cases v <;> omega
    rw [h11, h2, Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- (1+X)^q = 1 + X^q mod q, lifted. -/
lemma poly_congr {q : ℕ} (hq : q.Prime) (k N j : ℕ) :
    (q : ℤ) ^ (k + 1) ∣ (Nat.choose (q ^ (k + 1) * N) (q * j) : ℤ) -
      (Nat.choose (q ^ k * N) j : ℤ) := by
  have h1 : ((q : Polynomial ℤ)) ∣ (1 + Polynomial.X) ^ q - (1 + Polynomial.X ^ q) := by
    rw [show ((q : Polynomial ℤ)) = Polynomial.C (q : ℤ) from (map_natCast _ q).symm,
      Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow, Polynomial.coeff_add,
      Polynomial.coeff_one, Polynomial.coeff_X_pow]
    rcases Nat.lt_trichotomy i q with h | h | h
    · rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0; have hq0 : (0:ℕ) ≠ q := by omega
        simp [hq0]
      · rw [if_neg (by omega), if_neg (by omega)]
        simp only [add_zero, sub_zero]
        exact_mod_cast hq.dvd_choose_self (by omega) h
    · subst h; simp [hq.ne_zero]
    · rw [Nat.choose_eq_zero_of_lt h, if_neg (by omega), if_neg (by omega)]; simp
  have h2 := dvd_sub_pow_of_dvd_sub h1 k
  have h3 : ((1 + Polynomial.X : Polynomial ℤ) ^ q) ^ q ^ k - (1 + Polynomial.X ^ q) ^ q ^ k ∣
      (((1 + Polynomial.X) ^ q) ^ q ^ k) ^ N - ((1 + Polynomial.X ^ q) ^ q ^ k) ^ N :=
    sub_dvd_pow_sub_pow _ _ N
  have h4 := dvd_trans h2 h3
  rw [show ((q : Polynomial ℤ)) ^ (k + 1) = Polynomial.C ((q : ℤ) ^ (k + 1)) by simp,
    Polynomial.C_dvd_iff_dvd_coeff] at h4
  have h5 := h4 (q * j)
  rw [← pow_mul, ← pow_mul, ← pow_mul, Polynomial.coeff_sub,
    Polynomial.coeff_one_add_X_pow] at h5
  have h6 : (1 + (Polynomial.X : Polynomial ℤ) ^ q) ^ (q ^ k * N)
      = Polynomial.expand ℤ q ((1 + Polynomial.X) ^ (q ^ k * N)) := by simp
  rw [h6, Polynomial.coeff_expand_mul' hq.pos, Polynomial.coeff_one_add_X_pow,
    show q * (q ^ k * N) = q ^ (k + 1) * N by ring] at h5
  exact h5

end A300386

namespace A300386
open Finset PowerSeries LtsJacobsthal

/-! ### generic power-series tools -/

noncomputable def EKg (L : PowerSeries ℚ) (K : ℕ) (M : ℚ) : PowerSeries ℚ :=
  ∑ d ∈ range (K + 1), C (M ^ d / (d.factorial : ℚ)) * L ^ d

lemma deriv_EKg (L : PowerSeries ℚ) (K : ℕ) (M : ℚ) :
    derivative ℚ (EKg L K M) = C M * derivative ℚ L *
      (EKg L K M - C (M ^ K / (K.factorial : ℚ)) * L ^ K) := by
  have hd : ∀ (r : ℚ) (f : PowerSeries ℚ), derivative ℚ (C r * f) = C r * derivative ℚ f := by
    intro r f
    rw [Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul]
  have hterm : ∀ d : ℕ, derivative ℚ (C (M ^ (d + 1) / ((d + 1).factorial : ℚ)) * L ^ (d + 1))
      = C M * derivative ℚ L * (C (M ^ d / (d.factorial : ℚ)) * L ^ d) := by
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
    calc C (M ^ (d + 1) / ((d + 1).factorial : ℚ)) * (C ((d + 1 : ℕ) : ℚ) * L ^ d
          * derivative ℚ L)
        = C (M ^ (d + 1) / ((d + 1).factorial : ℚ) * ((d + 1 : ℕ) : ℚ)) * L ^ d
          * derivative ℚ L := by rw [map_mul]; ring
      _ = _ := by rw [h2, map_mul]; ring
  unfold EKg
  conv_rhs => rw [Finset.sum_range_succ, add_sub_cancel_right]
  rw [map_sum, Finset.sum_range_succ', Finset.mul_sum]
  have h0 : derivative ℚ (C (M ^ 0 / ((Nat.factorial 0 : ℕ) : ℚ)) * L ^ 0) = 0 := by
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

lemma constantCoeff_EKg (L : PowerSeries ℚ) (hL : constantCoeff L = 0) (K : ℕ) (M : ℚ) :
    constantCoeff (EKg L K M) = 1 := by
  rw [EKg, map_sum, Finset.sum_range_succ']
  simp [hL]

lemma coeff_lowg (L : PowerSeries ℚ) (hL : constantCoeff L = 0) (K k : ℕ) (hk : k < K)
    (A : PowerSeries ℚ) : coeff k (A * L ^ K) = 0 := by
  obtain ⟨B, hB⟩ := X_dvd_iff.mpr hL
  rw [hB, mul_pow, mul_left_comm, coeff_X_pow_mul', if_neg (by omega)]

lemma deriv_expand (q : ℕ) (hq0 : q ≠ 0) (f : PowerSeries ℚ) :
    derivative ℚ (expand q hq0 f) = C (q : ℚ) * X ^ (q - 1) * expand q hq0 (derivative ℚ f) := by
  ext n
  rw [coeff_derivative, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  by_cases h : q ∣ n + 1
  · obtain ⟨m, hm⟩ := h
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by rcases m with _ | m <;> simp at hm ⊢⟩
    have hle : q - 1 ≤ n := by
      have : q ≤ n + 1 := by rw [hm, Nat.mul_add, Nat.mul_one]; exact Nat.le_add_left q (q * j)
      omega
    have hsub : n - (q - 1) = q * j := by
      have : n + 1 = q * j + q := by rw [hm]; ring
      generalize q * j = P at this
      omega
    have hc : ((n : ℚ) + 1) = (q : ℚ) * ((j : ℚ) + 1) := by exact_mod_cast hm
    rw [if_pos hle, hsub, coeff_expand_mul, coeff_derivative, hm, coeff_expand_mul, hc]
    ring
  · rw [coeff_expand_of_not_dvd _ _ _ h, zero_mul]
    split_ifs with hle
    · rw [coeff_expand_of_not_dvd, mul_zero]
      intro hd
      apply h
      have : n + 1 = (n - (q - 1)) + q := by omega
      rw [this]
      exact Nat.dvd_add hd (dvd_refl q)
    · rw [mul_zero]

lemma coeff_agree_pow {F G : PowerSeries ℚ} {n : ℕ} (h : ∀ k ≤ n, coeff k F = coeff k G) (m : ℕ) :
    ∀ k ≤ n, coeff k (F ^ m) = coeff k (G ^ m) := by
  induction m with
  | zero => intro k _; rfl
  | succ m ih =>
    intro k hk
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    refine sum_congr rfl fun x hx => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rw [ih x.1 (by omega), h x.2 (by omega)]

lemma coeff_agree_mul {F G : PowerSeries ℚ} {n : ℕ} (h : ∀ k ≤ n, coeff k F = coeff k G)
    (H : PowerSeries ℚ) : coeff n (F * H) = coeff n (G * H) := by
  rw [coeff_mul, coeff_mul]
  refine sum_congr rfl fun x hx => ?_
  have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [h x.1 (by omega)]

lemma binom2 {R : Type*} [CommRing R] (b z : R) (m : ℕ) :
    ∃ W : R, (b + z) ^ (m + 1) = b ^ (m + 1) + ((m + 1 : ℕ) : R) * b ^ m * z + z ^ 2 * W := by
  induction m with
  | zero => exact ⟨0, by push_cast; ring⟩
  | succ m ih =>
    obtain ⟨W, hW⟩ := ih
    refine ⟨((m + 1 : ℕ) : R) * b ^ m + (b + z) * W, ?_⟩
    rw [pow_succ, hW]
    push_cast
    ring

/-! ### p-integral series -/

def I (q e : ℕ) (F : PowerSeries ℚ) : Prop := ∀ n, D q e (coeff n F)

variable {q : ℕ} [hq : Fact q.Prime]

lemma I.add {e : ℕ} {F G : PowerSeries ℚ} (hF : I q e F) (hG : I q e G) : I q e (F + G) :=
  fun n => by rw [map_add]; exact (hF n).add (hG n)

lemma I.sub {e : ℕ} {F G : PowerSeries ℚ} (hF : I q e F) (hG : I q e G) : I q e (F - G) :=
  fun n => by rw [map_sub]; exact (hF n).sub (hG n)

lemma I.mul {e f : ℕ} {F G : PowerSeries ℚ} (hF : I q e F) (hG : I q f G) : I q (e + f) (F * G) :=
  fun n => by
    rw [coeff_mul]
    exact D.sum _ _ fun x _ => (hF x.1).mul (hG x.2)

lemma I.one : I q 0 (1 : PowerSeries ℚ) := fun n => by
  rw [coeff_one]; split_ifs
  · exact D.one
  · exact D.zero 0

lemma I.zero (e : ℕ) : I q e (0 : PowerSeries ℚ) := fun n => by rw [map_zero]; exact D.zero e

lemma I.pow0 {F : PowerSeries ℚ} (hF : I q 0 F) (m : ℕ) : I q 0 (F ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact I.one
  | succ m ih => rw [pow_succ]; exact ih.mul hF

lemma I.C_mul {e f : ℕ} {r : ℚ} {F : PowerSeries ℚ} (hr : D q e r) (hF : I q f F) :
    I q (e + f) (C r * F) := fun n => by rw [coeff_C_mul]; exact hr.mul (hF n)

lemma I.le {e f : ℕ} {F : PowerSeries ℚ} (hF : I q e F) (h : f ≤ e) : I q f F :=
  fun n => (hF n).le h

lemma I.sum {ι : Type*} {e : ℕ} (s : Finset ι) (f : ι → PowerSeries ℚ) (h : ∀ i ∈ s, I q e (f i)) :
    I q e (∑ i ∈ s, f i) := fun n => by
  rw [map_sum]; exact D.sum _ _ fun i hi => h i hi n

lemma I.expand {e : ℕ} {F : PowerSeries ℚ} (hF : I q e F) : I q e (expand q hq.out.ne_zero F) :=
  fun n => by
    rw [coeff_expand]; split_ifs
    · exact hF _
    · exact D.zero e

lemma I.monomial {e : ℕ} {r : ℚ} (hr : D q e r) (k : ℕ) : I q e (monomial k r) := fun n => by
  rw [coeff_monomial]; split_ifs
  · exact hr
  · exact D.zero e

lemma D_natq (c : ℕ) (hc : q ∣ c) : D q 1 (c : ℚ) := by
  obtain ⟨t, rfl⟩ := hc
  exact ⟨t, 1, hq.out.not_dvd_one, by push_cast; ring⟩

lemma I.natq {e : ℕ} {c : ℕ} (hc : q ∣ c) {F : PowerSeries ℚ} (hF : I q e F) :
    I q (1 + e) ((c : PowerSeries ℚ) * F) := by
  rw [show ((c : PowerSeries ℚ)) = C (c : ℚ) from (map_natCast C c).symm]
  exact I.C_mul (D_natq c hc) hF

/-- Fermat in Z_(q) -/
lemma D_fermat {a : ℚ} (ha : D q 0 a) : D q 1 (a ^ q - a) := by
  obtain ⟨z, b, hb, h⟩ := ha
  have hbz : ((b : ℤ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hb
  have hdiv : (q : ℤ) ∣ z ^ q - z * (b : ℤ) ^ (q - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card, ZMod.pow_card_sub_one_eq_one (by exact_mod_cast hbz)]
    ring
  obtain ⟨t, ht⟩ := hdiv
  refine ⟨t, b ^ q, fun hd => hb (hq.out.dvd_of_dvd_pow hd), ?_⟩
  have hq1 : q = (q - 1) + 1 := by have := hq.out.two_le; omega
  have hb0 : (b : ℚ) ≠ 0 := by
    intro h0; apply hb; have : b = 0 := by exact_mod_cast h0
    rw [this]; exact dvd_zero q
  have h1 : a * (b : ℚ) = (z : ℚ) := by simpa using h
  have hz : a ^ q * (b : ℚ) ^ q = (z : ℚ) ^ q := by rw [← mul_pow, h1]
  have hbq : (b : ℚ) ^ q = (b : ℚ) * (b : ℚ) ^ (q - 1) := by
    rw [← pow_succ']; congr 1
  have ht' : (z : ℚ) ^ q - (z : ℚ) * (b : ℚ) ^ (q - 1) = (q : ℚ) * (t : ℚ) := by
    exact_mod_cast ht
  push_cast
  linear_combination hz - a * hbq - (b : ℚ) ^ (q - 1) * h1 + ht'

lemma frob_add {F G : PowerSeries ℚ} (hF : I q 0 F) (hG : I q 0 G) :
    I q 1 ((F + G) ^ q - F ^ q - G ^ q) := by
  rw [add_pow]
  obtain ⟨r, hr⟩ : ∃ r, q = r + 1 + 1 := ⟨q - 2, by have := hq.out.two_le; omega⟩
  have key : (∑ m ∈ range (q + 1), F ^ m * G ^ (q - m) * ((q.choose m : ℕ) : PowerSeries ℚ))
      - F ^ q - G ^ q
      = ∑ m ∈ Finset.Ioo 0 q, ((q.choose m : ℕ) : PowerSeries ℚ) * (F ^ m * G ^ (q - m)) := by
    rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [Nat.choose_self, Nat.choose_zero_right, Nat.sub_self, Nat.sub_zero, pow_zero,
      Nat.cast_one, mul_one, one_mul]
    rw [show Finset.Ico (0 + 1) q = Finset.Ioo 0 q by rfl]
    rw [show ∀ x y z w : PowerSeries ℚ, x + y + z - z - w = y + (x - w) by intros; ring,
      show ∀ x y : PowerSeries ℚ, x + (y - y) = x by intros; ring]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [key]
  refine I.sum _ _ fun m hm => ?_
  have hm' := Finset.mem_Ioo.mp hm
  have := I.natq (hq.out.dvd_choose_self (by omega) hm'.2) ((hF.pow0 m).mul (hG.pow0 (q - m)))
  simpa using this

lemma frob_monomial {a : ℚ} (ha : D q 0 a) (k : ℕ) :
    I q 1 ((monomial k a) ^ q - expand q hq.out.ne_zero (monomial k a)) := by
  rw [monomial_pow, expand_monomial, ← map_sub]
  exact I.monomial (D_fermat ha) _

lemma frob_trunc (A : PowerSeries ℚ) (n : ℕ) (h : ∀ k < n, D q 0 (coeff k A)) :
    I q 1 (((trunc n A : Polynomial ℚ) : PowerSeries ℚ) ^ q
      - expand q hq.out.ne_zero ((trunc n A : Polynomial ℚ) : PowerSeries ℚ)) := by
  induction n with
  | zero =>
    simp only [trunc_zero', Polynomial.coe_zero, map_zero]
    rw [zero_pow hq.out.ne_zero, sub_zero]; exact I.zero 1
  | succ n ih =>
    have ih' := ih fun k hk => h k (by omega)
    have hF : I q 0 ((trunc n A : Polynomial ℚ) : PowerSeries ℚ) := fun k => by
      rw [Polynomial.coeff_coe, coeff_trunc]; split_ifs with hk
      · exact h k (by omega)
      · exact D.zero 0
    have hZ : I q 0 (monomial n (coeff n A)) := I.monomial (h n (by omega)) n
    rw [trunc_succ, Polynomial.coe_add, Polynomial.coe_monomial]
    have := ((frob_add hF hZ).add ih').add (frob_monomial (h n (by omega)) n)
    convert this using 1
    rw [map_add]; ring

end A300386

namespace A300386
open Finset PowerSeries LtsJacobsthal

lemma seven_dvd (m : ℕ) (hm : 1 ≤ m) : 7 ∣ Nat.choose (7 * m) (2 * m) := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have h : (7 * t + 6 + 1) * Nat.choose (7 * t + 6) (2 * t + 1)
      = Nat.choose (7 * t + 6 + 1) (2 * t + 1 + 1) * (2 * t + 1 + 1) := Nat.add_one_mul_choose_eq _ _
  rw [show 7 * t + 6 + 1 = 7 * (t + 1) by ring, show 2 * t + 1 + 1 = 2 * (t + 1) by ring] at h
  have h2 : 7 * Nat.choose (7 * t + 6) (2 * t + 1) = 2 * Nat.choose (7 * (t + 1)) (2 * (t + 1)) := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < t + 1 by omega)
    calc (t + 1) * (7 * Nat.choose (7 * t + 6) (2 * t + 1))
        = 7 * (t + 1) * Nat.choose (7 * t + 6) (2 * t + 1) := by ring
      _ = Nat.choose (7 * (t + 1)) (2 * (t + 1)) * (2 * (t + 1)) := h
      _ = (t + 1) * (2 * Nat.choose (7 * (t + 1)) (2 * (t + 1))) := by ring
  have : 7 ∣ 2 * Nat.choose (7 * (t + 1)) (2 * (t + 1)) := ⟨_, h2.symm⟩
  exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this

lemma coeff_monomial_mul' (m n : ℕ) (a : ℚ) (F : PowerSeries ℚ) :
    coeff n (monomial m a * F) = if m ≤ n then a * coeff (n - m) F else 0 := by
  rw [show monomial m a = C a * X ^ m by
    rw [X_pow_eq, ← monomial_zero_eq_C_apply, monomial_mul_monomial]; simp,
    mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp

variable {q : ℕ} [hq : Fact q.Prime]

lemma D_cQ (m : ℕ) (hm : 1 ≤ m) : D q 0 (cQ m) := by
  obtain ⟨c, hc⟩ := seven_dvd m hm
  unfold cQ
  rw [hc]
  exact ⟨c, 1, hq.out.not_dvd_one, by push_cast; ring⟩

lemma D_of_dvdZ {e : ℕ} {z : ℤ} (h : (q : ℤ) ^ e ∣ z) : D q e (z : ℚ) := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c, 1, hq.out.not_dvd_one, by push_cast; ring⟩

lemma D_div {k w : ℕ} {x : ℚ} (hx : D q k x) (hw : ¬ q ∣ w) (N : ℕ) (hN : N = q ^ k * w) :
    D q 0 (x / (N : ℚ)) := by
  obtain ⟨z, b, hb, h⟩ := hx
  subst hN
  refine ⟨z, b * w, ?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hq.out).mp hd with h1 | h1
    · exact hb h1
    · exact hw h1
  · have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.out.ne_zero
    have hw0 : (w : ℚ) ≠ 0 := by
      intro h0; apply hw; have : w = 0 := by exact_mod_cast h0
      rw [this]; exact dvd_zero q
    push_cast
    field_simp
    linear_combination h

noncomputable def Ys (q : ℕ) : PowerSeries ℚ :=
  mk fun n => if n = 0 then 0 else ((if q ∣ n then cQ (n / q) else 0) - cQ n) / (n : ℚ)

lemma D_Y (n : ℕ) : D q 0 (coeff n (Ys q)) := by
  rw [Ys, coeff_mk]
  split_ifs with h0 hd
  · exact D.zero 0
  · obtain ⟨m, rfl⟩ := hd
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at h0
      · exact h
    obtain ⟨v, w, hw, hvw⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (show q * m ≠ 0 by omega) q hq.out.one_lt.ne'
    have hv : 1 ≤ v := by
      rcases Nat.eq_zero_or_pos v with h | h
      · subst h; exfalso; apply hw; rw [pow_zero, one_mul] at hvw; rw [← hvw]
        exact dvd_mul_right q m
      · exact h
    obtain ⟨k, rfl⟩ : ∃ k, v = k + 1 := ⟨v - 1, by omega⟩
    have hmw : m = q ^ k * w := by
      apply Nat.eq_of_mul_eq_mul_left hq.out.pos
      rw [hvw]; ring
    rw [Nat.mul_div_cancel_left m hq.out.pos]
    have hdiff : D q (k + 1) (cQ (q * m) - cQ m) := by
      by_cases h11 : q = 7
      · subst h11
        have := poly_congr hq.out (k + 1) w (2 * m)
        rw [show 7 ^ (k + 1 + 1) * w = 7 * (7 * m) by rw [hmw]; ring,
          show 7 ^ (k + 1) * w = 7 * m by rw [hmw]; ring,
          show 7 * (2 * m) = 2 * (7 * m) by ring] at this
        apply D.cancel (c := 1)
        refine (D_of_dvdZ this).congr ?_
        unfold cQ; push_cast; ring
      · have := poly_congr hq.out k (7 * w) (2 * m)
        rw [show q ^ (k + 1) * (7 * w) = 7 * (q * m) by rw [hmw]; ring,
          show q ^ k * (7 * w) = 7 * m by rw [hmw]; ring,
          show q * (2 * m) = 2 * (q * m) by ring] at this
        have h11' : ¬ q ∣ 7 := by
          intro hd
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd with h | h
          · exact hq.out.one_lt.ne' h
          · exact h11 h
        apply D.ucancel h11'
        refine (D_of_dvdZ this).congr ?_
        unfold cQ; push_cast; ring
    exact D_div (hdiff.neg.congr (by ring)) hw (q * m) hvw
  · rw [zero_sub, div_eq_mul_inv]
    exact (D_cQ n (by omega)).neg.mul0 (D.inv hd)

lemma constantCoeff_Ys : constantCoeff (Ys q) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Ys, coeff_mk]; simp

lemma D_qpow_fact (d : ℕ) (hd : 1 ≤ d) : D q 1 ((q : ℚ) ^ d / (d.factorial : ℚ)) := by
  obtain ⟨v, w, hw, hfw⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero d) q hq.out.one_lt.ne'
  have hw0' : w ≠ 0 := by rintro rfl; exact hw (dvd_zero q)
  have hv : padicValNat q d.factorial = v := by
    rw [hfw, padicValNat.mul (pow_ne_zero _ hq.out.ne_zero) hw0',
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hw, add_zero]
  have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero q (show d ≠ 0 by omega)
  rw [hv] at hlt
  have hq1 : 1 ≤ q - 1 := by have := hq.out.two_le; omega
  have hvd : v < d := lt_of_le_of_lt (Nat.le_mul_of_pos_left v hq1) hlt
  have hD : D q (d - v) ((q : ℚ) ^ d / (d.factorial : ℚ)) := by
    refine ⟨1, w, hw, ?_⟩
    rw [hfw]
    have hqv : ((q : ℚ) ^ v) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hq.out.ne_zero)
    have hw0 : (w : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hw0'
    have hsplit : (q : ℚ) ^ d = (q : ℚ) ^ (d - v) * (q : ℚ) ^ v := by
      rw [← pow_add, Nat.sub_add_cancel hvd.le]
    push_cast
    rw [hsplit]
    field_simp
  exact hD.le (by omega)

lemma E_sub_one {Y : PowerSeries ℚ} (hY : I q 0 Y) (K : ℕ) : I q 1 (EKg Y K q - 1) := by
  rw [EKg, Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, map_one, one_mul,
    add_sub_cancel_right]
  refine I.sum _ _ fun d _ => ?_
  have := I.C_mul (D_qpow_fact (q := q) (d + 1) (by omega)) (hY.pow0 (d + 1))
  simpa using this

lemma deriv_Y : derivative ℚ (Ys q) = X ^ (q - 1) * expand q hq.out.ne_zero Phi - Phi := by
  ext n
  rw [coeff_derivative, map_sub, coeff_X_pow_mul', Ys, coeff_mk, if_neg (Nat.succ_ne_zero n)]
  have hne : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [show ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) by push_cast; ring, div_mul_cancel₀ _ hne]
  simp only [Phi, coeff_mk]
  by_cases h : q ∣ n + 1
  · obtain ⟨m, hm⟩ := h
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by rcases m with _ | m <;> simp at hm ⊢⟩
    have hle : q - 1 ≤ n := by
      have : q ≤ n + 1 := by rw [hm, Nat.mul_add, Nat.mul_one]; exact Nat.le_add_left q (q * j)
      omega
    have hsub : n - (q - 1) = q * j := by
      have he : n + 1 = q * j + q := by rw [hm]; ring
      have h2 := hq.out.two_le
      generalize q * j = P at he ⊢
      omega
    rw [if_pos ⟨j + 1, hm⟩, if_pos hle, hsub, coeff_expand_mul, coeff_mk, hm,
      Nat.mul_div_cancel_left _ hq.out.pos]
  · rw [if_neg h]
    split_ifs with hle
    · rw [coeff_expand_of_not_dvd]
      · intro hd
        apply h
        have := hq.out.two_le
        have : n + 1 = (n - (q - 1)) + q := by omega
        rw [this]
        exact Nat.dvd_add hd (dvd_refl q)
    · ring

lemma constantCoeff_As : constantCoeff As = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, As, coeff_mk, OMA.S_oeis_a300386.a.eq_1]

lemma key1 (n : ℕ) :
    coeff n (expand q hq.out.ne_zero As) = coeff n (As ^ q * EKg (Ys q) n (q : ℚ)) := by
  have hq0 := hq.out.ne_zero
  obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  set E := EKg (Ys q) n (q : ℚ) with hE
  set R := C ((q : ℚ) ^ n / (n.factorial : ℚ)) with hR
  have hdE : derivative ℚ E = C (q : ℚ) * derivative ℚ (Ys q) * (E - R * Ys q ^ n) :=
    deriv_EKg (Ys q) n q
  have hzero := uniq n (expand q hq0 As - As ^ q * E) (C (q : ℚ) * X ^ (q - 1) * expand q hq0 Phi)
    (by
      rw [map_sub, map_mul, map_pow, hE, constantCoeff_EKg _ constantCoeff_Ys,
        constantCoeff_expand, constantCoeff_As]
      simp)
    (by
      intro j hj
      have hid : derivative ℚ (expand q hq0 As - As ^ q * E)
          - C (q : ℚ) * X ^ (q - 1) * expand q hq0 Phi * (expand q hq0 As - As ^ q * E)
          = (As ^ q * C (q : ℚ) * derivative ℚ (Ys q) * R) * Ys q ^ n := by
        rw [map_sub, Derivation.leibniz, derivative_pow, hdE, deriv_expand, deriv_As,
          map_mul (expand q hq0) Phi As]
        simp only [smul_eq_mul]
        rw [deriv_Y]
        have hc : ((q : ℕ) : PowerSeries ℚ) = C (q : ℚ) := (map_natCast C q).symm
        rw [hc]
        have hpow : As ^ q = As ^ (q - 1) * As := by
          rw [← pow_succ]; congr 1; omega
        rw [hpow]
        ring
      rw [hid]
      exact coeff_lowg _ constantCoeff_Ys _ _ hj _)
    n le_rfl
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

lemma a_int : ∀ n, D q 0 (coeff n As) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; rw [As, coeff_mk, OMA.S_oeis_a300386.a.eq_1]; exact D.one
  · have hq0 := hq.out.ne_zero
    set B : PowerSeries ℚ := ((trunc n As : Polynomial ℚ) : PowerSeries ℚ) with hB
    set an := coeff n As with han
    set Z : PowerSeries ℚ := monomial n an with hZ
    set E := EKg (Ys q) n (q : ℚ) with hE
    have hB0 : I q 0 B := fun k => by
      rw [hB, Polynomial.coeff_coe, coeff_trunc]; split_ifs with hk
      · exact ih k hk
      · exact D.zero 0
    have hBZ : ∀ k ≤ n, coeff k As = coeff k (B + Z) := by
      intro k hk
      rw [map_add, hB, Polynomial.coeff_coe, coeff_trunc, hZ, coeff_monomial]
      rcases lt_or_eq_of_le hk with h | h
      · rw [if_pos h, if_neg (by omega), add_zero]
      · subst h; rw [if_neg (lt_irrefl _), if_pos rfl, zero_add]
    have hkey := key1 (q := q) n
    have h1 : coeff n (expand q hq0 As) = coeff n (expand q hq0 B) := by
      rw [coeff_expand, coeff_expand]
      split_ifs with hd
      · rw [hB, Polynomial.coeff_coe, coeff_trunc, if_pos (Nat.div_lt_self hn hq.out.one_lt)]
      · rfl
    have h2 : coeff n (As ^ q * E) = coeff n ((B + Z) ^ q * E) :=
      coeff_agree_mul (coeff_agree_pow hBZ q) E
    obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    obtain ⟨W, hW⟩ := binom2 B Z r
    have hB1 : constantCoeff B = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply, hB, Polynomial.coeff_coe, coeff_trunc, if_pos hn,
        coeff_zero_eq_constantCoeff_apply, constantCoeff_As]
    have hE1 : constantCoeff E = 1 := constantCoeff_EKg _ constantCoeff_Ys _ _
    have h3 : coeff n ((B + Z) ^ q * E) = coeff n (B ^ q * E) + (q : ℚ) * an := by
      rw [hr, hW, add_mul, add_mul, map_add, map_add]
      have hz2 : coeff n (Z ^ 2 * W * E) = 0 := by
        rw [hZ, monomial_pow, mul_assoc, coeff_monomial_mul', if_neg (by omega)]
      have hz1 : coeff n (((r + 1 : ℕ) : PowerSeries ℚ) * B ^ r * Z * E) = ((r + 1 : ℕ) : ℚ) * an := by
        rw [show ((r + 1 : ℕ) : PowerSeries ℚ) * B ^ r * Z * E
            = Z * (((r + 1 : ℕ) : PowerSeries ℚ) * B ^ r * E) by ring,
          hZ, coeff_monomial_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply,
          map_mul, map_mul, map_pow, hB1, hE1, map_natCast]
        ring
      rw [hz2, hz1, add_zero]
    have hfr := frob_trunc (q := q) As n ih
    have hBE : I q 1 (B ^ q * (E - 1)) := by
      have := (hB0.pow0 q).mul (E_sub_one (q := q) (fun k => D_Y k) n)
      simpa using this
    have hsum : (q : ℚ) * an = -(coeff n (B ^ q - expand q hq0 B)) - coeff n (B ^ q * (E - 1)) := by
      have e1 : coeff n (B ^ q * E) = coeff n (B ^ q) + coeff n (B ^ q * (E - 1)) := by
        rw [← map_add]; congr 1; ring
      rw [map_sub, ← h1, hkey, h2, h3, e1]
      ring
    apply D.cancel (c := 1)
    rw [pow_one, hsum]
    exact ((hfr n).neg.sub (hBE n))

lemma rat_int (x : ℚ) (h : ∀ q : ℕ, q.Prime → D q 0 x) : ∃ z : ℤ, (z : ℚ) = x := by
  have hden : x.den = 1 := by
    by_contra hne
    obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd hne
    obtain ⟨z, b, hb, hz⟩ := h p hpp
    have hx : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
    have hd0 : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
    rw [hx] at hz
    have hz' : (x.num : ℚ) * (b : ℚ) = (z : ℚ) * (x.den : ℚ) := by
      field_simp at hz; linear_combination hz
    have hZ : x.num * (b : ℤ) = z * (x.den : ℤ) := by exact_mod_cast hz'
    have h1 : (p : ℤ) ∣ x.num * (b : ℤ) := by
      rw [hZ]; exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hpd) z
    rcases (Int.Prime.dvd_mul' hpp h1) with h2 | h2
    · have h3 : p ∣ x.num.natAbs := Int.natCast_dvd.mp h2
      exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hpp, h3, hpd⟩) x.reduced
    · exact hb (Int.natCast_dvd_natCast.mp h2)
  exact ⟨x.num, by exact_mod_cast Rat.coe_int_num_of_den_eq_one hden⟩

end A300386

namespace A300386
open Finset PowerSeries LtsJacobsthal

noncomputable def Lg : PowerSeries ℚ := mk fun n => if n = 0 then 0 else cQ n / (n : ℚ)

lemma constantCoeff_Lg : constantCoeff Lg = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Lg, coeff_mk]; simp

lemma deriv_Lg : derivative ℚ Lg = Phi := by
  ext n
  rw [coeff_derivative, Lg, coeff_mk, if_neg (Nat.succ_ne_zero n), Phi, coeff_mk]
  have hne : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [show ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) by push_cast; ring, div_mul_cancel₀ _ hne]

lemma key2 (p : ℕ) (hp1 : 1 ≤ p) : coeff p (As ^ p) = coeff p (EKg Lg p (p : ℚ)) := by
  set E := EKg Lg p (p : ℚ) with hE
  set R := C ((p : ℚ) ^ p / (p.factorial : ℚ)) with hR
  have hdE : derivative ℚ E = C (p : ℚ) * derivative ℚ Lg * (E - R * Lg ^ p) :=
    deriv_EKg Lg p p
  have hzero := uniq p (As ^ p - E) (C (p : ℚ) * Phi)
    (by
      rw [map_sub, map_pow, hE, constantCoeff_EKg _ constantCoeff_Lg, constantCoeff_As]
      simp)
    (by
      intro j hj
      have hid : derivative ℚ (As ^ p - E) - C (p : ℚ) * Phi * (As ^ p - E)
          = (C (p : ℚ) * Phi * R) * Lg ^ p := by
        rw [map_sub, derivative_pow, hdE, deriv_As, deriv_Lg]
        have hc : ((p : ℕ) : PowerSeries ℚ) = C (p : ℚ) := (map_natCast C p).symm
        rw [hc]
        have hpow : As ^ p = As ^ (p - 1) * As := by
          rw [← pow_succ]; congr 1; omega
        rw [hpow]
        ring
      rw [hid]
      exact coeff_lowg _ constantCoeff_Lg _ _ hj _)
    p le_rfl
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

variable {p : ℕ} [hp : Fact p.Prime]

lemma D_Lg_low {j : ℕ} (hj : j < p) : D p 0 (coeff j Lg) := by
  rw [Lg, coeff_mk]
  split_ifs with h0
  · exact D.zero 0
  · rw [div_eq_mul_inv]
    refine (D_cQ j (by omega)).mul0 (D.inv ?_)
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega

lemma D_Lpow_low (e : ℕ) {j : ℕ} (hj : j < p) : D p 0 (coeff j (Lg ^ e)) := by
  induction e generalizing j with
  | zero =>
    rw [pow_zero, coeff_one]
    split_ifs
    · exact D.one
    · exact D.zero 0
  | succ e ih =>
    rw [pow_succ, coeff_mul]
    refine D.sum _ _ fun x hx => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    exact (ih (by omega)).mul0 (D_Lg_low (by omega))

lemma D_Lpow_p (d : ℕ) (hd : 2 ≤ d) : D p 0 (coeff p (Lg ^ d)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 + 1 := ⟨d - 2, by omega⟩
  rw [pow_succ', coeff_mul]
  refine D.sum _ _ fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  by_cases h1 : x.1 = 0
  · rw [h1, coeff_zero_eq_constantCoeff_apply, constantCoeff_Lg, zero_mul]; exact D.zero 0
  · by_cases h2 : x.2 = 0
    · rw [h2, coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_Lg, zero_pow (by omega),
        mul_zero]
      exact D.zero 0
    · exact (D_Lg_low (by omega)).mul0 (D_Lpow_low _ (by omega))

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

lemma coeffE (h5 : 5 ≤ p) :
    D p 3 (coeff p (EKg Lg p (p : ℚ)) - cQ p - (p : ℚ) ^ 2 / 2 * coeff p (Lg ^ 2)) := by
  obtain ⟨K', hK⟩ : ∃ K', p = K' + 2 := ⟨p - 2, by omega⟩
  rw [show EKg Lg p (p : ℚ) = EKg Lg (K' + 2) (p : ℚ) by rw [← hK]]
  rw [EKg, map_sum, show K' + 2 + 1 = K' + 1 + 1 + 1 by ring, Finset.sum_range_succ',
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [coeff_C_mul]
  have c0 : coeff p (Lg ^ 0) = 0 := by rw [pow_zero, coeff_one, if_neg hp.out.ne_zero]
  have c1 : coeff p (Lg ^ (0 + 1)) = cQ p / (p : ℚ) := by
    rw [zero_add, pow_one, Lg, coeff_mk, if_neg hp.out.ne_zero]
  rw [c0, c1]
  have hA : D p 3 (∑ i ∈ range K', (p : ℚ) ^ (i + 1 + 1 + 1) /
      (((i + 1 + 1 + 1).factorial : ℕ) : ℚ) * coeff p (Lg ^ (i + 1 + 1 + 1))) :=
    D.sum _ _ fun d _ => D_tail h5 (s := 1) le_rfl (M := p) (by rw [pow_one]) d _
      (D_Lpow_p (d + 3) (by omega))
  have hB : (p : ℚ) ^ (0 + 1 + 1) / (((0 + 1 + 1).factorial : ℕ) : ℚ) = (p : ℚ) ^ 2 / 2 := by
    norm_num [Nat.factorial]
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hC : (p : ℚ) ^ (0 + 1) / (((0 + 1).factorial : ℕ) : ℚ) * (cQ p / (p : ℚ)) = cQ p := by
    norm_num [Nat.factorial]; field_simp
  refine hA.congr ?_
  rw [hB, hC]
  ring

lemma D_L2 (h5 : 11 ≤ p) (h11 : p ≠ 7) : D p 1 (coeff p (Lg ^ 2)) := by
  rw [pow_two, coeff_mul]
  refine D.sum _ _ fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  by_cases h1 : x.1 = 0
  · rw [h1, coeff_zero_eq_constantCoeff_apply, constantCoeff_Lg, zero_mul]; exact D.zero 1
  · by_cases h2 : x.2 = 0
    · rw [h2, coeff_zero_eq_constantCoeff_apply, constantCoeff_Lg, mul_zero]; exact D.zero 1
    · have hx2 : x.2 = p - x.1 := by omega
      have hc := carry h5 (i := x.1) (by omega) (by omega)
      rw [← hx2] at hc
      have hN : D p 1 (((Nat.choose (7 * x.1) (2 * x.1) * Nat.choose (7 * x.2) (2 * x.2) : ℕ) : ℚ)) :=
        D_natq _ hc
      have hnd : ∀ j : ℕ, 0 < j → j < p → ¬ p ∣ j := by
        intro j hj0 hjp hd; have := Nat.le_of_dvd hj0 hd; omega
      have h11' : ¬ p ∣ 7 := by
        intro hd
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd with h | h
        · exact hp.out.one_lt.ne' h
        · exact h11 h
      have hU : D p 0 ((7 : ℚ)⁻¹ * (7 : ℚ)⁻¹ * ((x.1 : ℕ) : ℚ)⁻¹ * ((x.2 : ℕ) : ℚ)⁻¹) := by
        have e11 : (7 : ℚ)⁻¹ = ((7 : ℕ) : ℚ)⁻¹ := by norm_num
        rw [e11]
        exact (((D.inv h11').mul0 (D.inv h11')).mul0 (D.inv (hnd x.1 (by omega) (by omega)))).mul0
          (D.inv (hnd x.2 (by omega) (by omega)))
      refine (hN.mul0 hU).congr ?_
      rw [Lg, coeff_mk, coeff_mk, if_neg h1, if_neg h2, cQ, cQ]
      push_cast
      ring

lemma cQ_p (h5 : 5 ≤ p) (h11 : p ≠ 7) : D p 3 (cQ p - 3) := by
  have hj := jacobsthal (p := p) h5 7 2 1 le_rfl
  simp only [pow_one, Nat.sub_self, pow_zero, mul_one] at hj
  have h21 : Nat.choose 7 2 = 21 := by decide
  rw [h21] at hj
  have h11' : ¬ p ∣ 7 := by
    intro hd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd with h | h
    · exact hp.out.one_lt.ne' h
    · exact h11 h
  apply D.ucancel h11'
  refine (D_of_dvdZ hj).congr ?_
  unfold cQ
  rw [mul_comm 7 p, mul_comm 2 p]
  push_cast
  ring

lemma main_D (h5 : 11 ≤ p) (h11 : p ≠ 7) : D p 3 (coeff p (As ^ p) - 3) := by
  rw [key2 p (by omega)]
  have h1 := coeffE (p := p) (by omega)
  have hp2 : ¬ p ∣ 2 := by
    intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
  have h2 : D p 3 ((p : ℚ) ^ 2 / 2 * coeff p (Lg ^ 2)) := by
    have := ((D.ppow (p := p) 2).mul (D_L2 h5 h11)).mul0 (D.inv hp2)
    refine this.congr ?_
    push_cast
    ring
  exact ((h1.add h2).add (cQ_p (by omega) h11)).congr (by ring)

omit hp in
lemma b_eq (p : ℕ) : OMA.S_oeis_a300386.b p = coeff p (As ^ p) := by
  unfold OMA.S_oeis_a300386.b
  rw [← Polynomial.coeff_coe, Polynomial.coe_pow]
  refine coeff_agree_pow (n := p) (fun k hk => ?_) p p le_rfl
  rw [Polynomial.coeff_coe, Polynomial.finsetSum_coeff, As, coeff_mk]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_range.mpr (by omega))]

end A300386

theorem OMA.solution : type_of% @OMA.S_oeis_a300386.main := by
  intro p hp hp11
  have := Fact.mk hp
  obtain ⟨z, hz⟩ := A300386.rat_int (OMA.S_oeis_a300386.b p) (fun q hq => by
    have := Fact.mk hq
    rw [A300386.b_eq]
    exact (A300386.I.pow0 (q := q) (fun n => A300386.a_int n) p) p)
  have hp7 : p ≠ 7 := by omega
  have h := A300386.main_D (p := p) hp11 hp7
  rw [← A300386.b_eq, ← hz] at h
  have hd : ((p : ℤ) ^ 3) ∣ z - 3 := by
    apply LtsJacobsthal.D.dvd
    push_cast
    exact h
  obtain ⟨m, hm⟩ := hd
  refine ⟨m, ?_⟩
  rw [← hz]
  have : ((z - 3 : ℤ) : ℚ) = (((p : ℤ) ^ 3 * m : ℤ) : ℚ) := by rw [hm]
  push_cast at this ⊢
  linarith
