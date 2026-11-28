import OMAStatements.S_oeis_a364181
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

namespace A364181P
open Nat LtsJacobsthal Finset
open OMA.S_oeis_a364181

private lemma hf_step (k : ℕ) : hf (k + 2) = hf k * (((k : ℚ) + 2) / 2) := by
  unfold hf
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have h1 : (j + j + 2) % 2 = 0 := by omega
    have h2 : (j + j) % 2 = 0 := by omega
    have h3 : (j + j + 2) / 2 = j + 1 := by omega
    have h4 : (j + j) / 2 = j := by omega
    rw [if_pos h1, if_pos h2, h3, h4, Nat.factorial_succ]
    push_cast; ring
  · have h1 : ¬ (2 * j + 1 + 2) % 2 = 0 := by omega
    have h2 : ¬ (2 * j + 1) % 2 = 0 := by omega
    have h3 : (2 * j + 1 + 2 + 1) / 2 = (2 * j + 1 + 1) / 2 + 1 := by omega
    rw [if_neg h1, if_neg h2, h3, Nat.doubleFactorial_add_two, pow_succ]
    push_cast
    field_simp

private lemma hf_add (K j : ℕ) :
    hf (K + 2 * j) = hf K * ∏ i ∈ range j, (((K : ℚ) + 2 * ((i : ℚ) + 1)) / 2) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show K + 2 * (j + 1) = (K + 2 * j) + 2 by ring, hf_step, ih, prod_range_succ]
    push_cast; ring

private lemma fact_add (B j : ℕ) :
    (((B + j)! : ℕ) : ℚ) = (B ! : ℚ) * ∏ i ∈ range j, ((B : ℚ) + ((i : ℚ) + 1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show B + (j + 1) = (B + j) + 1 by ring, Nat.factorial_succ, prod_range_succ]
    push_cast
    rw [ih]; ring

private lemma hf_pos2 (k : ℕ) : 0 < hf k ∧ 0 < hf (k + 1) := by
  induction k with
  | zero =>
    unfold hf
    norm_num
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [show k + 1 + 1 = k + 2 by ring, hf_step]
    have := ih.1
    positivity

private lemma hf_pos (k : ℕ) : 0 < hf k := (hf_pos2 k).1

/-- `G N = ∏_{0 ≤ i < 3N} (4N + 2i)/(3N + 2i)` -/
def G (N : ℕ) : ℚ := ∏ i ∈ range (3 * N), ((4 * (N : ℚ) + 2 * (i : ℚ)) / (3 * (N : ℚ) + 2 * (i : ℚ)))

private lemma a_eq0 (N : ℕ) :
    a N = ((10 * N).choose (5 * N) : ℚ) *
      ∏ i ∈ range (3 * N), ((4 * (N : ℚ) + 2 * ((i : ℚ) + 1)) / (3 * (N : ℚ) + 2 * ((i : ℚ) + 1))) := by
  unfold a
  have h9 : hf (9 * N) = hf (3 * N) * ∏ i ∈ range (3 * N), ((((3 * N : ℕ) : ℚ) + 2 * ((i : ℚ) + 1)) / 2) := by
    rw [show 9 * N = 3 * N + 2 * (3 * N) by ring]; exact hf_add _ _
  have h5 : (((5 * N)! : ℕ) : ℚ) = ((2 * N)! : ℚ) * ∏ i ∈ range (3 * N), (((2 * N : ℕ) : ℚ) + ((i : ℚ) + 1)) := by
    rw [show 5 * N = 2 * N + 3 * N by ring]; exact fact_add _ _
  have hc : ((10 * N).choose (5 * N) : ℚ) = ((10 * N)! : ℚ) / (((5 * N)! : ℚ) * ((5 * N)! : ℚ)) := by
    rw [Nat.cast_choose ℚ (by omega : 5 * N ≤ 10 * N), show 10 * N - 5 * N = 5 * N by omega]
  have hp : ∏ i ∈ range (3 * N), ((4 * (N : ℚ) + 2 * ((i : ℚ) + 1)) / (3 * (N : ℚ) + 2 * ((i : ℚ) + 1))) =
      (∏ i ∈ range (3 * N), (((2 * N : ℕ) : ℚ) + ((i : ℚ) + 1))) /
        ∏ i ∈ range (3 * N), ((((3 * N : ℕ) : ℚ) + 2 * ((i : ℚ) + 1)) / 2) := by
    rw [← prod_div_distrib]
    refine prod_congr rfl fun i _ => ?_
    push_cast
    have : (3 * (N : ℚ) + 2 * ((i : ℚ) + 1)) ≠ 0 := by positivity
    field_simp
    ring
  have hP1 : ∏ i ∈ range (3 * N), ((((3 * N : ℕ) : ℚ) + 2 * ((i : ℚ) + 1)) / 2) ≠ 0 := by
    rw [prod_ne_zero_iff]; intro i _; positivity
  have hP2 : ∏ i ∈ range (3 * N), (((2 * N : ℕ) : ℚ) + ((i : ℚ) + 1)) ≠ 0 := by
    rw [prod_ne_zero_iff]; intro i _; positivity
  have hh := (hf_pos (3 * N)).ne'
  rw [h9, hc, hp, h5]
  have f2 : ((2 * N)! : ℚ) ≠ 0 := by positivity
  field_simp

private lemma a_eq (N : ℕ) (hN : 1 ≤ N) :
    a N = ((10 * N).choose (5 * N) : ℚ) * (5 / 6) * G N := by
  rw [a_eq0]
  set g : ℕ → ℚ := fun i => (4 * (N : ℚ) + 2 * (i : ℚ)) / (3 * (N : ℚ) + 2 * (i : ℚ)) with hg
  have e1 := prod_range_succ' g (3 * N)
  have e2 := prod_range_succ g (3 * N)
  have hN0 : (N : ℚ) ≠ 0 := by positivity
  have g0 : g 0 = 4 / 3 := by simp only [hg]; push_cast; field_simp; ring
  have g3 : g (3 * N) = 10 / 9 := by simp only [hg]; push_cast; field_simp; ring
  have hG : G N = ∏ i ∈ range (3 * N), g i := rfl
  have hs : ∏ i ∈ range (3 * N), ((4 * (N : ℚ) + 2 * ((i : ℚ) + 1)) / (3 * (N : ℚ) + 2 * ((i : ℚ) + 1))) =
      ∏ i ∈ range (3 * N), g (i + 1) := by
    refine prod_congr rfl fun i _ => ?_
    simp only [hg]; push_cast; ring
  rw [hs, hG]
  rw [g0] at e1
  rw [g3] at e2
  have : ∏ i ∈ range (3 * N), g (i + 1) = 5 / 6 * ∏ i ∈ range (3 * N), g i := by
    linear_combination (-3 / 4 : ℚ) * (e2.symm.trans e1)
  rw [this]; ring


variable {p : ℕ} [hp : Fact p.Prime]

private lemma G_split (hp0 : 0 < p) (M : ℕ) (hM : 1 ≤ M) :
    G (p * M) = G M * (R p (-(2 * (p : ℚ) * (M : ℚ))) (p * (3 * M)) /
      R p (-(3 / 2 * (p : ℚ) * (M : ℚ))) (p * (3 * M))) := by
  unfold G
  rw [show 3 * (p * M) = p * (3 * M) by ring, prod_range_mul_split p (3 * M) hp0]
  have hA : ∏ k ∈ (range (p * (3 * M))).filter (fun k => ¬ p ∣ k),
      ((4 * ((p * M : ℕ) : ℚ) + 2 * (k : ℚ)) / (3 * ((p * M : ℕ) : ℚ) + 2 * (k : ℚ))) =
      R p (-(2 * (p : ℚ) * (M : ℚ))) (p * (3 * M)) / R p (-(3 / 2 * (p : ℚ) * (M : ℚ))) (p * (3 * M)) := by
    unfold R U
    rw [← prod_div_distrib]
    refine prod_congr rfl fun i hi => ?_
    have hi0 : (i : ℚ) ≠ 0 := by
      have : i ≠ 0 := by
        rintro rfl
        simp at hi
      exact_mod_cast this
    have e1 : 1 - (-(2 * (p : ℚ) * (M : ℚ))) / (i : ℚ) =
        (4 * ((p * M : ℕ) : ℚ) + 2 * (i : ℚ)) / (2 * (i : ℚ)) := by
      push_cast; field_simp; ring
    have e2 : 1 - (-(3 / 2 * (p : ℚ) * (M : ℚ))) / (i : ℚ) =
        (3 * ((p * M : ℕ) : ℚ) + 2 * (i : ℚ)) / (2 * (i : ℚ)) := by
      push_cast; field_simp; ring
    rw [e1, e2, div_div_div_cancel_right₀ (mul_ne_zero two_ne_zero hi0)]
  have hB : ∏ c ∈ range (3 * M),
      ((4 * ((p * M : ℕ) : ℚ) + 2 * ((p * c : ℕ) : ℚ)) / (3 * ((p * M : ℕ) : ℚ) + 2 * ((p * c : ℕ) : ℚ))) =
      ∏ c ∈ range (3 * M), ((4 * (M : ℚ) + 2 * (c : ℚ)) / (3 * (M : ℚ) + 2 * (c : ℚ))) := by
    refine prod_congr rfl fun c _ => ?_
    push_cast
    have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
    rw [show 4 * ((p : ℚ) * M) + 2 * (p * c) = p * (4 * M + 2 * c) by ring,
      show 3 * ((p : ℚ) * M) + 2 * (p * c) = p * (3 * M + 2 * c) by ring, mul_div_mul_left _ _ hp']
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

private lemma rho (h5 : 5 ≤ p) (a b r : ℕ) (hr : 1 ≤ r) :
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

private lemma D_inv_unit {e : ℕ} {x : ℚ} (he : 1 ≤ e) (h : D p e (x - 1)) : D p 0 x⁻¹ := by
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

private lemma D_one_add {e : ℕ} {x : ℚ} (h : D p e (x - 1)) : D p 0 x :=
  ((h.le (Nat.zero_le _)).add D.one).congr (by ring)

private lemma D_ne_zero {e : ℕ} {x : ℚ} (he : 1 ≤ e) (h : D p e (x - 1)) : x ≠ 0 := by
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

/-! ### p-integrality of `a` -/

private lemma Dfrac {X Y : ℕ} (hX : X ≠ 0) (hY : Y ≠ 0) (h : padicValNat p Y ≤ padicValNat p X) :
    D p 0 ((X : ℚ) / (Y : ℚ)) := by
  obtain ⟨Y', hY'⟩ := (pow_padicValNat_dvd : p ^ padicValNat p Y ∣ Y)
  obtain ⟨X', hX'⟩ := (pow_dvd_pow p h).trans (pow_padicValNat_dvd : p ^ padicValNat p X ∣ X)
  have hY'0 : Y' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hY'
    exact hY hY'
  have hnd : ¬ p ∣ Y' := by
    intro hd
    have h1 := one_le_padicValNat_of_dvd hY'0 hd
    have h2 : padicValNat p Y = padicValNat p Y + padicValNat p Y' := by
      conv_lhs => rw [hY']
      rw [padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hY'0, padicValNat.prime_pow]
    omega
  refine ⟨(X' : ℤ), Y', hnd, ?_⟩
  rw [Int.cast_natCast]
  have hpv : ((p : ℚ) ^ padicValNat p Y) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hY'q : (Y' : ℚ) ≠ 0 := by exact_mod_cast hY'0
  have eX : (X : ℚ) = (p : ℚ) ^ padicValNat p Y * (X' : ℚ) := by exact_mod_cast hX'
  have eY : (Y : ℚ) = (p : ℚ) ^ padicValNat p Y * (Y' : ℚ) := by exact_mod_cast hY'
  rw [eX, eY]
  field_simp

private lemma fl (c d q m : ℕ) (hcd : c * d = 180) :
    (c * m) / q = (c * ((180 * m) / q)) / 180 := by
  have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hcd)
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hcd)
  rw [← hcd, Nat.mul_div_mul_left _ _ hc, Nat.div_div_eq_div_mul,
    show c * d * m = c * m * d by ring, Nat.mul_div_mul_right _ _ hd]

private lemma kred (k : ℕ) :
    (10*k)/180 + (18*k)/180 + (3*k)/180 + (4*k)/180 ≤ (20*k)/180 + (6*k)/180 + (9*k)/180 := by
  obtain ⟨B, κ, hκ, rfl⟩ : ∃ B κ, κ < 180 ∧ k = κ + 180 * B :=
    ⟨k / 180, k % 180, Nat.mod_lt _ (by norm_num), (Nat.mod_add_div k 180).symm⟩
  have h : ∀ c, (c * (κ + 180 * B)) / 180 = (c * κ) / 180 + c * B := fun c => by
    rw [show c * (κ + 180 * B) = c * κ + 180 * (c * B) by ring, Nat.add_mul_div_left _ _ (by norm_num)]
  rw [h, h, h, h, h, h, h]
  interval_cases κ <;> omega

private lemma floorE (q m : ℕ) :
    (10 * m) / q + (9 * m) / q + (4 * m) / q ≤ (20 * m) / q + (3 * m) / q := by
  rw [fl 10 18 q m (by norm_num), fl 9 20 q m (by norm_num), fl 4 45 q m (by norm_num),
    fl 20 9 q m (by norm_num), fl 3 60 q m (by norm_num)]
  generalize 180 * m / q = k
  omega

private lemma floorO (q m : ℕ) :
    (5 * (2 * m + 1)) / q + (2 * (9 * m + 4) + 1) / q + (3 * m + 1) / q + (2 * (2 * m + 1)) / q ≤
      (10 * (2 * m + 1)) / q + (2 * (3 * m + 1) + 1) / q + (9 * m + 4) / q := by
  have t : ∀ x, x / q = (2 * x) / (2 * q) := fun x => (Nat.mul_div_mul_left x q two_pos).symm
  have h1 : (9 * m + 4) / q = (9 * (2 * m + 1)) / (2 * q) := by
    rw [t, show 9 * (2 * m + 1) = 2 * (9 * m + 4) + 1 by ring, Nat.succ_div_of_not_dvd]
    intro h
    have := (dvd_mul_right 2 q).trans h
    omega
  have h2 : (3 * m + 1) / q = (3 * (2 * m + 1)) / (2 * q) := by
    rw [t, show 3 * (2 * m + 1) = 2 * (3 * m + 1) + 1 by ring, Nat.succ_div_of_not_dvd]
    intro h
    have := (dvd_mul_right 2 q).trans h
    omega
  rw [h1, h2, t (5 * (2 * m + 1)), t (2 * (9 * m + 4) + 1), t (2 * (2 * m + 1)),
    t (10 * (2 * m + 1)), t (2 * (3 * m + 1) + 1),
    show 2 * (5 * (2 * m + 1)) = 10 * (2 * m + 1) by ring,
    show 2 * (2 * (9 * m + 4) + 1) = 18 * (2 * m + 1) by ring,
    show 2 * (2 * (2 * m + 1)) = 4 * (2 * m + 1) by ring,
    show 2 * (10 * (2 * m + 1)) = 20 * (2 * m + 1) by ring,
    show 2 * (2 * (3 * m + 1) + 1) = 6 * (2 * m + 1) by ring]
  rw [fl 10 18 (2 * q) (2 * m + 1) (by norm_num), fl 18 10 (2 * q) (2 * m + 1) (by norm_num),
    fl 3 60 (2 * q) (2 * m + 1) (by norm_num), fl 4 45 (2 * q) (2 * m + 1) (by norm_num),
    fl 20 9 (2 * q) (2 * m + 1) (by norm_num), fl 6 30 (2 * q) (2 * m + 1) (by norm_num),
    fl 9 20 (2 * q) (2 * m + 1) (by norm_num)]
  exact kred _

private lemma ve (m : ℕ) :
    padicValNat p ((10 * m)! * (9 * m)! * (4 * m)!) ≤ padicValNat p ((20 * m)! * (3 * m)!) := by
  have f0 := Nat.factorial_ne_zero
  rw [padicValNat.mul (mul_ne_zero (f0 _) (f0 _)) (f0 _), padicValNat.mul (f0 _) (f0 _),
    padicValNat.mul (f0 _) (f0 _)]
  have hB : ∀ x, x ≤ 20 * m → Nat.log p x < 20 * m + 1 := fun x hx =>
    lt_of_le_of_lt (Nat.log_le_self p x) (by omega)
  rw [padicValNat_factorial (hB (10 * m) (by omega)), padicValNat_factorial (hB (9 * m) (by omega)),
    padicValNat_factorial (hB (4 * m) (by omega)), padicValNat_factorial (hB (20 * m) (by omega)),
    padicValNat_factorial (hB (3 * m) (by omega))]
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  exact floorE (p ^ i) m

private lemma vo (m : ℕ) :
    padicValNat p ((5 * (2 * m + 1))! * (2 * (9 * m + 4) + 1)! * (3 * m + 1)! * (2 * (2 * m + 1))!) ≤
      padicValNat p ((10 * (2 * m + 1))! * (2 * (3 * m + 1) + 1)! * (9 * m + 4)!) := by
  have f0 := Nat.factorial_ne_zero
  rw [padicValNat.mul (mul_ne_zero (mul_ne_zero (f0 _) (f0 _)) (f0 _)) (f0 _),
    padicValNat.mul (mul_ne_zero (f0 _) (f0 _)) (f0 _), padicValNat.mul (f0 _) (f0 _),
    padicValNat.mul (mul_ne_zero (f0 _) (f0 _)) (f0 _), padicValNat.mul (f0 _) (f0 _)]
  have hB : ∀ x, x ≤ 20 * m + 20 → Nat.log p x < 20 * m + 21 := fun x hx =>
    lt_of_le_of_lt (Nat.log_le_self p x) (by omega)
  rw [padicValNat_factorial (hB (5 * (2 * m + 1)) (by omega)),
    padicValNat_factorial (hB (2 * (9 * m + 4) + 1) (by omega)),
    padicValNat_factorial (hB (3 * m + 1) (by omega)),
    padicValNat_factorial (hB (2 * (2 * m + 1)) (by omega)),
    padicValNat_factorial (hB (10 * (2 * m + 1)) (by omega)),
    padicValNat_factorial (hB (2 * (3 * m + 1) + 1) (by omega)),
    padicValNat_factorial (hB (9 * m + 4) (by omega))]
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  exact floorO (p ^ i) m

private lemma a_even (m : ℕ) :
    a (2 * m) = (((20 * m)! * (3 * m)! : ℕ) : ℚ) / (((10 * m)! * (9 * m)! * (4 * m)! : ℕ) : ℚ) := by
  unfold a hf
  rw [if_pos (by omega : 3 * (2 * m) % 2 = 0), if_pos (by omega : 9 * (2 * m) % 2 = 0),
    show 3 * (2 * m) / 2 = 3 * m by omega, show 9 * (2 * m) / 2 = 9 * m by omega,
    show 10 * (2 * m) = 20 * m by ring, show 5 * (2 * m) = 10 * m by ring,
    show 2 * (2 * m) = 4 * m by ring]
  push_cast
  ring

private lemma hf_odd (k : ℕ) :
    hf (2 * k + 1) = (((2 * k + 1)! : ℕ) : ℚ) / ((2 : ℚ) ^ (2 * k + 1) * (k ! : ℚ)) := by
  unfold hf
  rw [if_neg (by omega), show (2 * k + 1 + 1) / 2 = k + 1 by omega]
  have := Nat.factorial_eq_mul_doubleFactorial (2 * k)
  rw [Nat.doubleFactorial_two_mul] at this
  rw [this]
  push_cast
  field_simp
  ring

private lemma a_odd (m : ℕ) :
    a (2 * m + 1) = (2 : ℚ) ^ (12 * m + 6) *
      ((((10 * (2 * m + 1))! * (2 * (3 * m + 1) + 1)! * (9 * m + 4)! : ℕ) : ℚ) /
        (((5 * (2 * m + 1))! * (2 * (9 * m + 4) + 1)! * (3 * m + 1)! * (2 * (2 * m + 1))! : ℕ) : ℚ)) := by
  unfold a
  rw [show 3 * (2 * m + 1) = 2 * (3 * m + 1) + 1 by ring, show 9 * (2 * m + 1) = 2 * (9 * m + 4) + 1 by ring,
    hf_odd, hf_odd]
  push_cast
  field_simp
  ring

private lemma a_int (M : ℕ) : D p 0 (a M) := by
  rcases Nat.even_or_odd' M with ⟨m, rfl | rfl⟩
  · rw [a_even]
    exact Dfrac (by positivity) (by positivity) (ve m)
  · rw [a_odd]
    exact (D.two.pow0 _).mul0' (Dfrac (by positivity) (by positivity) (vo m))

/-! ### the main argument -/

theorem main' (h5 : 5 ≤ p) (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    D p (3 * r) (a (n * p ^ r) - a (n * p ^ (r - 1))) := by
  have hp0 : 0 < p := hp.out.pos
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hM : 1 ≤ n * p ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hNM : n * p ^ (k + 1) = p * (n * p ^ k) := by ring
  obtain ⟨ρ1, d1, h1⟩ := rho h5 (10 * n) (5 * n) (k + 1) (by omega)
  simp only [Nat.add_sub_cancel] at h1
  have hA1 : D p 0 (-(2 * (n : ℚ))) := (D.two.mul0 (D.nat n)).neg
  have hA2 : D p 0 (-(3 / 2 * (n : ℚ))) :=
    (((D.three.mul0 (D.inv hp2)).mul0 (D.nat n)).neg).congr (by push_cast; ring)
  have dR1 := R_D' h5 (by omega : 1 ≤ k + 1) _ hA1 (3 * n)
  have dR2 := R_D' h5 (by omega : 1 ≤ k + 1) _ hA2 (3 * n)
  set R1 := R p (-(2 * (n : ℚ)) * (p : ℚ) ^ (k + 1)) (3 * n * p ^ (k + 1)) with hR1
  set R2 := R p (-(3 / 2 * (n : ℚ)) * (p : ℚ) ^ (k + 1)) (3 * n * p ^ (k + 1)) with hR2
  have eR1 : R p (-(2 * (p : ℚ) * ((n * p ^ k : ℕ) : ℚ))) (p * (3 * (n * p ^ k))) = R1 := by
    rw [hR1]; congr 1
    · push_cast; ring
    · ring
  have eR2 : R p (-(3 / 2 * (p : ℚ) * ((n * p ^ k : ℕ) : ℚ))) (p * (3 * (n * p ^ k))) = R2 := by
    rw [hR2]; congr 1
    · push_cast; ring
    · ring
  have hG := G_split hp0 (n * p ^ k) hM
  rw [eR1, eR2] at hG
  have hN1 : 1 ≤ p * (n * p ^ k) := by nlinarith
  have hc1 : ((10 * (p * (n * p ^ k))).choose (5 * (p * (n * p ^ k))) : ℚ) =
      ((10 * (n * p ^ k)).choose (5 * (n * p ^ k)) : ℚ) * ρ1 := by
    rw [show 10 * (p * (n * p ^ k)) = 10 * n * p ^ (k + 1) by ring,
      show 5 * (p * (n * p ^ k)) = 5 * n * p ^ (k + 1) by ring, h1,
      show 10 * n * p ^ k = 10 * (n * p ^ k) by ring, show 5 * n * p ^ k = 5 * (n * p ^ k) by ring]
  have hR2ne : R2 ≠ 0 := D_ne_zero (by omega) dR2
  have e123 : D p (3 * (k + 1)) (ρ1 * R1 - R2) :=
    (((d1.mul0 (D_one_add dR1)).add dR1).sub dR2).congr (by ring)
  have key := (a_int (p := p) (n * p ^ k)).mul0' (e123.mul0 (D_inv_unit (by omega) dR2))
  refine key.congr ?_
  rw [hNM, a_eq _ hN1, a_eq _ hM, hG, hc1]
  field_simp

end A364181P

theorem OMA.solution : type_of% @OMA.S_oeis_a364181.main := by
  intro p hp h5 n r hn hr
  have := Fact.mk hp
  obtain ⟨a', b, hb, h⟩ := A364181P.main' h5 n r hn hr
  have hb0 : (b : ℚ) ≠ 0 := by
    have : b ≠ 0 := by rintro rfl; exact hb (dvd_zero p)
    exact_mod_cast this
  refine ⟨(a' : ℚ) / (b : ℚ), ?_, ?_⟩
  · have e : (a' : ℚ) / (b : ℚ) = Rat.divInt a' (b : ℤ) := by
      rw [Rat.divInt_eq_div]; push_cast; rfl
    rw [e]
    have hd : ((Rat.divInt a' (b : ℤ)).den : ℤ) ∣ (b : ℤ) := Rat.den_dvd a' b
    have hd' : (Rat.divInt a' (b : ℤ)).den ∣ b := Int.natCast_dvd_natCast.mp hd
    exact Nat.Coprime.coprime_dvd_left hd' (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hb))
  · field_simp
    linear_combination h
