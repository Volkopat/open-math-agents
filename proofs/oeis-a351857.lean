import OMAStatements.S_oeis_a351857
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

example : True := trivial

namespace A351857P

noncomputable def th {R : Type*} [CommRing R] (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => (n : R) * PowerSeries.coeff n f

lemma coeff_th {R : Type*} [CommRing R] (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (th f) = (n : R) * PowerSeries.coeff n f := by
  simp [th, PowerSeries.coeff_mk]

lemma th_add {R : Type*} [CommRing R] (f g : PowerSeries R) : th (f + g) = th f + th g := by
  ext n; simp only [coeff_th, map_add]; ring

lemma th_sub {R : Type*} [CommRing R] (f g : PowerSeries R) : th (f - g) = th f - th g := by
  ext n; simp only [coeff_th, map_sub]; ring

lemma th_mul {R : Type*} [CommRing R] (f g : PowerSeries R) :
    th (f * g) = th f * g + f * th g := by
  ext n
  rw [map_add, coeff_th, PowerSeries.coeff_mul, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [coeff_th, coeff_th]
  have h : (n : R) = (x.1 : R) + (x.2 : R) := by rw [← hx]; push_cast; ring
  rw [h]; ring

lemma th_C {R : Type*} [CommRing R] (r : R) : th (PowerSeries.C r) = 0 := by
  ext n
  rw [coeff_th, PowerSeries.coeff_C, map_zero]
  split_ifs with h
  · rw [h]; simp
  · simp

lemma th_one {R : Type*} [CommRing R] : th (1 : PowerSeries R) = 0 := by
  rw [← map_one (PowerSeries.C (R := R))]; exact th_C 1

lemma th_Cmul {R : Type*} [CommRing R] (r : R) (f : PowerSeries R) :
    th (PowerSeries.C r * f) = PowerSeries.C r * th f := by
  rw [th_mul, th_C]; ring

lemma th_X {R : Type*} [CommRing R] : th (PowerSeries.X : PowerSeries R) = PowerSeries.X := by
  ext n
  rw [coeff_th, PowerSeries.coeff_X]
  split_ifs with h
  · rw [h]; simp
  · simp

lemma th_pow {R : Type*} [CommRing R] (f : PowerSeries R) (k : ℕ) :
    th (f ^ (k + 1)) = PowerSeries.C ((k + 1 : ℕ) : R) * f ^ k * th f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, th_mul, ih]
    have h : PowerSeries.C (((k + 1 + 1 : ℕ)) : R) = PowerSeries.C ((k + 1 : ℕ) : R) + 1 := by
      rw [← map_one (PowerSeries.C (R := R)), ← map_add]; push_cast; ring_nf
    rw [h]; ring

lemma th_map (f : PowerSeries ℤ) :
    th (PowerSeries.map (Int.castRingHom ℚ) f) = PowerSeries.map (Int.castRingHom ℚ) (th f) := by
  ext n
  simp [coeff_th, PowerSeries.coeff_map]

lemma coeff_zero_th {R : Type*} [CommRing R] (f : PowerSeries R) :
    PowerSeries.coeff 0 (th f) = 0 := by
  rw [coeff_th]; simp

/-! truncated exponential -/

noncomputable def Ex (K : ℕ) (A : PowerSeries ℚ) : PowerSeries ℚ :=
  ∑ k ∈ Finset.range K, PowerSeries.C ((k.factorial : ℚ)⁻¹) * A ^ k

lemma Ex_succ (K : ℕ) (A : PowerSeries ℚ) :
    Ex (K + 1) A = Ex K A + PowerSeries.C ((K.factorial : ℚ)⁻¹) * A ^ K := by
  unfold Ex; rw [Finset.sum_range_succ]

lemma th_Ex (K : ℕ) (A : PowerSeries ℚ) : th (Ex (K + 1) A) = Ex K A * th A := by
  induction K with
  | zero => simp [Ex, th_one]
  | succ K ih =>
    rw [Ex_succ, th_add, ih, th_Cmul, th_pow, Ex_succ]
    have h : PowerSeries.C (((K + 1).factorial : ℚ)⁻¹) * PowerSeries.C (((K + 1 : ℕ) : ℚ)) =
        PowerSeries.C ((K.factorial : ℚ)⁻¹) := by
      rw [← map_mul]
      congr 1
      rw [Nat.factorial_succ]
      push_cast
      have : (K.factorial : ℚ) ≠ 0 := by exact_mod_cast K.factorial_ne_zero
      field_simp
    rw [← h]; ring

lemma coeff_zero_Ex (K : ℕ) (A : PowerSeries ℚ) (hA : PowerSeries.coeff 0 A = 0) :
    PowerSeries.coeff 0 (Ex (K + 1) A) = 1 := by
  induction K with
  | zero => simp [Ex]
  | succ K ih =>
    rw [Ex_succ, map_add, ih, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hA]
    simp

/-! ODE uniqueness -/

lemma uniq {K : ℕ} {Y Z B : PowerSeries ℚ} (hB : PowerSeries.coeff 0 B = 0)
    (h0 : PowerSeries.coeff 0 Y = PowerSeries.coeff 0 Z)
    (hY : PowerSeries.X ^ K ∣ th Y - Y * B) (hZ : PowerSeries.X ^ K ∣ th Z - Z * B) :
    ∀ n, n < K → PowerSeries.coeff n Y = PowerSeries.coeff n Z := by
  have hW : PowerSeries.X ^ K ∣ th (Y - Z) - (Y - Z) * B := by
    have e : th (Y - Z) - (Y - Z) * B = (th Y - Y * B) - (th Z - Z * B) := by rw [th_sub]; ring
    rw [e]; exact dvd_sub hY hZ
  rw [PowerSeries.X_pow_dvd_iff] at hW
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rw [← sub_eq_zero, ← map_sub]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [map_sub, h0, sub_self]
    have h := hW n hn
    rw [map_sub, coeff_th, PowerSeries.coeff_mul] at h
    rw [Finset.sum_eq_zero (fun x hx => by
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rcases Nat.eq_zero_or_pos x.2 with h2 | h2
      · rw [h2, hB, mul_zero]
      · rw [map_sub, ih x.1 (by omega) (by omega), sub_self, zero_mul])] at h
    rw [sub_zero] at h
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
    exact (mul_eq_zero.mp h).resolve_left hn0

/-- `Ex` of a sum solves the ODE up to order `K + 1`. -/
lemma Ex_ode (K : ℕ) (A B : PowerSeries ℚ) (hA : PowerSeries.coeff 0 A = 0)
    (hB : PowerSeries.coeff 0 B = 0) :
    PowerSeries.X ^ (K + 1) ∣ th (Ex (K + 1) A * Ex (K + 1) B) -
      (Ex (K + 1) A * Ex (K + 1) B) * (th A + th B) := by
  have hXA : PowerSeries.X ∣ A := PowerSeries.X_dvd_iff.mpr (by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hA)
  have hXB : PowerSeries.X ∣ B := PowerSeries.X_dvd_iff.mpr (by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hB)
  have hXtA : PowerSeries.X ∣ th A := PowerSeries.X_dvd_iff.mpr (by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact (coeff_zero_th A))
  have hXtB : PowerSeries.X ∣ th B := PowerSeries.X_dvd_iff.mpr (by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact (coeff_zero_th B))
  have e : th (Ex (K + 1) A * Ex (K + 1) B) -
      (Ex (K + 1) A * Ex (K + 1) B) * (th A + th B) =
      -(PowerSeries.C ((K.factorial : ℚ)⁻¹) * Ex (K + 1) B) * (A ^ K * th A) -
        (PowerSeries.C ((K.factorial : ℚ)⁻¹) * Ex (K + 1) A) * (B ^ K * th B) := by
    rw [th_mul, th_Ex, th_Ex, Ex_succ K A, Ex_succ K B]; ring
  rw [e, pow_succ]
  exact dvd_sub (Dvd.dvd.mul_left (mul_dvd_mul (pow_dvd_pow_of_dvd hXA K) hXtA) _)
    (Dvd.dvd.mul_left (mul_dvd_mul (pow_dvd_pow_of_dvd hXB K) hXtB) _)

/-- Coefficient `p M` of `expand E1 * E2`. -/
lemma coeff_expand_mul_sum (p : ℕ) (hp : p ≠ 0) (E1 E2 : PowerSeries ℚ) (M : ℕ) :
    PowerSeries.coeff (p * M) (PowerSeries.expand p hp E1 * E2) =
      ∑ i ∈ Finset.range (M + 1), PowerSeries.coeff i E1 * PowerSeries.coeff (p * (M - i)) E2 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hinj : Set.InjOn (fun i => p * i) (Finset.range (M + 1) : Set ℕ) := by
    intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) h
  have hsub : (Finset.range (M + 1)).image (fun i => p * i) ⊆ Finset.range (p * M + 1) := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    rw [Finset.mem_range] at hi ⊢
    have : p * i ≤ p * M := Nat.mul_le_mul_left p (by omega)
    omega
  rw [← Finset.sum_subset hsub, Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [PowerSeries.coeff_expand_mul, Nat.mul_sub]
  · intro u hu hnot
    have hnd : ¬ p ∣ u := by
      rintro ⟨i, rfl⟩
      apply hnot
      refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
      rw [Finset.mem_range] at hu ⊢
      by_contra hc
      have : p * (M + 1) ≤ p * i := Nat.mul_le_mul_left p (by omega)
      rw [Nat.mul_succ] at this
      have : 1 ≤ p := Nat.pos_of_ne_zero hp
      omega
    simp [PowerSeries.coeff_expand_of_not_dvd p hp _ hnd]

/-! the series of A351857 -/

noncomputable def g : PowerSeries ℤ :=
  Ring.inverse ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2))

def cc (m : ℕ) : ℤ := if m = 0 then 0 else 2 + (-1) ^ m

noncomputable def Cz : PowerSeries ℤ := PowerSeries.mk cc

lemma g_mul : g * ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2)) = 1 := by
  rw [mul_comm]
  exact Ring.mul_inverse_cancel _ (by rw [PowerSeries.isUnit_iff_constantCoeff]; simp)

lemma Cz_mul : Cz * (1 - PowerSeries.X ^ 2) = PowerSeries.X + (PowerSeries.X ^ 2 + PowerSeries.X ^ 2 + PowerSeries.X ^ 2) := by
  ext n
  simp only [mul_sub, mul_one, map_sub, map_add, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_X, Cz,
    PowerSeries.coeff_mk, cc]
  rcases n with _ | _ | _ | n
  · simp
  · simp
  · simp
  · simp only [show n + 1 + 1 + 1 - 2 = n + 1 by omega]
    simp [pow_succ]

lemma th_g : th g = g * Cz := by
  have h1 := g_mul
  have h2 : th g * ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2)) +
      g * th ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2)) = 0 := by
    rw [← th_mul, h1, th_one]
  have hP : th ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2) : PowerSeries ℤ) =
      -(Cz * ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2))) := by
    have e : Cz * ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2)) =
        (Cz * (1 - PowerSeries.X ^ 2)) * (1 - PowerSeries.X) := by ring
    rw [e, Cz_mul, th_mul, th_sub, th_sub, th_one, th_X,
      show (PowerSeries.X : PowerSeries ℤ) ^ 2 = PowerSeries.X ^ (1 + 1) by rfl, th_pow, th_X]
    have e2 : (PowerSeries.C (((1 + 1 : ℕ)) : ℤ) : PowerSeries ℤ) = 2 := by
      rw [map_natCast]; norm_num
    rw [e2]; ring
  rw [hP] at h2
  linear_combination (-th g + g * Cz) * h1 + g * h2

/-! rational versions -/

noncomputable def G : PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) g
noncomputable def Cq : PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) Cz

lemma th_G : th G = G * Cq := by
  unfold G Cq; rw [th_map, th_g, map_mul]

lemma coeff_zero_g : PowerSeries.coeff 0 g = 1 := by
  have h := congrArg PowerSeries.constantCoeff g_mul
  rw [map_mul, map_one] at h
  simpa using h

lemma coeff_zero_G : PowerSeries.coeff 0 G = 1 := by
  unfold G; rw [PowerSeries.coeff_map, coeff_zero_g]; simp

lemma coeff_zero_Gpow (m : ℕ) : PowerSeries.coeff 0 (G ^ m) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_G, one_pow]

lemma th_Gpow (m : ℕ) : th (G ^ (m + 1)) = G ^ (m + 1) * (PowerSeries.C ((m + 1 : ℕ) : ℚ) * Cq) := by
  rw [th_pow, th_G]; ring

noncomputable def ell : PowerSeries ℚ := PowerSeries.mk fun m => (cc m : ℚ) / m

noncomputable def Ls (p : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun m => if p ∣ m then 0 else (cc m : ℚ) / m

lemma cc_zero : cc 0 = 0 := by simp [cc]

lemma th_ell : th ell = Cq := by
  ext m
  rw [coeff_th, ell, Cq, PowerSeries.coeff_mk, PowerSeries.coeff_map, Cz, PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [cc_zero]
  · have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    simp only [eq_intCast]
    field_simp

lemma cc_mul_p {p : ℕ} (hp : Odd p) (j : ℕ) : cc (p * j) = cc j := by
  unfold cc
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · have hp0 : p ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hp)
    rw [if_neg (Nat.mul_ne_zero hp0 hj.ne'), if_neg hj.ne', pow_mul, hp.neg_one_pow]

lemma Ex_zero (K : ℕ) : Ex (K + 1) 0 = 1 := by
  unfold Ex
  rw [Finset.sum_range_succ']
  simp

lemma Ex_expand (p : ℕ) (hp : p ≠ 0) (K : ℕ) (A : PowerSeries ℚ) :
    Ex K (PowerSeries.expand p hp A) = PowerSeries.expand p hp (Ex K A) := by
  unfold Ex
  simp [map_sum, PowerSeries.expand_C]

/-- The main identity: `a(p M) = sum_i b_i e_(p (M - i))`. -/
lemma main_identity {p : ℕ} (hp : p.Prime) (hodd : Odd p) (M : ℕ) (hM : 1 ≤ M) :
    PowerSeries.coeff (p * M) (G ^ (2 * (p * M))) =
      ∑ i ∈ Finset.range (M + 1), PowerSeries.coeff i (G ^ (2 * M)) *
        PowerSeries.coeff (p * (M - i))
          (Ex (p * M + 1) (PowerSeries.C ((2 * (p * M) : ℕ) : ℚ) * Ls p)) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  set K := p * M with hK
  set A' : PowerSeries ℚ := PowerSeries.C ((2 * M : ℕ) : ℚ) * ell with hA'
  set B : PowerSeries ℚ := PowerSeries.C ((2 * K : ℕ) : ℚ) * Ls p with hB
  have hA'0 : PowerSeries.coeff 0 A' = 0 := by
    rw [hA', PowerSeries.coeff_C_mul, ell, PowerSeries.coeff_mk]; simp
  have hB0 : PowerSeries.coeff 0 B = 0 := by
    rw [hB, PowerSeries.coeff_C_mul, Ls, PowerSeries.coeff_mk]; simp
  have hA0 : PowerSeries.coeff 0 (PowerSeries.expand p hp0 A') = 0 := by
    rw [show (0 : ℕ) = p * 0 by simp, PowerSeries.coeff_expand_mul]; exact hA'0
  -- ODE for G^(2M)
  have hsmall : ∀ i, i < K + 1 → PowerSeries.coeff i (G ^ (2 * M)) =
      PowerSeries.coeff i (Ex (K + 1) A') := by
    obtain ⟨m, hm⟩ : ∃ m, 2 * M = m + 1 := ⟨2 * M - 1, by omega⟩
    have hode := Ex_ode K A' 0 hA'0 (by simp)
    rw [Ex_zero, mul_one] at hode
    have hthA : th A' + th 0 = PowerSeries.C ((2 * M : ℕ) : ℚ) * Cq := by
      rw [hA', th_Cmul, th_ell, show (0 : PowerSeries ℚ) = PowerSeries.C 0 by simp, th_C, add_zero]
    rw [hthA] at hode
    intro i hi
    refine uniq (B := PowerSeries.C ((2 * M : ℕ) : ℚ) * Cq) ?_ ?_ ?_ hode i hi
    · rw [PowerSeries.coeff_C_mul, Cq, PowerSeries.coeff_map, Cz, PowerSeries.coeff_mk, cc_zero]; simp
    · rw [coeff_zero_Gpow, coeff_zero_Ex K A' hA'0]
    · rw [hm, th_Gpow, ← hm, sub_self]; exact dvd_zero _
  -- ODE for G^(2N)
  have hthAB : th (PowerSeries.expand p hp0 A') + th B =
      PowerSeries.C ((2 * K : ℕ) : ℚ) * Cq := by
    ext n
    rw [map_add, coeff_th, coeff_th, PowerSeries.coeff_expand, hB, hA', PowerSeries.coeff_C_mul,
      PowerSeries.coeff_C_mul, Ls, PowerSeries.coeff_mk, Cq, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_map, Cz, PowerSeries.coeff_mk]
    by_cases hd : p ∣ n
    · obtain ⟨j, rfl⟩ := hd
      rw [if_pos (dvd_mul_right p j), if_pos (dvd_mul_right p j), ell,
        PowerSeries.coeff_mk, Nat.mul_div_cancel_left j hp.pos, cc_mul_p hodd]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [cc_zero]
      · have : (j : ℚ) ≠ 0 := by exact_mod_cast hj.ne'
        have : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
        simp only [eq_intCast, hK]
        push_cast
        field_simp
        ring
    · rw [if_neg hd, if_neg hd]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [cc_zero]
      · have : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
        simp only [eq_intCast]
        field_simp
        ring
  have hbig : PowerSeries.coeff K (G ^ (2 * K)) =
      PowerSeries.coeff K (Ex (K + 1) (PowerSeries.expand p hp0 A') * Ex (K + 1) B) := by
    have hK1 : 1 ≤ K := by
      rw [hK]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp0 (by omega))
    obtain ⟨m, hm⟩ : ∃ m, 2 * K = m + 1 := ⟨2 * K - 1, by omega⟩
    have hode := Ex_ode K _ B hA0 hB0
    rw [hthAB] at hode
    refine uniq (B := PowerSeries.C ((2 * K : ℕ) : ℚ) * Cq) ?_ ?_ ?_ hode K (by omega)
    · rw [PowerSeries.coeff_C_mul, Cq, PowerSeries.coeff_map, Cz, PowerSeries.coeff_mk, cc_zero]; simp
    · rw [coeff_zero_Gpow, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
        coeff_zero_Ex K _ hA0, coeff_zero_Ex K B hB0, mul_one]
    · rw [hm, th_Gpow, ← hm, sub_self]; exact dvd_zero _
  rw [hbig, Ex_expand, hK, coeff_expand_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hsmall i (by
    rw [Finset.mem_range] at hi
    have : M ≤ p * M := Nat.le_mul_of_pos_left M hp.pos
    omega)]

end A351857P
/-! p-adic bounds -/

namespace A351857P
open LtsJacobsthal

variable {p : ℕ} [hp : Fact p.Prime]

lemma D_coeff_Ls (n : ℕ) : D p 0 (PowerSeries.coeff n (Ls p)) := by
  rw [Ls, PowerSeries.coeff_mk]
  split_ifs with h
  · exact D.zero 0
  · rw [div_eq_mul_inv]; exact (D.int _).mul0 (D.inv h)

lemma D_coeff_Ls_pow (k n : ℕ) : D p 0 (PowerSeries.coeff n (Ls p ^ k)) := by
  induction k generalizing n with
  | zero =>
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact D.one
    · exact D.zero 0
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    exact D.sum _ _ fun x _ => (ih x.1).mul0 (D_coeff_Ls x.2)

lemma coeff_Ls_mul_p (t : ℕ) : PowerSeries.coeff (p * t) (Ls p) = 0 := by
  rw [Ls, PowerSeries.coeff_mk, if_pos (dvd_mul_right p t)]

lemma D_int_coeff (m i : ℕ) : D p 0 (PowerSeries.coeff i (G ^ m)) := by
  have : PowerSeries.coeff i (G ^ m) = ((PowerSeries.coeff i (g ^ m) : ℤ) : ℚ) := by
    rw [G, ← map_pow, PowerSeries.coeff_map]; rfl
  rw [this]; exact D.int _

lemma D_int_coeff' (m i : ℕ) : D p 0 (PowerSeries.coeff i (G ^ m * Cq)) := by
  have : PowerSeries.coeff i (G ^ m * Cq) = ((PowerSeries.coeff i (g ^ m * Cz) : ℤ) : ℚ) := by
    rw [G, Cq, ← map_pow, ← map_mul, PowerSeries.coeff_map]; rfl
  rw [this]; exact D.int _

/-- `i b_i` is divisible by `p^mu` when `p^mu ∣ M`. -/
lemma D_ib {μ M : ℕ} (hM : p ^ μ ∣ M) (hM1 : 1 ≤ M) (i : ℕ) :
    D p μ ((i : ℚ) * PowerSeries.coeff i (G ^ (2 * M))) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * M = m + 1 := ⟨2 * M - 1, by omega⟩
  have h := congrArg (PowerSeries.coeff i) (th_Gpow m)
  rw [coeff_th, ← hm] at h
  rw [h, show G ^ (2 * M) * (PowerSeries.C ((2 * M : ℕ) : ℚ) * Cq) =
    PowerSeries.C ((2 * M : ℕ) : ℚ) * (G ^ (2 * M) * Cq) by ring, PowerSeries.coeff_C_mul]
  obtain ⟨M', rfl⟩ := hM
  have e : (((2 * (p ^ μ * M') : ℕ)) : ℚ) = (p : ℚ) ^ μ * ((2 * M' : ℕ) : ℚ) := by
    push_cast; ring
  rw [e, mul_assoc]
  exact (D.ppow μ).mul0 ((D.nat _).mul0 (D_int_coeff' _ _))

lemma D_b {μ M s i' : ℕ} (hM : p ^ μ ∣ M) (hM1 : 1 ≤ M) (hs : s ≤ μ) (hi' : ¬ p ∣ i') :
    D p (μ - s) (PowerSeries.coeff (p ^ s * i') (G ^ (2 * M))) := by
  have h := D_ib hM hM1 (p ^ s * i')
  apply D.ucancel hi'
  apply D.cancel (c := s)
  rw [show μ - s + s = μ by omega]
  have e : (((p ^ s * i' : ℕ)) : ℚ) * PowerSeries.coeff (p ^ s * i') (G ^ (2 * M)) =
      (p : ℚ) ^ s * ((i' : ℚ) * PowerSeries.coeff (p ^ s * i') (G ^ (2 * M))) := by
    push_cast; ring
  rw [← e]; exact h

/-! the factorial bound -/

lemma D_fact {μ k c : ℕ} (h5 : 5 ≤ p) (hk : 3 ≤ k) :
    D p (3 * (μ + 1)) (((p : ℚ) ^ (μ + 1) * (c : ℚ)) ^ k * ((k.factorial : ℚ))⁻¹) := by
  obtain ⟨v, w, hw, hfw⟩ := Nat.exists_eq_pow_mul_and_not_dvd k.factorial_ne_zero p
    (hp.out.one_lt.ne')
  have hv : v ≤ k - 3 := by
    have h1 : p ^ v ∣ k.factorial := ⟨w, hfw⟩
    have h2 : v ≤ k.factorial.factorization p :=
      (hp.out.pow_dvd_iff_le_factorization k.factorial_ne_zero).mp h1
    have h3 := Nat.factorization_factorial_le_div_pred hp.out k
    have h4 : k / (p - 1) ≤ k / 4 := Nat.div_le_div_left (by omega) (by norm_num)
    have h5' : k / 4 ≤ k - 3 := by omega
    omega
  have hle : v + 3 * (μ + 1) ≤ (μ + 1) * k := by
    have : (k - 3) ≤ (k - 3) * (μ + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have e : (μ + 1) * k = (k - 3) * (μ + 1) + 3 * (μ + 1) := by
      rw [Nat.sub_mul]; have : 3 * (μ + 1) ≤ k * (μ + 1) := Nat.mul_le_mul_right _ hk
      rw [mul_comm (μ + 1) k]; omega
    omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
  refine ⟨((p : ℤ) ^ r * (c : ℤ) ^ k), w, hw, ?_⟩
  have hw0 : (w : ℚ) ≠ 0 := by
    intro h0; apply hw; have : w = 0 := by exact_mod_cast h0
    rw [this]; exact dvd_zero p
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hf : (k.factorial : ℚ) = (p : ℚ) ^ v * (w : ℚ) := by rw [hfw]; push_cast; ring
  rw [hf, mul_pow, ← pow_mul, hr]
  push_cast
  rw [pow_add, pow_add]
  field_simp

/-! the quadratic coefficient -/

lemma cc_refl {T u : ℕ} (hu0 : 0 < u) (huT : u < T) :
    (cc u : ℚ) * (cc (T - u) : ℚ) =
      4 + (-1) ^ T + 2 * (1 + (-1) ^ T) * (-1) ^ u := by
  unfold cc
  rw [if_neg (by omega), if_neg (by omega)]
  have e : ((-1 : ℤ)) ^ T = (-1) ^ (T - u) * (-1) ^ u := by
    rw [← pow_add, Nat.sub_add_cancel huT.le]
  have e2 : ((-1 : ℤ) ^ u) * (-1) ^ u = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have e3 : ((-1 : ℤ)) ^ (T - u) = (-1) ^ T * (-1) ^ u := by
    rw [e, mul_assoc, e2, mul_one]
  push_cast
  have e3' : ((-1 : ℚ)) ^ (T - u) = (-1) ^ T * (-1) ^ u := by exact_mod_cast e3
  have e2' : ((-1 : ℚ) ^ u) * (-1) ^ u = 1 := by exact_mod_cast e2
  rw [e3']
  linear_combination (2 * (-1) ^ T) * e2' - (2 * (-1) ^ T) * e2' + ((-1 : ℚ) ^ T) * e2'

end A351857P
/-! the quadratic coefficient q_t -/

namespace A351857P
open LtsJacobsthal

variable {p : ℕ} [hp : Fact p.Prime]

lemma alt_sum (h5 : 5 ≤ p) (Q : ℕ) :
    ∑ u ∈ U p (2 * Q), ((-1 : ℚ)) ^ u / (u : ℚ) = sg p Q 1 - sg p (2 * Q) 1 := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have h1 : ∀ u ∈ U p (2 * Q), ((-1 : ℚ)) ^ u / (u : ℚ) =
      2 * (if Even u then (u : ℚ)⁻¹ else 0) - ((u : ℚ)⁻¹) ^ 1 := by
    intro u _
    rcases Nat.even_or_odd u with he | ho
    · rw [he.neg_one_pow, if_pos he]; ring
    · rw [ho.neg_one_pow, if_neg (Nat.not_even_iff_odd.mpr ho)]; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
  have himg : (U p (2 * Q)).filter (fun u => Even u) = (U p Q).image (fun w => 2 * w) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_image, mem_U]
    constructor
    · rintro ⟨⟨hlt, hnd⟩, ⟨w, hw⟩⟩
      refine ⟨w, ⟨by omega, ?_⟩, by omega⟩
      intro hd; apply hnd; rw [hw]; exact Dvd.dvd.add hd hd
    · rintro ⟨w, ⟨hlt, hnd⟩, rfl⟩
      refine ⟨⟨by omega, ?_⟩, ⟨w, by ring⟩⟩
      intro hd
      rcases (Nat.Prime.dvd_mul hp.out).mp hd with h | h
      · exact hp2 h
      · exact hnd h
  have hinj : Set.InjOn (fun w => 2 * w) (U p Q : Set ℕ) := by
    intro a _ b _ h; simp only at h; omega
  rw [himg, Finset.sum_image hinj]
  unfold sg
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  push_cast
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp
  · have : (w : ℚ) ≠ 0 := by exact_mod_cast hw.ne'
    field_simp

lemma coeff_Ls_sq (T : ℕ) (hT : p ∣ T) :
    PowerSeries.coeff T (Ls p ^ 2) =
      ∑ u ∈ U p T, ((cc u : ℚ) / (u : ℚ)) * ((cc (T - u) : ℚ) / ((T - u : ℕ) : ℚ)) := by
  rw [sq, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hsub : U p T ⊆ Finset.range (T + 1) := by
    intro u hu; rw [mem_U] at hu; rw [Finset.mem_range]; omega
  symm
  apply Finset.sum_subset_zero_on_sdiff hsub
  · intro u hu
    rw [Finset.mem_sdiff, Finset.mem_range, mem_U] at hu
    simp only [Ls, PowerSeries.coeff_mk]
    by_cases hpu : p ∣ u
    · rw [if_pos hpu, zero_mul]
    · have huT : u = T := by
        by_contra hne; exact hu.2 ⟨by omega, hpu⟩
      rw [huT, if_pos hT, zero_mul]
  · intro u hu
    rw [mem_U] at hu
    have h2 : ¬ p ∣ T - u := by
      intro hd
      apply hu.2
      have : T - u + u = T := Nat.sub_add_cancel hu.1.le
      have h3 : p ∣ T - u + u := by rw [this]; exact hT
      exact (Nat.dvd_add_right hd).mp h3
    simp only [Ls, PowerSeries.coeff_mk]
    rw [if_neg hu.2, if_neg h2]

lemma D_q (h5 : 5 ≤ p) (s t' : ℕ) (ht' : ¬ p ∣ t') :
    D p (s + 1) (PowerSeries.coeff (p * (p ^ s * t')) (Ls p ^ 2)) := by
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  set T := p * (p ^ s * t') with hT
  have hT' : T = t' * p ^ (s + 1) := by rw [hT]; ring
  have hpT : p ∣ T := dvd_mul_right p _
  have ht'0 : t' ≠ 0 := by rintro rfl; exact ht' (dvd_zero p)
  have hT0 : (T : ℚ) ≠ 0 := by
    rw [hT']; push_cast
    exact mul_ne_zero (by exact_mod_cast ht'0) (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))
  set τ : ℚ := (-1) ^ T with hτ
  -- the sum Y
  set Y : ℚ := (4 + τ) * sg p T 1 + 2 * (1 + τ) * ∑ u ∈ U p T, ((-1 : ℚ)) ^ u / (u : ℚ) with hY
  have hq : PowerSeries.coeff T (Ls p ^ 2) = (2 / (T : ℚ)) * Y := by
    rw [coeff_Ls_sq T hpT]
    have hpt : ∀ u ∈ U p T, ((cc u : ℚ) / (u : ℚ)) * ((cc (T - u) : ℚ) / ((T - u : ℕ) : ℚ)) =
        (1 / (T : ℚ)) * ((cc u : ℚ) * (cc (T - u) : ℚ) / (u : ℚ) +
          (cc u : ℚ) * (cc (T - u) : ℚ) / ((T - u : ℕ) : ℚ)) := by
      intro u hu
      rw [mem_U] at hu
      have hu0 : u ≠ 0 := by rintro rfl; exact hu.2 (dvd_zero p)
      have hu0' : (u : ℚ) ≠ 0 := by exact_mod_cast hu0
      have hTu : ((T - u : ℕ) : ℚ) = (T : ℚ) - (u : ℚ) := by rw [Nat.cast_sub hu.1.le]
      have hTu0 : ((T - u : ℕ) : ℚ) ≠ 0 := by
        have : T - u ≠ 0 := by omega
        exact_mod_cast this
      rw [hTu] at hTu0 ⊢
      field_simp
      ring
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, Finset.sum_add_distrib]
    have hrefl := sum_U_reflect hpT (fun u => (cc u : ℚ) * (cc (T - u) : ℚ) / ((T - u : ℕ) : ℚ))
    rw [hrefl]
    have hpt2 : ∀ u ∈ U p T, (cc (T - u) : ℚ) * (cc (T - (T - u)) : ℚ) / ((T - (T - u) : ℕ) : ℚ) =
        (cc u : ℚ) * (cc (T - u) : ℚ) / (u : ℚ) := by
      intro u hu
      rw [mem_U] at hu
      rw [show T - (T - u) = u by omega]; ring
    rw [Finset.sum_congr rfl hpt2]
    have hpt3 : ∀ u ∈ U p T, (cc u : ℚ) * (cc (T - u) : ℚ) / (u : ℚ) =
        (4 + τ) * ((u : ℚ)⁻¹) ^ 1 + 2 * (1 + τ) * (((-1 : ℚ)) ^ u / (u : ℚ)) := by
      intro u hu
      rw [mem_U] at hu
      have hu0 : 0 < u := by
        rcases Nat.eq_zero_or_pos u with h | h
        · exact absurd (h ▸ dvd_zero p) hu.2
        · exact h
      rw [cc_refl hu0 hu.1]
      ring
    rw [Finset.sum_congr rfl hpt3, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hY]
    unfold sg
    ring
  -- D bound for Y
  have hS : D p (2 * (s + 1)) (sg p T 1) := by
    rw [hT']; exact S1_D h5 (by omega) t'
  have hYD : D p (2 * (s + 1)) Y := by
    rcases Nat.even_or_odd T with he | ho
    · have hτ1 : τ = 1 := by rw [hτ]; exact he.neg_one_pow
      obtain ⟨t'', ht''⟩ : 2 ∣ t' := by
        have h2T : 2 ∣ t' * p ^ (s + 1) := hT' ▸ (even_iff_two_dvd.mp he)
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2T with h | h
        · exact h
        · exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)) (fun h' => by
            have : 2 ∣ p := h'
            have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp this
            omega)
      have hT2 : T = 2 * (t'' * p ^ (s + 1)) := by rw [hT', ht'']; ring
      have halt := alt_sum h5 (t'' * p ^ (s + 1))
      rw [← hT2] at halt
      rw [hY, halt, hτ1]
      have hS2 : D p (2 * (s + 1)) (sg p (t'' * p ^ (s + 1)) 1) := S1_D h5 (by omega) t''
      have e : (4 + 1 : ℚ) * sg p T 1 + 2 * (1 + 1) * (sg p (t'' * p ^ (s + 1)) 1 - sg p T 1) =
          sg p T 1 + 4 * sg p (t'' * p ^ (s + 1)) 1 := by ring
      rw [e]
      exact hS.add (D.mul0' (by simpa using D.nat (p := p) 4) hS2)
    · have hτ1 : τ = -1 := by rw [hτ]; exact ho.neg_one_pow
      rw [hY, hτ1]
      have e : (4 + -1 : ℚ) * sg p T 1 + 2 * (1 + -1) * ∑ u ∈ U p T, ((-1 : ℚ)) ^ u / (u : ℚ) =
          3 * sg p T 1 := by ring
      rw [e]
      exact D.mul0' D.three hS
  -- divide by T
  rw [hq]
  apply D.ucancel ht'
  apply D.cancel (c := s + 1)
  rw [show s + 1 + (s + 1) = 2 * (s + 1) by ring]
  have e : (p : ℚ) ^ (s + 1) * ((t' : ℚ) * ((2 / (T : ℚ)) * Y)) = 2 * Y := by
    have : (T : ℚ) = (t' : ℚ) * (p : ℚ) ^ (s + 1) := by rw [hT']; push_cast; ring
    rw [this] at hT0 ⊢
    field_simp
  rw [e]
  exact D.mul0' D.two hYD

end A351857P
/-! assembly -/

namespace A351857P
open LtsJacobsthal

variable {p : ℕ} [hp : Fact p.Prime]

lemma D_e (h5 : 5 ≤ p) (K μ M' s t' : ℕ) (ht' : ¬ p ∣ t') :
    D p (2 * μ + 3 + min s μ) (PowerSeries.coeff (p * (p ^ s * t'))
      (Ex K (PowerSeries.C ((2 * (p * (p ^ μ * M')) : ℕ) : ℚ) * Ls p))) := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have ht'0 : t' ≠ 0 := by rintro rfl; exact ht' (dvd_zero p)
  have hpt0 : p * (p ^ s * t') ≠ 0 := Nat.mul_ne_zero hp0 (Nat.mul_ne_zero (pow_ne_zero _ hp0) ht'0)
  unfold Ex
  rw [map_sum]
  apply D.sum
  intro k _
  rw [PowerSeries.coeff_C_mul, mul_pow, ← map_pow, PowerSeries.coeff_C_mul]
  have hc : (((2 * (p * (p ^ μ * M')) : ℕ)) : ℚ) = (p : ℚ) ^ (μ + 1) * ((2 * M' : ℕ) : ℚ) := by
    push_cast; ring
  rw [hc]
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k
    · simp only [pow_zero]; rw [PowerSeries.coeff_one, if_neg hpt0]; simpa using D.zero (p := p) _
    · simp only [pow_one]; rw [coeff_Ls_mul_p]; simpa using D.zero (p := p) _
    · have hq := D_q h5 s t' ht'
      have e : ((Nat.factorial 2 : ℕ) : ℚ)⁻¹ * (((p : ℚ) ^ (μ + 1) * ((2 * M' : ℕ) : ℚ)) ^ 2 *
          PowerSeries.coeff (p * (p ^ s * t')) (Ls p ^ 2)) =
          ((p : ℚ) ^ (2 * μ + 2) * ((2 * M' * M' : ℕ) : ℚ)) *
            PowerSeries.coeff (p * (p ^ s * t')) (Ls p ^ 2) := by
        simp only [Nat.factorial]; push_cast; ring
      rw [e]
      exact (((D.ppow (2 * μ + 2)).mul0 (D.nat _)).mul hq).le (by omega)
  · have hf := D_fact (μ := μ) (c := 2 * M') h5 hk
    have e : ((k.factorial : ℕ) : ℚ)⁻¹ * (((p : ℚ) ^ (μ + 1) * ((2 * M' : ℕ) : ℚ)) ^ k *
        PowerSeries.coeff (p * (p ^ s * t')) (Ls p ^ k)) =
        (((p : ℚ) ^ (μ + 1) * ((2 * M' : ℕ) : ℚ)) ^ k * ((k.factorial : ℚ))⁻¹) *
          PowerSeries.coeff (p * (p ^ s * t')) (Ls p ^ k) := by ring
    rw [e]
    exact (hf.mul0 (D_coeff_Ls_pow k _)).le (by omega)

lemma key (h5 : 5 ≤ p) (μ M' : ℕ) (hM' : 1 ≤ M') :
    D p (3 * μ + 3) (PowerSeries.coeff (p * (p ^ μ * M')) (G ^ (2 * (p * (p ^ μ * M')))) -
      PowerSeries.coeff (p ^ μ * M') (G ^ (2 * (p ^ μ * M')))) := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  set M := p ^ μ * M' with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero _ hp0) (by omega))
  rw [main_identity hp.out hodd M hM1, Finset.sum_range_succ, Nat.sub_self, Nat.mul_zero]
  have hB0 : PowerSeries.coeff 0 (PowerSeries.C ((2 * (p * M) : ℕ) : ℚ) * Ls p) = 0 := by
    rw [PowerSeries.coeff_C_mul, Ls, PowerSeries.coeff_mk]; simp
  rw [coeff_zero_Ex _ _ hB0, mul_one, add_sub_cancel_right]
  apply D.sum
  intro i hi
  rw [Finset.mem_range] at hi
  have ht0 : M - i ≠ 0 := by omega
  obtain ⟨s, t', ht', hst⟩ := Nat.exists_eq_pow_mul_and_not_dvd ht0 p hp.out.one_lt.ne'
  rw [hst]
  have he := D_e h5 (p * M + 1) μ M' s t' ht'
  rw [← hMdef] at he
  by_cases hs : μ ≤ s
  · rw [min_eq_right hs] at he
    exact D.mul0' (D_int_coeff _ _) (he.le (by omega))
  · replace hs : s < μ := Nat.lt_of_not_le hs
    rw [min_eq_left hs.le] at he
    have hMs : M = p ^ s * (p ^ (μ - s) * M') := by
      rw [hMdef, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hs.le]
    have hle : t' ≤ p ^ (μ - s) * M' := by
      have h1 : p ^ s * t' ≤ p ^ s * (p ^ (μ - s) * M') := by rw [← hst, ← hMs]; omega
      exact Nat.le_of_mul_le_mul_left h1 (pow_pos hp.out.pos s)
    have hi' : i = p ^ s * (p ^ (μ - s) * M' - t') := by
      rw [Nat.mul_sub, ← hMs, ← hst]; omega
    have hnd : ¬ p ∣ (p ^ (μ - s) * M' - t') := by
      intro hd
      apply ht'
      have h1 : p ∣ p ^ (μ - s) * M' :=
        Dvd.dvd.mul_right (dvd_pow_self p (by omega)) M'
      have h2 : p ^ (μ - s) * M' - t' + t' = p ^ (μ - s) * M' := Nat.sub_add_cancel hle
      rw [← h2] at h1
      exact (Nat.dvd_add_right hd).mp h1
    have hb := D_b (p := p) (μ := μ) (M := M) (by rw [hMdef]; exact dvd_mul_right _ _) hM1
      hs.le hnd
    rw [← hi'] at hb
    exact (hb.mul he).le (by omega)

theorem final {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ((q : ℤ) ^ (3 * k)) ∣
      (PowerSeries.coeff (n * q ^ k) (g ^ (2 * (n * q ^ k))) -
        PowerSeries.coeff (n * q ^ (k - 1)) (g ^ (2 * (n * q ^ (k - 1))))) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have h := key (p := q) h5 j n hn
  have e1 : n * q ^ (j + 1) = q * (q ^ j * n) := by ring
  have e2 : n * q ^ j = q ^ j * n := by ring
  rw [e1, e2, show 3 * (j + 1) = 3 * j + 3 by ring]
  apply D.dvd
  have hc : ∀ i m : ℕ, PowerSeries.coeff i (G ^ m) = ((PowerSeries.coeff i (g ^ m) : ℤ) : ℚ) := by
    intro i m
    rw [G, ← map_pow, PowerSeries.coeff_map]; rfl
  push_cast
  rw [← hc, ← hc]
  exact h

end A351857P

theorem OMA.solution : type_of% @OMA.S_oeis_a351857.main := by
  intro p n k hp h5 hn hk
  exact A351857P.final hp h5 n k hn hk
