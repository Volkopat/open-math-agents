import OMAReductions.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R1
/-!
# Proof of `Erdos940.erdos_940.variants.three_powerful.R1.H2.R1.H1`

Lower bound `(n : ℝ)^(49/100) ≤ (S n).card` for sufficiently large `n ≡ 7 (mod 8)`
via Estermann-Siegel's lower bound on `L(1, χ)`, Dirichlet's class number lower bound,
Gauss's ternary quadratic form genus lower bound, and Hurwitz quaternion lifting.
-/

section ModQuaternionLift

open Finset BigOperators

namespace E940.QuaternionLift

/-!
### Hurwitz Quaternions and the Elementary Lift `r₃(d * s²) ≥ r₃(d) * φ(s)`
-/

structure HQ where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  par : (a - b) % 2 = 0 ∧ (a - c) % 2 = 0 ∧ (a - d) % 2 = 0

namespace HQ

lemma ext {p q : HQ} (ha : p.a = q.a) (hb : p.b = q.b) (hc : p.c = q.c) (hd : p.d = q.d) :
    p = q := by
  cases p; cases q; dsimp at ha hb hc hd; subst ha hb hc hd; rfl

instance : DecidableEq HQ := fun p q =>
  if h : p.a = q.a ∧ p.b = q.b ∧ p.c = q.c ∧ p.d = q.d then
    isTrue (HQ.ext h.1 h.2.1 h.2.2.1 h.2.2.2)
  else
    isFalse fun heq => h ⟨congrArg HQ.a heq, congrArg HQ.b heq, congrArg HQ.c heq, congrArg HQ.d heq⟩

lemma mul_par_aux (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ)
    (h₁ : (a₁ - b₁) % 2 = 0 ∧ (a₁ - c₁) % 2 = 0 ∧ (a₁ - d₁) % 2 = 0)
    (h₂ : (a₂ - b₂) % 2 = 0 ∧ (a₂ - c₂) % 2 = 0 ∧ (a₂ - d₂) % 2 = 0) :
    let x := (a₁ * a₂ - b₁ * b₂ - c₁ * c₂ - d₁ * d₂) / 2
    let y := (a₁ * b₂ + b₁ * a₂ + c₁ * d₂ - d₁ * c₂) / 2
    let z := (a₁ * c₂ - b₁ * d₂ + c₁ * a₂ + d₁ * b₂) / 2
    let w := (a₁ * d₂ + b₁ * c₂ - c₁ * b₂ + d₁ * a₂) / 2
    2 * x = a₁ * a₂ - b₁ * b₂ - c₁ * c₂ - d₁ * d₂ ∧
    2 * y = a₁ * b₂ + b₁ * a₂ + c₁ * d₂ - d₁ * c₂ ∧
    2 * z = a₁ * c₂ - b₁ * d₂ + c₁ * a₂ + d₁ * b₂ ∧
    2 * w = a₁ * d₂ + b₁ * c₂ - c₁ * b₂ + d₁ * a₂ ∧
    (x - y) % 2 = 0 ∧ (x - z) % 2 = 0 ∧ (x - w) % 2 = 0 := by
  set r₁ := (b₁ - a₁) / 2
  set r₂ := (c₁ - a₁) / 2
  set r₃ := (d₁ - a₁) / 2
  set s₁ := (b₂ - a₂) / 2
  set s₂ := (c₂ - a₂) / 2
  set s₃ := (d₂ - a₂) / 2
  have hb₁ : b₁ = a₁ + 2 * r₁ := by omega
  have hc₁ : c₁ = a₁ + 2 * r₂ := by omega
  have hd₁ : d₁ = a₁ + 2 * r₃ := by omega
  have hb₂ : b₂ = a₂ + 2 * s₁ := by omega
  have hc₂ : c₂ = a₂ + 2 * s₂ := by omega
  have hd₂ : d₂ = a₂ + 2 * s₃ := by omega
  have e1 : a₁ * a₂ - b₁ * b₂ - c₁ * c₂ - d₁ * d₂ =
      2 * (-(a₁ * a₂) - a₁ * (s₁ + s₂ + s₃) - a₂ * (r₁ + r₂ + r₃) - 2 * (r₁ * s₁ + r₂ * s₂ + r₃ * s₃)) := by
    rw [hb₁, hc₁, hd₁, hb₂, hc₂, hd₂]; ring
  have e2 : a₁ * b₂ + b₁ * a₂ + c₁ * d₂ - d₁ * c₂ =
      2 * (a₁ * a₂ + a₁ * (s₁ + s₃ - s₂) + a₂ * (r₁ + r₂ - r₃) + 2 * (r₂ * s₃ - r₃ * s₂)) := by
    rw [hb₁, hc₁, hd₁, hb₂, hc₂, hd₂]; ring
  have e3 : a₁ * c₂ - b₁ * d₂ + c₁ * a₂ + d₁ * b₂ =
      2 * (a₁ * a₂ + a₁ * (s₂ + s₁ - s₃) + a₂ * (r₂ + r₃ - r₁) + 2 * (r₃ * s₁ - r₁ * s₃)) := by
    rw [hb₁, hc₁, hd₁, hb₂, hc₂, hd₂]; ring
  have e4 : a₁ * d₂ + b₁ * c₂ - c₁ * b₂ + d₁ * a₂ =
      2 * (a₁ * a₂ + a₁ * (s₃ + s₂ - s₁) + a₂ * (r₃ + r₁ - r₂) + 2 * (r₁ * s₂ - r₂ * s₁)) := by
    rw [hb₁, hc₁, hd₁, hb₂, hc₂, hd₂]; ring
  dsimp only
  rw [e1, e2, e3, e4]
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · rw [Int.mul_ediv_cancel_left _ (by decide), Int.mul_ediv_cancel_left _ (by decide)]
    have hsub : -(a₁ * a₂) - a₁ * (s₁ + s₂ + s₃) - a₂ * (r₁ + r₂ + r₃) - 2 * (r₁ * s₁ + r₂ * s₂ + r₃ * s₃) -
        (a₁ * a₂ + a₁ * (s₁ + s₃ - s₂) + a₂ * (r₁ + r₂ - r₃) + 2 * (r₂ * s₃ - r₃ * s₂)) =
        2 * (-(a₁ * a₂) - a₁ * (s₁ + s₃) - a₂ * (r₁ + r₂) - (r₁ * s₁ + r₂ * s₂ + r₃ * s₃ + r₂ * s₃ - r₃ * s₂)) := by ring
    rw [hsub]; omega
  · rw [Int.mul_ediv_cancel_left _ (by decide), Int.mul_ediv_cancel_left _ (by decide)]
    have hsub : -(a₁ * a₂) - a₁ * (s₁ + s₂ + s₃) - a₂ * (r₁ + r₂ + r₃) - 2 * (r₁ * s₁ + r₂ * s₂ + r₃ * s₃) -
        (a₁ * a₂ + a₁ * (s₂ + s₁ - s₃) + a₂ * (r₂ + r₃ - r₁) + 2 * (r₃ * s₁ - r₁ * s₃)) =
        2 * (-(a₁ * a₂) - a₁ * (s₁ + s₂) - a₂ * (r₂ + r₃) - (r₁ * s₁ + r₂ * s₂ + r₃ * s₃ + r₃ * s₁ - r₁ * s₃)) := by ring
    rw [hsub]; omega
  · rw [Int.mul_ediv_cancel_left _ (by decide), Int.mul_ediv_cancel_left _ (by decide)]
    have hsub : -(a₁ * a₂) - a₁ * (s₁ + s₂ + s₃) - a₂ * (r₁ + r₂ + r₃) - 2 * (r₁ * s₁ + r₂ * s₂ + r₃ * s₃) -
        (a₁ * a₂ + a₁ * (s₃ + s₂ - s₁) + a₂ * (r₃ + r₁ - r₂) + 2 * (r₁ * s₂ - r₂ * s₁)) =
        2 * (-(a₁ * a₂) - a₁ * (s₂ + s₃) - a₂ * (r₁ + r₃) - (r₁ * s₁ + r₂ * s₂ + r₃ * s₃ + r₁ * s₂ - r₂ * s₁)) := by ring
    rw [hsub]; omega

def zero : HQ := ⟨0, 0, 0, 0, by omega⟩
def one : HQ := ⟨2, 0, 0, 0, by omega⟩
def neg (q : HQ) : HQ := ⟨-q.a, -q.b, -q.c, -q.d, by have := q.par; omega⟩
def add (p q : HQ) : HQ := ⟨p.a + q.a, p.b + q.b, p.c + q.c, p.d + q.d, by have := p.par; have := q.par; omega⟩
def sub (p q : HQ) : HQ := ⟨p.a - q.a, p.b - q.b, p.c - q.c, p.d - q.d, by have := p.par; have := q.par; omega⟩
def mul (p q : HQ) : HQ :=
  ⟨(p.a * q.a - p.b * q.b - p.c * q.c - p.d * q.d) / 2,
   (p.a * q.b + p.b * q.a + p.c * q.d - p.d * q.c) / 2,
   (p.a * q.c - p.b * q.d + p.c * q.a + p.d * q.b) / 2,
   (p.a * q.d + p.b * q.c - p.c * q.b + p.d * q.a) / 2,
   let h := mul_par_aux p.a p.b p.c p.d q.a q.b q.c q.d p.par q.par
   ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩⟩
def conj (q : HQ) : HQ := ⟨q.a, -q.b, -q.c, -q.d, by have := q.par; omega⟩
def ofInt (n : ℤ) : HQ := ⟨2 * n, 0, 0, 0, by omega⟩
def ofVec (x y z : ℤ) : HQ := ⟨0, 2 * x, 2 * y, 2 * z, by omega⟩

instance : Zero HQ := ⟨zero⟩
instance : One HQ := ⟨one⟩
instance : Neg HQ := ⟨neg⟩
instance : Add HQ := ⟨add⟩
instance : Sub HQ := ⟨sub⟩
instance : Mul HQ := ⟨mul⟩

@[simp] lemma zero_a : (0 : HQ).a = 0 := rfl
@[simp] lemma zero_b : (0 : HQ).b = 0 := rfl
@[simp] lemma zero_c : (0 : HQ).c = 0 := rfl
@[simp] lemma zero_d : (0 : HQ).d = 0 := rfl
@[simp] lemma one_a : (1 : HQ).a = 2 := rfl
@[simp] lemma one_b : (1 : HQ).b = 0 := rfl
@[simp] lemma one_c : (1 : HQ).c = 0 := rfl
@[simp] lemma one_d : (1 : HQ).d = 0 := rfl
@[simp] lemma add_a (p q : HQ) : (p + q).a = p.a + q.a := rfl
@[simp] lemma add_b (p q : HQ) : (p + q).b = p.b + q.b := rfl
@[simp] lemma add_c (p q : HQ) : (p + q).c = p.c + q.c := rfl
@[simp] lemma add_d (p q : HQ) : (p + q).d = p.d + q.d := rfl
@[simp] lemma sub_a (p q : HQ) : (p - q).a = p.a - q.a := rfl
@[simp] lemma sub_b (p q : HQ) : (p - q).b = p.b - q.b := rfl
@[simp] lemma sub_c (p q : HQ) : (p - q).c = p.c - q.c := rfl
@[simp] lemma sub_d (p q : HQ) : (p - q).d = p.d - q.d := rfl
@[simp] lemma neg_a (q : HQ) : (-q).a = -q.a := rfl
@[simp] lemma neg_b (q : HQ) : (-q).b = -q.b := rfl
@[simp] lemma neg_c (q : HQ) : (-q).c = -q.c := rfl
@[simp] lemma neg_d (q : HQ) : (-q).d = -q.d := rfl
@[simp] lemma conj_a (q : HQ) : (conj q).a = q.a := rfl
@[simp] lemma conj_b (q : HQ) : (conj q).b = -q.b := rfl
@[simp] lemma conj_c (q : HQ) : (conj q).c = -q.c := rfl
@[simp] lemma conj_d (q : HQ) : (conj q).d = -q.d := rfl
@[simp] lemma ofInt_a (n : ℤ) : (ofInt n).a = 2 * n := rfl
@[simp] lemma ofInt_b (n : ℤ) : (ofInt n).b = 0 := rfl
@[simp] lemma ofInt_c (n : ℤ) : (ofInt n).c = 0 := rfl
@[simp] lemma ofInt_d (n : ℤ) : (ofInt n).d = 0 := rfl

lemma two_mul_a (p q : HQ) : 2 * (p * q).a = p.a * q.a - p.b * q.b - p.c * q.c - p.d * q.d :=
  (mul_par_aux p.a p.b p.c p.d q.a q.b q.c q.d p.par q.par).1
lemma two_mul_b (p q : HQ) : 2 * (p * q).b = p.a * q.b + p.b * q.a + p.c * q.d - p.d * q.c :=
  (mul_par_aux p.a p.b p.c p.d q.a q.b q.c q.d p.par q.par).2.1
lemma two_mul_c (p q : HQ) : 2 * (p * q).c = p.a * q.c - p.b * q.d + p.c * q.a + p.d * q.b :=
  (mul_par_aux p.a p.b p.c p.d q.a q.b q.c q.d p.par q.par).2.2.1
lemma two_mul_d (p q : HQ) : 2 * (p * q).d = p.a * q.d + p.b * q.c - p.c * q.b + p.d * q.a :=
  (mul_par_aux p.a p.b p.c p.d q.a q.b q.c q.d p.par q.par).2.2.2.1

lemma mul_assoc' (p q r : HQ) : (p * q) * r = p * (q * r) := by
  apply HQ.ext
  · linarith [show 4 * ((p * q) * r).a = 4 * (p * (q * r)).a by
      linear_combination 2 * (two_mul_a (p * q) r) - 2 * (two_mul_a p (q * r))
        + r.a * two_mul_a p q - r.b * two_mul_b p q - r.c * two_mul_c p q - r.d * two_mul_d p q
        - p.a * two_mul_a q r + p.b * two_mul_b q r + p.c * two_mul_c q r + p.d * two_mul_d q r]
  · linarith [show 4 * ((p * q) * r).b = 4 * (p * (q * r)).b by
      linear_combination 2 * (two_mul_b (p * q) r) - 2 * (two_mul_b p (q * r))
        + r.b * two_mul_a p q + r.a * two_mul_b p q + r.d * two_mul_c p q - r.c * two_mul_d p q
        - p.a * two_mul_b q r - p.b * two_mul_a q r - p.c * two_mul_d q r + p.d * two_mul_c q r]
  · linarith [show 4 * ((p * q) * r).c = 4 * (p * (q * r)).c by
      linear_combination 2 * (two_mul_c (p * q) r) - 2 * (two_mul_c p (q * r))
        + r.c * two_mul_a p q - r.d * two_mul_b p q + r.a * two_mul_c p q + r.b * two_mul_d p q
        - p.a * two_mul_c q r + p.b * two_mul_d q r - p.c * two_mul_a q r - p.d * two_mul_b q r]
  · linarith [show 4 * ((p * q) * r).d = 4 * (p * (q * r)).d by
      linear_combination 2 * (two_mul_d (p * q) r) - 2 * (two_mul_d p (q * r))
        + r.d * two_mul_a p q + r.c * two_mul_b p q - r.b * two_mul_c p q + r.a * two_mul_d p q
        - p.a * two_mul_d q r - p.b * two_mul_c q r + p.c * two_mul_b q r - p.d * two_mul_a q r]

instance : Ring HQ where
  add_assoc p q r := by apply HQ.ext <;> simp [add_assoc]
  zero_add q := by apply HQ.ext <;> simp
  add_zero q := by apply HQ.ext <;> simp
  nsmul := nsmulRec
  add_comm p q := by apply HQ.ext <;> simp [add_comm]
  zsmul := zsmulRec
  neg_add_cancel q := by apply HQ.ext <;> simp
  sub_eq_add_neg p q := by apply HQ.ext <;> simp [sub_eq_add_neg]
  mul_assoc := mul_assoc'
  one_mul q := by
    apply HQ.ext
    · have h := two_mul_a 1 q; simp at h; linarith
    · have h := two_mul_b 1 q; simp at h; linarith
    · have h := two_mul_c 1 q; simp at h; linarith
    · have h := two_mul_d 1 q; simp at h; linarith
  mul_one q := by
    apply HQ.ext
    · have h := two_mul_a q 1; simp at h; linarith
    · have h := two_mul_b q 1; simp at h; linarith
    · have h := two_mul_c q 1; simp at h; linarith
    · have h := two_mul_d q 1; simp at h; linarith
  left_distrib p q r := by
    apply HQ.ext
    · have h1 := two_mul_a p (q + r); have h2 := two_mul_a p q; have h3 := two_mul_a p r; simp at h1 ⊢; linarith
    · have h1 := two_mul_b p (q + r); have h2 := two_mul_b p q; have h3 := two_mul_b p r; simp at h1 ⊢; linarith
    · have h1 := two_mul_c p (q + r); have h2 := two_mul_c p q; have h3 := two_mul_c p r; simp at h1 ⊢; linarith
    · have h1 := two_mul_d p (q + r); have h2 := two_mul_d p q; have h3 := two_mul_d p r; simp at h1 ⊢; linarith
  right_distrib p q r := by
    apply HQ.ext
    · have h1 := two_mul_a (p + q) r; have h2 := two_mul_a p r; have h3 := two_mul_a q r; simp at h1 ⊢; linarith
    · have h1 := two_mul_b (p + q) r; have h2 := two_mul_b p r; have h3 := two_mul_b q r; simp at h1 ⊢; linarith
    · have h1 := two_mul_c (p + q) r; have h2 := two_mul_c p r; have h3 := two_mul_c q r; simp at h1 ⊢; linarith
    · have h1 := two_mul_d (p + q) r; have h2 := two_mul_d p r; have h3 := two_mul_d q r; simp at h1 ⊢; linarith
  zero_mul q := by
    apply HQ.ext
    · have h := two_mul_a 0 q; simp at h ⊢; linarith
    · have h := two_mul_b 0 q; simp at h ⊢; linarith
    · have h := two_mul_c 0 q; simp at h ⊢; linarith
    · have h := two_mul_d 0 q; simp at h ⊢; linarith
  mul_zero q := by
    apply HQ.ext
    · have h := two_mul_a q 0; simp at h ⊢; linarith
    · have h := two_mul_b q 0; simp at h ⊢; linarith
    · have h := two_mul_c q 0; simp at h ⊢; linarith
    · have h := two_mul_d q 0; simp at h ⊢; linarith

/-- Norm as an integer `N(q) = (a² + b² + c² + d²) / 4`. -/
def normZ (q : HQ) : ℤ := (q.a ^ 2 + q.b ^ 2 + q.c ^ 2 + q.d ^ 2) / 4

def norm (q : HQ) : ℕ := (normZ q).toNat

lemma four_mul_normZ (q : HQ) : 4 * normZ q = q.a ^ 2 + q.b ^ 2 + q.c ^ 2 + q.d ^ 2 := by
  have h := q.par
  dsimp only [normZ]
  have hdiv : (4 : ℤ) ∣ q.a ^ 2 + q.b ^ 2 + q.c ^ 2 + q.d ^ 2 := by
    refine ⟨q.a ^ 2 + q.a * ((q.b - q.a) / 2 + (q.c - q.a) / 2 + (q.d - q.a) / 2) +
      ((q.b - q.a) / 2) ^ 2 + ((q.c - q.a) / 2) ^ 2 + ((q.d - q.a) / 2) ^ 2, ?_⟩
    have hb : q.b = q.a + 2 * ((q.b - q.a) / 2) := by omega
    have hc : q.c = q.a + 2 * ((q.c - q.a) / 2) := by omega
    have hd : q.d = q.a + 2 * ((q.d - q.a) / 2) := by omega
    conv_lhs => rw [hb, hc, hd]
    ring
  exact Int.mul_ediv_cancel' hdiv

lemma normZ_nonneg (q : HQ) : 0 ≤ normZ q := by
  have h := four_mul_normZ q
  nlinarith [sq_nonneg q.a, sq_nonneg q.b, sq_nonneg q.c, sq_nonneg q.d]

lemma norm_coe (q : HQ) : (norm q : ℤ) = normZ q :=
  Int.toNat_of_nonneg (normZ_nonneg q)

lemma four_mul_norm (q : HQ) : 4 * (norm q : ℤ) = q.a ^ 2 + q.b ^ 2 + q.c ^ 2 + q.d ^ 2 := by
  rw [norm_coe, four_mul_normZ]

lemma norm_eq_zero_iff (q : HQ) : norm q = 0 ↔ q = 0 := by
  constructor
  · intro h
    have h4 := four_mul_norm q
    rw [h] at h4
    simp only [Nat.cast_zero, mul_zero] at h4
    apply HQ.ext <;> simp <;> nlinarith [sq_nonneg q.a, sq_nonneg q.b, sq_nonneg q.c, sq_nonneg q.d]
  · rintro rfl; simp [norm, normZ]

lemma norm_mul (p q : HQ) : norm (p * q) = norm p * norm q := by
  suffices h : 16 * (norm (p * q) : ℤ) = 16 * ((norm p * norm q : ℕ) : ℤ) by
    exact_mod_cast (mul_left_cancel₀ (by decide : (16 : ℤ) ≠ 0) h)
  push_cast
  have h1 := four_mul_norm (p * q)
  have h2 := four_mul_norm p
  have h3 := four_mul_norm q
  have ha := two_mul_a p q
  have hb := two_mul_b p q
  have hc := two_mul_c p q
  have hd := two_mul_d p q
  linear_combination 4 * h1 - 4 * (norm q : ℤ) * h2 - (p.a ^ 2 + p.b ^ 2 + p.c ^ 2 + p.d ^ 2) * h3
    + (2 * (p * q).a + (p.a * q.a - p.b * q.b - p.c * q.c - p.d * q.d)) * ha
    + (2 * (p * q).b + (p.a * q.b + p.b * q.a + p.c * q.d - p.d * q.c)) * hb
    + (2 * (p * q).c + (p.a * q.c - p.b * q.d + p.c * q.a + p.d * q.b)) * hc
    + (2 * (p * q).d + (p.a * q.d + p.b * q.c - p.c * q.b + p.d * q.a)) * hd

lemma conj_conj (q : HQ) : conj (conj q) = q := by apply HQ.ext <;> simp

lemma conj_mul (p q : HQ) : conj (p * q) = conj q * conj p := by
  apply HQ.ext
  · have h1 := two_mul_a p q; have h2 := two_mul_a (conj q) (conj p); simp at h2 ⊢; linarith
  · have h1 := two_mul_b p q; have h2 := two_mul_b (conj q) (conj p); simp at h2 ⊢; linarith
  · have h1 := two_mul_c p q; have h2 := two_mul_c (conj q) (conj p); simp at h2 ⊢; linarith
  · have h1 := two_mul_d p q; have h2 := two_mul_d (conj q) (conj p); simp at h2 ⊢; linarith

lemma conj_add (p q : HQ) : conj (p + q) = conj p + conj q := by apply HQ.ext <;> simp [add_comm]

lemma norm_conj (q : HQ) : norm (conj q) = norm q := by
  suffices h : 4 * (norm (conj q) : ℤ) = 4 * (norm q : ℤ) by
    exact_mod_cast (mul_left_cancel₀ (by decide : (4 : ℤ) ≠ 0) h)
  rw [four_mul_norm, four_mul_norm]; simp

lemma ofInt_mul (n : ℤ) (q : HQ) : ofInt n * q = ⟨n * q.a, n * q.b, n * q.c, n * q.d, by
    have := q.par
    have h1 : n * q.a - n * q.b = n * (q.a - q.b) := by ring
    have h2 : n * q.a - n * q.c = n * (q.a - q.c) := by ring
    have h3 : n * q.a - n * q.d = n * (q.a - q.d) := by ring
    rw [h1, h2, h3]; simp [Int.mul_emod, this]⟩ := by
  apply HQ.ext
  · have h := two_mul_a (ofInt n) q; simp at h ⊢; linarith
  · have h := two_mul_b (ofInt n) q; simp at h ⊢; linarith
  · have h := two_mul_c (ofInt n) q; simp at h ⊢; linarith
  · have h := two_mul_d (ofInt n) q; simp at h ⊢; linarith

lemma mul_ofInt (q : HQ) (n : ℤ) : q * ofInt n = ofInt n * q := by
  apply HQ.ext
  · have h1 := two_mul_a q (ofInt n); have h2 := two_mul_a (ofInt n) q; simp at h1 h2; linarith
  · have h1 := two_mul_b q (ofInt n); have h2 := two_mul_b (ofInt n) q; simp at h1 h2; linarith
  · have h1 := two_mul_c q (ofInt n); have h2 := two_mul_c (ofInt n) q; simp at h1 h2; linarith
  · have h1 := two_mul_d q (ofInt n); have h2 := two_mul_d (ofInt n) q; simp at h1 h2; linarith

lemma conj_mul_self (q : HQ) : conj q * q = ofInt (norm q : ℤ) := by
  apply HQ.ext
  · have h1 := two_mul_a (conj q) q; have h2 := four_mul_norm q; simp at h1 ⊢; linarith
  · have h1 := two_mul_b (conj q) q; simp at h1 ⊢; linarith
  · have h1 := two_mul_c (conj q) q; simp at h1 ⊢; linarith
  · have h1 := two_mul_d (conj q) q; simp at h1 ⊢; linarith

lemma mul_conj_self (q : HQ) : q * conj q = ofInt (norm q : ℤ) := by
  have := conj_mul_self (conj q)
  rw [conj_conj, norm_conj] at this
  exact this

lemma norm_ofInt (n : ℕ) : norm (ofInt (n : ℤ)) = n ^ 2 := by
  suffices h : 4 * (norm (ofInt (n : ℤ)) : ℤ) = 4 * ((n ^ 2 : ℕ) : ℤ) by
    exact_mod_cast (mul_left_cancel₀ (by decide : (4 : ℤ) ≠ 0) h)
  rw [four_mul_norm]; simp; ring

lemma norm_ofVec (x y z : ℤ) : (norm (ofVec x y z) : ℤ) = x ^ 2 + y ^ 2 + z ^ 2 := by
  have h := four_mul_norm (ofVec x y z)
  have ha : (ofVec x y z).a = 0 := rfl
  have hb : (ofVec x y z).b = 2 * x := rfl
  have hc : (ofVec x y z).c = 2 * y := rfl
  have hd : (ofVec x y z).d = 2 * z := rfl
  rw [ha, hb, hc, hd] at h
  linarith

lemma ofInt_one : ofInt 1 = 1 := by apply HQ.ext <;> simp

lemma norm_one : norm (1 : HQ) = 1 := by
  rw [← ofInt_one]
  simpa using norm_ofInt 1

lemma conj_ofInt (n : ℤ) : conj (ofInt n) = ofInt n := by apply HQ.ext <;> simp

lemma conj_zero : conj 0 = 0 := by apply HQ.ext <;> simp

lemma ofInt_mul_ofInt (m n : ℤ) : ofInt m * ofInt n = ofInt (m * n) := by
  rw [ofInt_mul]; apply HQ.ext <;> simp; ring

lemma mul_left_cancel_of_ne_zero {a b c : HQ} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have h1 : conj a * (a * b) = conj a * (a * c) := congrArg (conj a * ·) h
  rw [← mul_assoc, ← mul_assoc, conj_mul_self, ofInt_mul, ofInt_mul] at h1
  have hna : (norm a : ℤ) ≠ 0 := by
    intro hz
    exact ha ((norm_eq_zero_iff a).mp (by exact_mod_cast hz))
  apply HQ.ext
  · exact mul_left_cancel₀ hna (congrArg HQ.a h1)
  · exact mul_left_cancel₀ hna (congrArg HQ.b h1)
  · exact mul_left_cancel₀ hna (congrArg HQ.c h1)
  · exact mul_left_cancel₀ hna (congrArg HQ.d h1)

lemma mul_right_cancel_of_ne_zero {a b c : HQ} (ha : a ≠ 0) (h : b * a = c * a) : b = c := by
  have h1 : (b * a) * conj a = (c * a) * conj a := congrArg (· * conj a) h
  rw [mul_assoc, mul_assoc, mul_conj_self, mul_ofInt, mul_ofInt, ofInt_mul, ofInt_mul] at h1
  have hna : (norm a : ℤ) ≠ 0 := by
    intro hz
    exact ha ((norm_eq_zero_iff a).mp (by exact_mod_cast hz))
  apply HQ.ext
  · exact mul_left_cancel₀ hna (congrArg HQ.a h1)
  · exact mul_left_cancel₀ hna (congrArg HQ.b h1)
  · exact mul_left_cancel₀ hna (congrArg HQ.c h1)
  · exact mul_left_cancel₀ hna (congrArg HQ.d h1)

/-- Conjugating a pure integer vector `ofVec x y z` by any Hurwitz quaternion `q`
produces another pure integer vector `ofVec x' y' z'`. -/
lemma conj_ofVec_is_ofVec (q : HQ) (x y z : ℤ) :
    ∃ x' y' z' : ℤ, q * ofVec x y z * conj q = ofVec x' y' z' := by
  set w := q * ofVec x y z * conj q
  have hre : w.a = 0 := by
    have hc : conj w = -w := by
      dsimp only [w]
      rw [conj_mul, conj_mul, conj_conj]
      have hv : conj (ofVec x y z) = -(ofVec x y z) := by apply HQ.ext <;> simp [ofVec]
      rw [hv]
      simp [mul_assoc]
    have ha := congrArg HQ.a hc
    simp at ha
    omega
  have hpar := w.par
  rw [hre] at hpar
  refine ⟨w.b / 2, w.c / 2, w.d / 2, ?_⟩
  apply HQ.ext <;> simp only [ofVec] <;> omega

private lemma nearest_two_mul (u m : ℤ) (hm : 0 < m) :
    ∃ k : ℤ, -m ≤ u - 2 * m * k ∧ u - 2 * m * k ≤ m := by
  set k := (u + m) / (2 * m)
  have h1 : (2 * m) * k + (u + m) % (2 * m) = u + m := Int.mul_ediv_add_emod (u + m) (2 * m)
  have h2 : (u + m) % (2 * m) < 2 * m := Int.emod_lt_of_pos _ (by omega)
  have h3 : 0 ≤ (u + m) % (2 * m) := Int.emod_nonneg _ (by omega)
  exact ⟨k, by nlinarith, by nlinarith⟩

/-- Hurwitz right Euclidean division: `x = y * q + r` with `norm r < norm y`. -/
theorem right_euclid (x y : HQ) (hy : y ≠ 0) :
    ∃ q r : HQ, x = y * q + r ∧ norm r < norm y := by
  set m : ℤ := (norm y : ℤ)
  have hm : 0 < m := by
    have h0 : norm y ≠ 0 := fun h => hy ((norm_eq_zero_iff y).mp h)
    dsimp only [m]; exact_mod_cast Nat.pos_of_ne_zero h0
  set u := conj y * x
  obtain ⟨k₀, hk₀l, hk₀u⟩ := nearest_two_mul u.a m hm
  obtain ⟨k₁, hk₁l, hk₁u⟩ := nearest_two_mul u.b m hm
  obtain ⟨k₂, hk₂l, hk₂u⟩ := nearest_two_mul u.c m hm
  obtain ⟨k₃, hk₃l, hk₃u⟩ := nearest_two_mul u.d m hm
  by_cases hall : (u.a - 2 * m * k₀) ^ 2 + (u.b - 2 * m * k₁) ^ 2 +
      (u.c - 2 * m * k₂) ^ 2 + (u.d - 2 * m * k₃) ^ 2 < 4 * m ^ 2
  · let q : HQ := ⟨2 * k₀, 2 * k₁, 2 * k₂, 2 * k₃, by omega⟩
    refine ⟨q, x - y * q, by abel, ?_⟩
    have hmul : conj y * (x - y * q) = u - ofInt m * q := by
      rw [mul_sub, ← mul_assoc, conj_mul_self]
    have hnm : (norm (conj y * (x - y * q)) : ℤ) = m * (norm (x - y * q) : ℤ) := by
      rw [norm_mul, norm_conj]; push_cast; rfl
    have hlt : 4 * (m * (norm (x - y * q) : ℤ)) < 4 * m ^ 2 := by
      rw [← hnm, hmul, four_mul_norm, ofInt_mul]
      simp only [sub_a, sub_b, sub_c, sub_d, q]
      linarith
    have hlt' : (norm (x - y * q) : ℤ) < m := by nlinarith
    dsimp only [m] at hlt'
    exact_mod_cast hlt'
  · have hs0 : (u.a - 2 * m * k₀) ^ 2 ≤ m ^ 2 := by nlinarith
    have hs1 : (u.b - 2 * m * k₁) ^ 2 ≤ m ^ 2 := by nlinarith
    have hs2 : (u.c - 2 * m * k₂) ^ 2 ≤ m ^ 2 := by nlinarith
    have hs3 : (u.d - 2 * m * k₃) ^ 2 ≤ m ^ 2 := by nlinarith
    have he0 : (u.a - 2 * m * k₀) ^ 2 = m ^ 2 := by linarith
    have he1 : (u.b - 2 * m * k₁) ^ 2 = m ^ 2 := by linarith
    have he2 : (u.c - 2 * m * k₂) ^ 2 = m ^ 2 := by linarith
    have he3 : (u.d - 2 * m * k₃) ^ 2 = m ^ 2 := by linarith
    have hd : ∀ (t k : ℤ), (t - 2 * m * k) ^ 2 = m ^ 2 → ∃ s : ℤ, s % 2 = 1 ∧ t = m * s := by
      intro t k ht
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp ht with h | h
      · exact ⟨2 * k + 1, by omega, by linarith⟩
      · exact ⟨2 * k - 1, by omega, by linarith⟩
    obtain ⟨s₀, hs₀, hu₀⟩ := hd u.a k₀ he0
    obtain ⟨s₁, hs₁, hu₁⟩ := hd u.b k₁ he1
    obtain ⟨s₂, hs₂, hu₂⟩ := hd u.c k₂ he2
    obtain ⟨s₃, hs₃, hu₃⟩ := hd u.d k₃ he3
    let q : HQ := ⟨s₀, s₁, s₂, s₃, by omega⟩
    have huq : u = ofInt m * q := by
      rw [ofInt_mul]; apply HQ.ext <;> simp [q, hu₀, hu₁, hu₂, hu₃]
    have hxy : x = y * q := by
      apply mul_left_cancel_of_ne_zero (a := conj y)
      · intro h; exact hy (by have := congrArg conj h; simpa [conj_conj, conj_zero] using this)
      · rw [← mul_assoc, conj_mul_self, ← huq]
    refine ⟨q, 0, by simp [hxy], ?_⟩
    rw [show norm 0 = 0 from (norm_eq_zero_iff 0).mpr rfl]
    dsimp only [m] at hm
    exact_mod_cast hm

/-- Divisibility of a Hurwitz quaternion by an integer `n`. -/
def intDvd (n : ℕ) (q : HQ) : Prop :=
  ∃ q' : HQ, q = ofInt (n : ℤ) * q'

lemma intDvd_iff_coords (n : ℕ) (q : HQ) (hn : Odd n) :
    intDvd n q ↔ ((n : ℤ) ∣ q.a ∧ (n : ℤ) ∣ q.b ∧ (n : ℤ) ∣ q.c ∧ (n : ℤ) ∣ q.d) := by
  constructor
  · rintro ⟨q', hq'⟩
    rw [ofInt_mul] at hq'
    exact ⟨⟨q'.a, congrArg HQ.a hq'⟩, ⟨q'.b, congrArg HQ.b hq'⟩,
      ⟨q'.c, congrArg HQ.c hq'⟩, ⟨q'.d, congrArg HQ.d hq'⟩⟩
  · rintro ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨c', hc'⟩, ⟨d', hd'⟩⟩
    have hpar := q.par
    rw [ha', hb', hc', hd'] at hpar
    have hn2 : (n : ℤ) % 2 = 1 := by obtain ⟨k, rfl⟩ := hn; omega
    have hp' : (a' - b') % 2 = 0 ∧ (a' - c') % 2 = 0 ∧ (a' - d') % 2 = 0 := by
      have h1 : ((n : ℤ) * (a' - b')) % 2 = 0 := by rw [mul_sub]; exact hpar.1
      have h2 : ((n : ℤ) * (a' - c')) % 2 = 0 := by rw [mul_sub]; exact hpar.2.1
      have h3 : ((n : ℤ) * (a' - d')) % 2 = 0 := by rw [mul_sub]; exact hpar.2.2
      rw [Int.mul_emod, hn2, one_mul, Int.emod_emod] at h1 h2 h3
      exact ⟨h1, h2, h3⟩
    refine ⟨⟨a', b', c', d', hp'⟩, ?_⟩
    rw [ofInt_mul]; apply HQ.ext <;> simp [ha', hb', hc', hd']

def leftDvd (q w : HQ) : Prop := ∃ a : HQ, w = q * a

lemma right_ideal_gcd (q₁ q₂ : HQ) (h : q₁ ≠ 0 ∨ q₂ ≠ 0) :
    ∃ g x y : HQ, g = q₁ * x + q₂ * y ∧ leftDvd g q₁ ∧ leftDvd g q₂ := by
  classical
  let S : Set ℕ := {k : ℕ | 0 < k ∧ ∃ x y : HQ, norm (q₁ * x + q₂ * y) = k}
  have hSne : S.Nonempty := by
    rcases h with h₁ | h₂
    · refine ⟨norm q₁, Nat.pos_of_ne_zero (fun hz => h₁ ((norm_eq_zero_iff _).mp hz)), 1, 0, by simp⟩
    · refine ⟨norm q₂, Nat.pos_of_ne_zero (fun hz => h₂ ((norm_eq_zero_iff _).mp hz)), 0, 1, by simp⟩
  set k := Nat.find hSne
  obtain ⟨hkpos, x, y, hxy⟩ := Nat.find_spec hSne
  set g := q₁ * x + q₂ * y
  have hgne : g ≠ 0 := fun hz => by rw [hz, (norm_eq_zero_iff 0).mpr rfl] at hxy; omega
  have hdiv : ∀ z : HQ, (∃ u v : HQ, z = q₁ * u + q₂ * v) → leftDvd g z := by
    rintro z ⟨u, v, rfl⟩
    obtain ⟨t, r, htr, hrlt⟩ := right_euclid (q₁ * u + q₂ * v) g hgne
    have hr0 : r = 0 := by
      by_contra hrne
      have hrpos : 0 < norm r := Nat.pos_of_ne_zero (fun hz => hrne ((norm_eq_zero_iff _).mp hz))
      have hrmem : norm r ∈ S := by
        refine ⟨hrpos, u - x * t, v - y * t, ?_⟩
        have hreq : r = q₁ * (u - x * t) + q₂ * (v - y * t) := by
          have : r = (q₁ * u + q₂ * v) - g * t := eq_sub_of_add_eq' htr.symm
          rw [this]; dsimp only [g]; noncomm_ring
        rw [← hreq]
      exact absurd (Nat.find_min' hSne hrmem) (by omega)
    rw [hr0, add_zero] at htr
    exact ⟨t, htr⟩
  exact ⟨g, x, y, rfl, hdiv q₁ ⟨1, 0, by simp⟩, hdiv q₂ ⟨0, 1, by simp⟩⟩

lemma unique_left_divisor_prime {p : ℕ} (hp : p.Prime) {w q₁ q₂ : HQ}
    (hprim : ¬ intDvd p w) (h1 : leftDvd q₁ w) (h2 : leftDvd q₂ w)
    (hn1 : norm q₁ = p) (hn2 : norm q₂ = p) :
    ∃ u : HQ, norm u = 1 ∧ q₂ = q₁ * u := by
  have hq1ne : q₁ ≠ 0 := fun h => by rw [h, (norm_eq_zero_iff 0).mpr rfl] at hn1; exact hp.ne_zero hn1.symm
  obtain ⟨g, x, y, hg, ⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩ := right_ideal_gcd q₁ q₂ (Or.inl hq1ne)
  have hng_dvd : norm g ∣ p := ⟨norm a₁, by rw [← norm_mul, ← ha₁, hn1]⟩
  rcases hp.eq_one_or_self_of_dvd (norm g) hng_dvd with hg1 | hgp
  · exfalso
    obtain ⟨b₁, hb₁⟩ := h1
    obtain ⟨b₂, hb₂⟩ := h2
    have hgm : g * conj g = 1 := by rw [mul_conj_self, hg1, Nat.cast_one, ofInt_one]
    have hc1 : conj q₁ * w = ofInt (p : ℤ) * b₁ := by
      rw [hb₁, ← mul_assoc, conj_mul_self, hn1]
    have hc2 : conj q₂ * w = ofInt (p : ℤ) * b₂ := by
      rw [hb₂, ← mul_assoc, conj_mul_self, hn2]
    have hgw : w = g * (conj g * w) := by rw [← mul_assoc, hgm, one_mul]
    have hconj_g : conj g = conj x * conj q₁ + conj y * conj q₂ := by
      rw [hg, conj_add, conj_mul, conj_mul]
    have h1' : conj g * w = ofInt (p : ℤ) * (conj x * b₁ + conj y * b₂) := by
      rw [hconj_g, add_mul, mul_assoc, hc1, mul_assoc, hc2, ← mul_ofInt, ← mul_ofInt,
        ← mul_assoc, ← mul_assoc, mul_ofInt, mul_ofInt, ← mul_add]
    have hfinal : w = ofInt (p : ℤ) * (g * (conj x * b₁ + conj y * b₂)) := by
      calc w = g * (conj g * w) := hgw
        _ = g * (ofInt (p : ℤ) * (conj x * b₁ + conj y * b₂)) := by rw [h1']
        _ = (g * ofInt (p : ℤ)) * (conj x * b₁ + conj y * b₂) := (mul_assoc _ _ _).symm
        _ = (ofInt (p : ℤ) * g) * (conj x * b₁ + conj y * b₂) := by rw [mul_ofInt]
        _ = ofInt (p : ℤ) * (g * (conj x * b₁ + conj y * b₂)) := mul_assoc _ _ _
    exact hprim ⟨g * (conj x * b₁ + conj y * b₂), hfinal⟩
  · have ha1u : norm a₁ = 1 := by
      have h := norm_mul g a₁
      rw [← ha₁, hn1, hgp] at h
      have hppos : 0 < p := hp.pos
      nlinarith
    have ha2u : norm a₂ = 1 := by
      have h := norm_mul g a₂
      rw [← ha₂, hn2, hgp] at h
      have hppos : 0 < p := hp.pos
      nlinarith
    refine ⟨conj a₁ * a₂, by rw [norm_mul, norm_conj, ha1u, ha2u, mul_one], ?_⟩
    rw [ha₁, ha₂, mul_assoc, ← mul_assoc a₁, mul_conj_self, ha1u, Nat.cast_one, ofInt_one, one_mul]

lemma exists_left_divisor_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {q : HQ}
    (hdvd : p ∣ norm q) (hprim : ¬ intDvd p q) :
    ∃ r : HQ, norm r = p ∧ leftDvd r q := by
  have hpne : ofInt (p : ℤ) ≠ 0 := fun h => by
    have := congrArg HQ.a h; simp at this; exact hp.ne_zero this
  obtain ⟨g, x, y, hg, ⟨a, ha⟩, ⟨b, hb⟩⟩ := right_ideal_gcd q (ofInt (p : ℤ)) (Or.inr hpne)
  have hng_dvd_p2 : norm g ∣ p ^ 2 := ⟨norm b, by rw [← norm_mul, ← hb, norm_ofInt]⟩
  have hng_cases : norm g = 1 ∨ norm g = p ∨ norm g = p ^ 2 := by
    rw [Nat.dvd_prime_pow hp] at hng_dvd_p2
    obtain ⟨k, hk, hgk⟩ := hng_dvd_p2
    interval_cases k
    · left; simpa using hgk
    · right; left; simpa using hgk
    · right; right; exact hgk
  rcases hng_cases with hg1 | hgp | hgp2
  · exfalso
    have h1 : q * x = g - ofInt (p : ℤ) * y := eq_sub_of_add_eq hg.symm
    have h2 : norm (q * x) = norm (g - ofInt (p : ℤ) * y) := congrArg norm h1
    have h3 : (p : ℤ) ∣ (norm (q * x) : ℤ) := by
      rw [norm_mul, Nat.cast_mul]
      exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hdvd) _
    have h4 : (p : ℤ) ∣ 4 * (norm (g - ofInt (p : ℤ) * y) : ℤ) - 4 * (norm g : ℤ) := by
      rw [four_mul_norm, four_mul_norm, ofInt_mul]
      simp only [sub_a, sub_b, sub_c, sub_d]
      refine ⟨-2 * (g.a * y.a + g.b * y.b + g.c * y.c + g.d * y.d) +
        (p : ℤ) * (y.a ^ 2 + y.b ^ 2 + y.c ^ 2 + y.d ^ 2), ?_⟩
      ring
    rw [← h2, hg1, Nat.cast_one, mul_one] at h4
    have h5 : (p : ℤ) ∣ 4 * (norm (q * x) : ℤ) := dvd_mul_of_dvd_right h3 4
    have h6 : (p : ℤ) ∣ 4 := by
      have := dvd_sub h5 h4
      simpa using this
    have hp4 : p ∣ 4 := Int.natCast_dvd_natCast.mp h6
    have hp2' : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using hp4)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2')
  · exact ⟨g, hgp, ⟨a, ha⟩⟩
  · exfalso
    have hbu : norm b = 1 := by
      have h := norm_mul g b
      rw [← hb, norm_ofInt, hgp2] at h
      have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
      nlinarith
    have hg_eq : g = ofInt (p : ℤ) * conj b := by
      calc g = g * (b * conj b) := by rw [mul_conj_self, hbu, Nat.cast_one, ofInt_one, mul_one]
        _ = (g * b) * conj b := (mul_assoc _ _ _).symm
        _ = ofInt (p : ℤ) * conj b := by rw [← hb]
    exact hprim ⟨conj b * a, by rw [ha, hg_eq, mul_assoc]⟩

/-- Unique left factorization for any odd norm `s`: if `w` is not divisible by any prime dividing `s`,
then any two left divisors of `w` of norm `s` differ by a right unit. -/
lemma unique_left_divisor {s : ℕ} (hs : Odd s) :
    ∀ {w q₁ q₂ : HQ},
      (∀ p : ℕ, p.Prime → p ∣ s → ¬ intDvd p w) →
      leftDvd q₁ w → leftDvd q₂ w → norm q₁ = s → norm q₂ = s →
      ∃ u : HQ, norm u = 1 ∧ q₂ = q₁ * u := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro w q₁ q₂ hprim h1 h2 hn1 hn2
    by_cases hs1 : s = 1
    · subst hs1
      refine ⟨conj q₁ * q₂, by rw [norm_mul, norm_conj, hn1, hn2, mul_one], ?_⟩
      rw [← mul_assoc, mul_conj_self, hn1, Nat.cast_one, ofInt_one, one_mul]
    · have hs_gt : 1 < s := by obtain ⟨k, rfl⟩ := hs; omega
      obtain ⟨p, hp, hps⟩ := Nat.exists_prime_and_dvd (by omega : s ≠ 1)
      have hp2 : p ≠ 2 := by
        intro h; subst h; obtain ⟨k, hk⟩ := hps; obtain ⟨m, hm⟩ := hs; omega
      obtain ⟨s', rfl⟩ := hps
      have hs'odd : Odd s' := by
        rcases Nat.even_or_odd s' with ⟨k, rfl⟩ | h
        · obtain ⟨m, hm⟩ := hs
          have : p * (k + k) = 2 * (p * k) := by ring
          omega
        · exact h
      have hs'lt : s' < p * s' := by
        have hpos : 0 < s' := by obtain ⟨k, rfl⟩ := hs'odd; omega
        have hp_gt : 1 < p := hp.one_lt
        nlinarith
      have hprim_p : ¬ intDvd p w := hprim p hp (dvd_mul_right p s')
      have hprim_q1 : ¬ intDvd p q₁ := fun ⟨t, ht⟩ => by
        obtain ⟨a, ha⟩ := h1
        exact hprim_p ⟨t * a, by rw [ha, ht, mul_assoc]⟩
      have hprim_q2 : ¬ intDvd p q₂ := fun ⟨t, ht⟩ => by
        obtain ⟨a, ha⟩ := h2
        exact hprim_p ⟨t * a, by rw [ha, ht, mul_assoc]⟩
      obtain ⟨r₁, hr₁n, ⟨q₁', hq₁'⟩⟩ := exists_left_divisor_prime hp hp2 (hn1 ▸ dvd_mul_right p s') hprim_q1
      obtain ⟨r₂, hr₂n, ⟨q₂', hq₂'⟩⟩ := exists_left_divisor_prime hp hp2 (hn2 ▸ dvd_mul_right p s') hprim_q2
      have hr1w : leftDvd r₁ w := by
        obtain ⟨a, ha⟩ := h1; exact ⟨q₁' * a, by rw [ha, hq₁', mul_assoc]⟩
      have hr2w : leftDvd r₂ w := by
        obtain ⟨a, ha⟩ := h2; exact ⟨q₂' * a, by rw [ha, hq₂', mul_assoc]⟩
      obtain ⟨u₀, hu₀n, hr2eq⟩ := unique_left_divisor_prime hp hprim_p hr1w hr2w hr₁n hr₂n
      -- Cancel r₁ from w = r₁ * w'
      obtain ⟨a₁, ha₁⟩ := h1
      obtain ⟨a₂, ha₂⟩ := h2
      have hr1ne : r₁ ≠ 0 := fun h => by rw [h, (norm_eq_zero_iff 0).mpr rfl] at hr₁n; exact hp.ne_zero hr₁n.symm
      set w' := q₁' * a₁
      have hw'_eq2 : w' = (u₀ * q₂') * a₂ := by
        apply mul_left_cancel_of_ne_zero hr1ne
        calc r₁ * w' = (r₁ * q₁') * a₁ := (mul_assoc _ _ _).symm
          _ = w := by rw [← hq₁', ← ha₁]
          _ = (r₂ * q₂') * a₂ := by rw [← hq₂', ← ha₂]
          _ = r₁ * ((u₀ * q₂') * a₂) := by rw [hr2eq]; noncomm_ring
      have hprim' : ∀ l : ℕ, l.Prime → l ∣ s' → ¬ intDvd l w' := by
        intro l hl hls ⟨t, ht⟩
        exact hprim l hl (dvd_mul_of_dvd_right hls p) ⟨r₁ * t, by
          calc w = r₁ * w' := by rw [ha₁, hq₁', mul_assoc]
            _ = r₁ * (ofInt (l : ℤ) * t) := by rw [ht]
            _ = ofInt (l : ℤ) * (r₁ * t) := by rw [← mul_assoc, mul_ofInt, mul_assoc]⟩
      have hq1'n : norm q₁' = s' := by
        have := norm_mul r₁ q₁'; rw [← hq₁', hn1, hr₁n] at this
        exact mul_left_cancel₀ hp.ne_zero this.symm
      have hq2'n : norm (u₀ * q₂') = s' := by
        rw [norm_mul, hu₀n, one_mul]
        have := norm_mul r₂ q₂'; rw [← hq₂', hn2, hr₂n] at this
        exact mul_left_cancel₀ hp.ne_zero this.symm
      obtain ⟨u, hun, hu_eq⟩ := ih s' hs'lt hs'odd hprim' ⟨a₁, rfl⟩ ⟨a₂, hw'_eq2⟩ hq1'n hq2'n
      refine ⟨u, hun, ?_⟩
      rw [hq₂', hr2eq, mul_assoc, hu_eq, hq₁', mul_assoc]

/-!
### Counting Hurwitz units (`card = 24`) and mod-`p` matrix representation `ψ : HQ → M₂(𝔽_p)`
-/

/-- Explicit list of all 24 Hurwitz units `norm u = 1`. -/
def unitsList : List HQ :=
  [⟨2, 0, 0, 0, by omega⟩, ⟨-2, 0, 0, 0, by omega⟩,
   ⟨0, 2, 0, 0, by omega⟩, ⟨0, -2, 0, 0, by omega⟩,
   ⟨0, 0, 2, 0, by omega⟩, ⟨0, 0, -2, 0, by omega⟩,
   ⟨0, 0, 0, 2, by omega⟩, ⟨0, 0, 0, -2, by omega⟩,
   ⟨1, 1, 1, 1, by omega⟩, ⟨1, 1, 1, -1, by omega⟩,
   ⟨1, 1, -1, 1, by omega⟩, ⟨1, 1, -1, -1, by omega⟩,
   ⟨1, -1, 1, 1, by omega⟩, ⟨1, -1, 1, -1, by omega⟩,
   ⟨1, -1, -1, 1, by omega⟩, ⟨1, -1, -1, -1, by omega⟩,
   ⟨-1, 1, 1, 1, by omega⟩, ⟨-1, 1, 1, -1, by omega⟩,
   ⟨-1, 1, -1, 1, by omega⟩, ⟨-1, 1, -1, -1, by omega⟩,
   ⟨-1, -1, 1, 1, by omega⟩, ⟨-1, -1, 1, -1, by omega⟩,
   ⟨-1, -1, -1, 1, by omega⟩, ⟨-1, -1, -1, -1, by omega⟩]

def unitsFinset : Finset HQ := unitsList.toFinset

lemma mem_unitsFinset_iff (u : HQ) : u ∈ unitsFinset ↔ norm u = 1 := by
  constructor
  · intro hu
    rw [unitsFinset, List.mem_toFinset] at hu
    simp only [unitsList, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro h1
    have h4 := four_mul_norm u
    rw [h1] at h4
    simp only [Nat.cast_one, mul_one] at h4
    have ha2 : u.a ^ 2 ≤ 4 := by nlinarith [sq_nonneg u.b, sq_nonneg u.c, sq_nonneg u.d]
    have hb2 : u.b ^ 2 ≤ 4 := by nlinarith [sq_nonneg u.a, sq_nonneg u.c, sq_nonneg u.d]
    have hc2 : u.c ^ 2 ≤ 4 := by nlinarith [sq_nonneg u.a, sq_nonneg u.b, sq_nonneg u.d]
    have hd2 : u.d ^ 2 ≤ 4 := by nlinarith [sq_nonneg u.a, sq_nonneg u.b, sq_nonneg u.c]
    have ha : -2 ≤ u.a ∧ u.a ≤ 2 := ⟨by nlinarith, by nlinarith⟩
    have hb : -2 ≤ u.b ∧ u.b ≤ 2 := ⟨by nlinarith, by nlinarith⟩
    have hc : -2 ≤ u.c ∧ u.c ≤ 2 := ⟨by nlinarith, by nlinarith⟩
    have hd : -2 ≤ u.d ∧ u.d ≤ 2 := ⟨by nlinarith, by nlinarith⟩
    have hpar := u.par
    rw [unitsFinset, List.mem_toFinset]
    have hmem : ∀ a b c d : ℤ, u.a = a → u.b = b → u.c = c → u.d = d →
        (∃ h, (⟨a, b, c, d, h⟩ : HQ) ∈ unitsList) → u ∈ unitsList := by
      rintro a b c d ha' hb' hc' hd' ⟨h, hm⟩
      have heq : u = ⟨a, b, c, d, h⟩ := HQ.ext ha' hb' hc' hd'
      rwa [heq]
    rcases u with ⟨a, b, c, d, par⟩
    dsimp only at h4 ha hb hc hd hpar
    have hcases : a = -2 ∨ a = -1 ∨ a = 0 ∨ a = 1 ∨ a = 2 := by omega
    have hb_c : b = -2 ∨ b = -1 ∨ b = 0 ∨ b = 1 ∨ b = 2 := by omega
    have hc_c : c = -2 ∨ c = -1 ∨ c = 0 ∨ c = 1 ∨ c = 2 := by omega
    have hd_c : d = -2 ∨ d = -1 ∨ d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
    · rcases hb_c with rfl | rfl | rfl | rfl | rfl <;>
      · rcases hc_c with rfl | rfl | rfl | rfl | rfl <;>
        · rcases hd_c with rfl | rfl | rfl | rfl | rfl <;>
          · first | (exfalso; omega) | (simp [unitsList])

lemma card_unitsFinset : unitsFinset.card = 24 := by decide

/-- Ring homomorphism `ψ : HQ → M₂(ZMod p)` for an odd prime `p` given `a² + b² + 1 = 0` in `ZMod p`. -/
def matMod (p : ℕ) [Fact p.Prime] (a b : ZMod p) (q : HQ) : Matrix (Fin 2) (Fin 2) (ZMod p) :=
  let inv2 : ZMod p := (2 : ZMod p)⁻¹
  let qa : ZMod p := (q.a : ZMod p) * inv2
  let qb : ZMod p := (q.b : ZMod p) * inv2
  let qc : ZMod p := (q.c : ZMod p) * inv2
  let qd : ZMod p := (q.d : ZMod p) * inv2
  !![qa + a * qc - b * qd, -qb + b * qc + a * qd;
     qb + b * qc + a * qd, qa - a * qc + b * qd]

lemma matMod_mul {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a b : ZMod p} (hab : a ^ 2 + b ^ 2 = -1)
    (q₁ q₂ : HQ) :
    matMod p a b (q₁ * q₂) = matMod p a b q₁ * matMod p a b q₂ := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h2dvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2dvd)
  have hinv2 : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h2ne
  have ha := congrArg (fun z : ℤ => (z : ZMod p)) (two_mul_a q₁ q₂)
  have hb := congrArg (fun z : ℤ => (z : ZMod p)) (two_mul_b q₁ q₂)
  have hc := congrArg (fun z : ℤ => (z : ZMod p)) (two_mul_c q₁ q₂)
  have hd := congrArg (fun z : ℤ => (z : ZMod p)) (two_mul_d q₁ q₂)
  push_cast at ha hb hc hd
  have ha' : ((q₁ * q₂).a : ZMod p) * (2 : ZMod p)⁻¹ =
      ((q₁.a : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.a : ZMod p) * (2 : ZMod p)⁻¹) -
      ((q₁.b : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.b : ZMod p) * (2 : ZMod p)⁻¹) -
      ((q₁.c : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.c : ZMod p) * (2 : ZMod p)⁻¹) -
      ((q₁.d : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.d : ZMod p) * (2 : ZMod p)⁻¹) := by
    linear_combination (2 : ZMod p)⁻¹ ^ 2 * ha - ((q₁ * q₂).a : ZMod p) * (2 : ZMod p)⁻¹ * hinv2
  have hb' : ((q₁ * q₂).b : ZMod p) * (2 : ZMod p)⁻¹ =
      ((q₁.a : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.b : ZMod p) * (2 : ZMod p)⁻¹) +
      ((q₁.b : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.a : ZMod p) * (2 : ZMod p)⁻¹) +
      ((q₁.c : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.d : ZMod p) * (2 : ZMod p)⁻¹) -
      ((q₁.d : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.c : ZMod p) * (2 : ZMod p)⁻¹) := by
    linear_combination (2 : ZMod p)⁻¹ ^ 2 * hb - ((q₁ * q₂).b : ZMod p) * (2 : ZMod p)⁻¹ * hinv2
  have hc' : ((q₁ * q₂).c : ZMod p) * (2 : ZMod p)⁻¹ =
      ((q₁.a : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.c : ZMod p) * (2 : ZMod p)⁻¹) -
      ((q₁.b : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.d : ZMod p) * (2 : ZMod p)⁻¹) +
      ((q₁.c : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.a : ZMod p) * (2 : ZMod p)⁻¹) +
      ((q₁.d : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.b : ZMod p) * (2 : ZMod p)⁻¹) := by
    linear_combination (2 : ZMod p)⁻¹ ^ 2 * hc - ((q₁ * q₂).c : ZMod p) * (2 : ZMod p)⁻¹ * hinv2
  have hd' : ((q₁ * q₂).d : ZMod p) * (2 : ZMod p)⁻¹ =
      ((q₁.a : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.d : ZMod p) * (2 : ZMod p)⁻¹) +
      ((q₁.b : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.c : ZMod p) * (2 : ZMod p)⁻¹) -
      ((q₁.c : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.b : ZMod p) * (2 : ZMod p)⁻¹) +
      ((q₁.d : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.a : ZMod p) * (2 : ZMod p)⁻¹) := by
    linear_combination (2 : ZMod p)⁻¹ ^ 2 * hd - ((q₁ * q₂).d : ZMod p) * (2 : ZMod p)⁻¹ * hinv2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matMod, Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp only [ha', hb', hc', hd']
  · linear_combination -(((q₁.c : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.c : ZMod p) * (2 : ZMod p)⁻¹) +
      ((q₁.d : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.d : ZMod p) * (2 : ZMod p)⁻¹)) * hab
  · linear_combination -(((q₁.c : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.d : ZMod p) * (2 : ZMod p)⁻¹) -
      ((q₁.d : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.c : ZMod p) * (2 : ZMod p)⁻¹)) * hab
  · linear_combination (((q₁.c : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.d : ZMod p) * (2 : ZMod p)⁻¹) -
      ((q₁.d : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.c : ZMod p) * (2 : ZMod p)⁻¹)) * hab
  · linear_combination -(((q₁.c : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.c : ZMod p) * (2 : ZMod p)⁻¹) +
      ((q₁.d : ZMod p) * (2 : ZMod p)⁻¹) * ((q₂.d : ZMod p) * (2 : ZMod p)⁻¹)) * hab

lemma matMod_add {p : ℕ} [Fact p.Prime] (a b : ZMod p) (q₁ q₂ : HQ) :
    matMod p a b (q₁ + q₂) = matMod p a b q₁ + matMod p a b q₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matMod] <;> ring

lemma matMod_eq_zero_iff {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a b : ZMod p} (hab : a ^ 2 + b ^ 2 = -1)
    (q : HQ) :
    matMod p a b q = 0 ↔ intDvd p q := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp h))
  rw [intDvd_iff_coords p q hpodd]
  constructor
  · intro hm
    have e00 : (matMod p a b q) 0 0 = 0 := by rw [hm]; rfl
    have e01 : (matMod p a b q) 0 1 = 0 := by rw [hm]; rfl
    have e10 : (matMod p a b q) 1 0 = 0 := by rw [hm]; rfl
    have e11 : (matMod p a b q) 1 1 = 0 := by rw [hm]; rfl
    simp only [matMod, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue] at e00 e01 e10 e11
    have hinv2 : (2 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero h2ne
    have hqa : (q.a : ZMod p) = 0 := by
      have : 2 * ((q.a : ZMod p) * (2 : ZMod p)⁻¹) = 0 := by linear_combination e00 + e11
      rw [mul_comm 2, mul_assoc, inv_mul_cancel₀ h2ne, mul_one] at this; exact this
    have hqb : (q.b : ZMod p) = 0 := by
      have : 2 * ((q.b : ZMod p) * (2 : ZMod p)⁻¹) = 0 := by linear_combination e10 - e01
      rw [mul_comm 2, mul_assoc, inv_mul_cancel₀ h2ne, mul_one] at this; exact this
    have hqc : (q.c : ZMod p) = 0 := by
      have h1 : 2 * (a * ((q.c : ZMod p) * (2 : ZMod p)⁻¹) - b * ((q.d : ZMod p) * (2 : ZMod p)⁻¹)) = 0 := by
        linear_combination e00 - e11
      have h2 : 2 * (b * ((q.c : ZMod p) * (2 : ZMod p)⁻¹) + a * ((q.d : ZMod p) * (2 : ZMod p)⁻¹)) = 0 := by
        linear_combination e01 + e10
      have h3 : (q.c : ZMod p) * (2 : ZMod p)⁻¹ = 0 := by
        have : -2 * ((q.c : ZMod p) * (2 : ZMod p)⁻¹) = 0 := by
          linear_combination a * h1 + b * h2 - 2 * ((q.c : ZMod p) * (2 : ZMod p)⁻¹) * hab
        have : (2 : ZMod p) * ((q.c : ZMod p) * (2 : ZMod p)⁻¹) = 0 := by linear_combination -this
        exact (mul_eq_zero.mp this).resolve_left h2ne
      exact (mul_eq_zero.mp h3).resolve_right hinv2
    have hqd : (q.d : ZMod p) = 0 := by
      have h1 : 2 * (a * ((q.c : ZMod p) * (2 : ZMod p)⁻¹) - b * ((q.d : ZMod p) * (2 : ZMod p)⁻¹)) = 0 := by
        linear_combination e00 - e11
      have h2 : 2 * (b * ((q.c : ZMod p) * (2 : ZMod p)⁻¹) + a * ((q.d : ZMod p) * (2 : ZMod p)⁻¹)) = 0 := by
        linear_combination e01 + e10
      have h3 : (q.d : ZMod p) * (2 : ZMod p)⁻¹ = 0 := by
        have : -2 * ((q.d : ZMod p) * (2 : ZMod p)⁻¹) = 0 := by
          linear_combination -b * h1 + a * h2 - 2 * ((q.d : ZMod p) * (2 : ZMod p)⁻¹) * hab
        have : (2 : ZMod p) * ((q.d : ZMod p) * (2 : ZMod p)⁻¹) = 0 := by linear_combination -this
        exact (mul_eq_zero.mp this).resolve_left h2ne
      exact (mul_eq_zero.mp h3).resolve_right hinv2
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hqa,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hqb,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hqc,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hqd⟩
  · rintro ⟨ha, hb, hc, hd⟩
    have ha0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr ha
    have hb0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hb
    have hc0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hc
    have hd0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matMod, ha0, hb0, hc0, hd0]

lemma matMod_surjective {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a b : ZMod p} (hab : a ^ 2 + b ^ 2 = -1) :
    Function.Surjective (matMod p a b) := by
  intro M
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp h))
  have hinv2 : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h2ne
  let xa : ZMod p := (M 0 0 + M 1 1) * (2 : ZMod p)⁻¹
  let xb : ZMod p := (M 1 0 - M 0 1) * (2 : ZMod p)⁻¹
  let xc : ZMod p := -(a * (M 0 0 - M 1 1) + b * (M 0 1 + M 1 0)) * (2 : ZMod p)⁻¹
  let xd : ZMod p := (b * (M 0 0 - M 1 1) - a * (M 0 1 + M 1 0)) * (2 : ZMod p)⁻¹
  let q : HQ := ⟨2 * (xa.val : ℤ), 2 * (xb.val : ℤ), 2 * (xc.val : ℤ), 2 * (xd.val : ℤ), by omega⟩
  refine ⟨q, ?_⟩
  have hq : ∀ z : ZMod p, ((2 * (z.val : ℤ) : ℤ) : ZMod p) * (2 : ZMod p)⁻¹ = z := by
    intro z; push_cast; rw [ZMod.natCast_zmod_val, mul_comm 2, mul_assoc, mul_inv_cancel₀ h2ne, mul_one]
  have h2mul : ∀ z : ZMod p, (2 : ZMod p) * z * (2 : ZMod p)⁻¹ = z := fun z => by
    linear_combination z * hinv2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matMod, q, h2mul]
  · dsimp only [xa, xc, xd]
    linear_combination (-(M 0 0 - M 1 1) * (2 : ZMod p)⁻¹) * hab + M 0 0 * hinv2
  · dsimp only [xb, xc, xd]
    linear_combination (-(M 0 1 + M 1 0) * (2 : ZMod p)⁻¹) * hab + M 0 1 * hinv2
  · dsimp only [xb, xc, xd]
    linear_combination (-(M 0 1 + M 1 0) * (2 : ZMod p)⁻¹) * hab + M 1 0 * hinv2
  · dsimp only [xa, xc, xd]
    linear_combination ((M 0 0 - M 1 1) * (2 : ZMod p)⁻¹) * hab + M 1 1 * hinv2

lemma matMod_conj {p : ℕ} [Fact p.Prime] (a b : ZMod p) (q : HQ) :
    matMod p a b (conj q) =
      !![(matMod p a b q) 1 1, -(matMod p a b q) 0 1;
         -(matMod p a b q) 1 0, (matMod p a b q) 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matMod] <;> ring

lemma matMod_det {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a b : ZMod p} (hab : a ^ 2 + b ^ 2 = -1)
    (q : HQ) :
    (matMod p a b q).det = (norm q : ZMod p) := by
  have h1 := matMod_mul hp2 hab q (conj q)
  rw [mul_conj_self] at h1
  have h00 := congrFun (congrFun h1 0) 0
  rw [matMod_conj] at h00
  simp only [matMod, ofInt_a, ofInt_b, ofInt_c, ofInt_d, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Fin.isValue] at h00
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp h))
  have hlhs : ((2 * (norm q : ℤ) : ℤ) : ZMod p) * (2 : ZMod p)⁻¹ + a * (0 * (2 : ZMod p)⁻¹) -
      b * (0 * (2 : ZMod p)⁻¹) = (norm q : ZMod p) := by
    push_cast
    rw [mul_comm 2, mul_assoc, mul_inv_cancel₀ h2ne, mul_one]; ring
  rw [Matrix.det_fin_two]
  dsimp only [matMod] at h00 ⊢
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Fin.isValue] at h00 ⊢
  linear_combination -h00 + hlhs

/-!
### Part 2: Mod-`p` Prime-Power Counting and `r₃^ℤ(d * s²) ≥ r₃^ℤ(d) * φ(s)`
-/

private def rowVec {p : ℕ} : Option (ZMod p) → Fin 2 → ZMod p
  | some t => ![1, t]
  | none => ![0, 1]

private lemma rowVec_ne_zero {p : ℕ} [NeZero p] [Fact p.Prime] (α : Option (ZMod p)) :
    rowVec α 0 ≠ 0 ∨ rowVec α 1 ≠ 0 := by
  cases α with
  | some t => left; simp [rowVec]
  | none => right; simp [rowVec]

private lemma rowVec_prop_eq {p : ℕ} [Fact p.Prime] {α β : Option (ZMod p)} {c : ZMod p}
    (hc : c ≠ 0) (h0 : rowVec α 0 = c * rowVec β 0) (h1 : rowVec α 1 = c * rowVec β 1) :
    α = β := by
  cases α with
  | some t =>
    cases β with
    | some s =>
      simp only [rowVec, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      have hc1 : c = 1 := by linear_combination -h0
      subst hc1; simp only [one_mul] at h1; rw [h1]
    | none =>
      simp only [rowVec, Matrix.cons_val_zero, mul_zero] at h0
      exact absurd h0 one_ne_zero
  | none =>
    cases β with
    | some s =>
      simp only [rowVec, Matrix.cons_val_zero, mul_one] at h0
      exact absurd h0.symm hc
    | none => rfl

/-- Given a rank-1 matrix `M` over `ZMod p` with `det M = 0` and `M ≠ 0`, it factors as `u * wᵀ`. -/
private lemma rank_one_factor {p : ℕ} [Fact p.Prime] {M : Matrix (Fin 2) (Fin 2) (ZMod p)}
    (hdet : M.det = 0) (hne : M ≠ 0) :
    ∃ (u w : Fin 2 → ZMod p), (u 0 ≠ 0 ∨ u 1 ≠ 0) ∧ (w 0 ≠ 0 ∨ w 1 ≠ 0) ∧
      ∀ i j, M i j = u i * w j := by
  rw [Matrix.det_fin_two] at hdet
  by_cases hr0 : M 0 0 ≠ 0 ∨ M 0 1 ≠ 0
  · rcases hr0 with h00 | h01
    · refine ⟨![1, M 1 0 * (M 0 0)⁻¹], ![M 0 0, M 0 1], Or.inl one_ne_zero, Or.inl h00, fun i j => ?_⟩
      fin_cases i <;> fin_cases j <;> simp
      · rw [mul_assoc, inv_mul_cancel₀ h00, mul_one]
      · have hmul : M 1 1 * M 0 0 = M 1 0 * M 0 1 := by linear_combination hdet
        calc M 1 1 = (M 1 1 * M 0 0) * (M 0 0)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ h00, mul_one]
          _ = M 1 0 * (M 0 0)⁻¹ * M 0 1 := by rw [hmul]; ring
    · refine ⟨![1, M 1 1 * (M 0 1)⁻¹], ![M 0 0, M 0 1], Or.inl one_ne_zero, Or.inr h01, fun i j => ?_⟩
      fin_cases i <;> fin_cases j <;> simp
      · have hmul : M 1 0 * M 0 1 = M 1 1 * M 0 0 := by linear_combination -hdet
        calc M 1 0 = (M 1 0 * M 0 1) * (M 0 1)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ h01, mul_one]
          _ = M 1 1 * (M 0 1)⁻¹ * M 0 0 := by rw [hmul]; ring
      · rw [mul_assoc, inv_mul_cancel₀ h01, mul_one]
  · push Not at hr0
    have hr1 : M 1 0 ≠ 0 ∨ M 1 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hne; ext i j; fin_cases i <;> fin_cases j <;> simp [hr0, h]
    refine ⟨![0, 1], ![M 1 0, M 1 1], Or.inr one_ne_zero, hr1, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;> simp [hr0]

/-- For each `α : Option (ZMod p)`, construct a norm-`p` Hurwitz quaternion `π` whose mod-`p` matrix
factors as `u * (rowVec α)ᵀ` with `u ≠ 0`. -/
private lemma exists_prime_quat_for_row {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {a b : ZMod p} (hab : a ^ 2 + b ^ 2 = -1) (α : Option (ZMod p)) :
    ∃ (π : HQ) (u : Fin 2 → ZMod p),
      norm π = p ∧ (u 0 ≠ 0 ∨ u 1 ≠ 0) ∧
      ∀ i j, matMod p a b π i j = u i * rowVec α j := by
  let E : Matrix (Fin 2) (Fin 2) (ZMod p) := !![rowVec α 0, rowVec α 1; 0, 0]
  obtain ⟨q₀, hq₀⟩ := matMod_surjective hp2 hab E
  have hdet0 : (matMod p a b q₀).det = 0 := by rw [hq₀, Matrix.det_fin_two]; simp [E]
  have hdvd : p ∣ norm q₀ := by
    have h := matMod_det hp2 hab q₀
    rw [hdet0] at h
    exact (ZMod.natCast_eq_zero_iff (norm q₀) p).mp h.symm
  have hEne : E ≠ 0 := by
    intro h
    rcases rowVec_ne_zero α with h0 | h1
    · exact h0 (by simpa [E] using congrFun (congrFun h 0) 0)
    · exact h1 (by simpa [E] using congrFun (congrFun h 0) 1)
  have hprim_q₀ : ¬ intDvd p q₀ := by
    rw [← matMod_eq_zero_iff hp2 hab, hq₀]; exact hEne
  have hprim_cq₀ : ¬ intDvd p (conj q₀) := fun ⟨t, ht⟩ => hprim_q₀ ⟨conj t, by
    have := congrArg conj ht
    rw [conj_conj, conj_mul, conj_ofInt, mul_ofInt] at this; exact this⟩
  have hdvd_c : p ∣ norm (conj q₀) := by rwa [norm_conj]
  obtain ⟨r, hrn, ⟨c, hc⟩⟩ := exists_left_divisor_prime Fact.out hp2 hdvd_c hprim_cq₀
  let π := conj r
  have hπn : norm π = p := by rw [norm_conj, hrn]
  have hq₀_fac : q₀ = conj c * π := by
    have := congrArg conj hc
    rw [conj_conj, conj_mul] at this; exact this
  have hMfac : E = matMod p a b (conj c) * matMod p a b π := by
    rw [← hq₀, hq₀_fac, matMod_mul hp2 hab]
  have hπ_det : (matMod p a b π).det = 0 := by
    rw [matMod_det hp2 hab, hπn, ZMod.natCast_self]
  have hπ_ne : matMod p a b π ≠ 0 := by
    intro h; rw [h, Matrix.mul_zero] at hMfac; exact hEne hMfac
  obtain ⟨u, w, hu, hw, hπ_eq⟩ := rank_one_factor hπ_det hπ_ne
  -- Row 0 of E is rowVec α = (c₀₀ u₀ + c₀₁ u₁) * w, so w is a nonzero multiple of rowVec α!
  set sc : ZMod p := matMod p a b (conj c) 0 0 * u 0 + matMod p a b (conj c) 0 1 * u 1
  have hrow0 : ∀ j : Fin 2, rowVec α j = sc * w j := by
    intro j
    have h := congrFun (congrFun hMfac 0) j
    simp only [E, Matrix.mul_apply, Fin.sum_univ_two, hπ_eq, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Fin.isValue] at h
    fin_cases j <;> simp [sc] at h ⊢ <;> linear_combination h
  have hsc_ne : sc ≠ 0 := by
    intro hsc0
    rcases rowVec_ne_zero α with h0 | h1
    · exact h0 (by rw [hrow0 0, hsc0, zero_mul])
    · exact h1 (by rw [hrow0 1, hsc0, zero_mul])
  refine ⟨π, fun i => u i * sc⁻¹, hπn, ?_, fun i j => ?_⟩
  · rcases hu with h0 | h1
    · exact Or.inl (mul_ne_zero h0 (inv_ne_zero hsc_ne))
    · exact Or.inr (mul_ne_zero h1 (inv_ne_zero hsc_ne))
  · rw [hπ_eq i j, hrow0 j]
    have : sc⁻¹ * sc = 1 := inv_mul_cancel₀ hsc_ne
    linear_combination u i * w j * this.symm

/-- Conjugation action of a rank-1 matrix `P = u * wᵀ` on a matrix `M`:
`(P * M * adj P) i j = (wᵀ M w^⊥) * (u * (u^⊥)ᵀ) i j`. -/
private lemma rank_one_conj_formula {p : ℕ} [Fact p.Prime]
    (P M : Matrix (Fin 2) (Fin 2) (ZMod p)) (u w : Fin 2 → ZMod p)
    (hP : ∀ i j, P i j = u i * w j) (htr : M 0 0 + M 1 1 = 0) :
    let adjP : Matrix (Fin 2) (Fin 2) (ZMod p) := !![P 1 1, -P 0 1; -P 1 0, P 0 0]
    let qval : ZMod p := -M 0 1 * w 0 ^ 2 + 2 * M 0 0 * w 0 * w 1 + M 1 0 * w 1 ^ 2
    let U : Matrix (Fin 2) (Fin 2) (ZMod p) := !![u 0 * u 1, -(u 0 ^ 2); u 1 ^ 2, -(u 0 * u 1)]
    P * M * adjP = qval • U := by
  intro adjP qval U
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjP, qval, U, Matrix.mul_apply, Fin.sum_univ_two, hP]
  · linear_combination -u 0 * u 1 * w 0 * w 1 * htr
  · linear_combination u 0 ^ 2 * w 0 * w 1 * htr
  · linear_combination -u 1 ^ 2 * w 0 * w 1 * htr
  · linear_combination u 0 * u 1 * w 0 * w 1 * htr

/-- For odd prime `p`, nonzero traceless `M`, at most 2 values of `α : Option (ZMod p)` annihilate `qval`. -/
private lemma card_good_first_step {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (M : Matrix (Fin 2) (Fin 2) (ZMod p)) (hMne : M ≠ 0) (htr : M 0 0 + M 1 1 = 0) :
    p - 1 ≤ (Finset.univ.filter fun α : Option (ZMod p) =>
      -M 0 1 * rowVec α 0 ^ 2 + 2 * M 0 0 * rowVec α 0 * rowVec α 1 + M 1 0 * rowVec α 1 ^ 2 ≠ 0).card := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp h))
  let bad := Finset.univ.filter fun α : Option (ZMod p) =>
    -M 0 1 * rowVec α 0 ^ 2 + 2 * M 0 0 * rowVec α 0 * rowVec α 1 + M 1 0 * rowVec α 1 ^ 2 = 0
  have htot : (Finset.univ : Finset (Option (ZMod p))).card = p + 1 := by
    simp [ZMod.card]
  have hcomp : (Finset.univ.filter fun α : Option (ZMod p) =>
      -M 0 1 * rowVec α 0 ^ 2 + 2 * M 0 0 * rowVec α 0 * rowVec α 1 + M 1 0 * rowVec α 1 ^ 2 ≠ 0).card +
      bad.card = p + 1 := by
    have hun : (Finset.univ.filter fun α : Option (ZMod p) =>
        -M 0 1 * rowVec α 0 ^ 2 + 2 * M 0 0 * rowVec α 0 * rowVec α 1 + M 1 0 * rowVec α 1 ^ 2 ≠ 0) ∪
        bad = Finset.univ := by
      ext α; simp only [bad, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro (ne_or_eq _ 0)
    have hdj : Disjoint (Finset.univ.filter fun α : Option (ZMod p) =>
        -M 0 1 * rowVec α 0 ^ 2 + 2 * M 0 0 * rowVec α 0 * rowVec α 1 + M 1 0 * rowVec α 1 ^ 2 ≠ 0) bad := by
      rw [Finset.disjoint_left]; intro α h1 h2
      exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    rw [← Finset.card_union_of_disjoint hdj, hun, htot]
  suffices hbad : bad.card ≤ 2 by omega
  -- Count roots of f(t) = M 1 0 * t^2 + 2 * M 0 0 * t - M 0 1 in ZMod p, plus maybe none
  let f : Polynomial (ZMod p) :=
    Polynomial.C (M 1 0) * Polynomial.X ^ 2 + Polynomial.C (2 * M 0 0) * Polynomial.X + Polynomial.C (-M 0 1)
  have hmem_some : ∀ t : ZMod p, some t ∈ bad ↔ f.eval t = 0 := by
    intro t
    dsimp only [bad]
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, rowVec, Matrix.cons_val_zero, Matrix.cons_val_one, f,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    constructor <;> intro h <;> linear_combination h
  have hmem_none : none ∈ bad ↔ M 1 0 = 0 := by
    simp [bad, rowVec]
  by_cases h10 : M 1 0 ≠ 0
  · have hfne : f ≠ 0 := by
      intro hf0
      have hc := congrArg (fun g => g.coeff 2) hf0
      simp [f] at hc
      exact h10 hc
    have hdeg : f.natDegree ≤ 2 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    have hsub : bad ⊆ f.roots.toFinset.image some := by
      intro α hα
      cases α with
      | none => exact absurd (hmem_none.mp hα) h10
      | some t =>
        rw [Finset.mem_image]
        exact ⟨t, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hfne).mpr ((hmem_some t).mp hα)), rfl⟩
    calc bad.card ≤ (f.roots.toFinset.image some).card := Finset.card_le_card hsub
      _ ≤ f.roots.toFinset.card := Finset.card_image_le
      _ ≤ f.roots.card := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := Polynomial.card_roots' f
      _ ≤ 2 := hdeg
  · push Not at h10
    by_cases h00 : M 0 0 ≠ 0
    · -- Linear polynomial 2 * M 0 0 * t - M 0 1 has at most 1 root, plus none -> ≤ 2
      have hsub : bad ⊆ {none, some (M 0 1 * (2 * M 0 0)⁻¹)} := by
        intro α hα
        cases α with
        | none => simp
        | some t =>
          simp only [Finset.mem_insert, Finset.mem_singleton, Option.some.injEq, reduceCtorEq, false_or]
          have hev := (hmem_some t).mp hα
          simp only [f, h10, map_zero, zero_mul, zero_add, Polynomial.eval_add,
            Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at hev
          have h2m0 : 2 * M 0 0 ≠ 0 := mul_ne_zero h2ne h00
          have hmul : 2 * M 0 0 * t = M 0 1 := by linear_combination hev
          calc t = (2 * M 0 0 * t) * (2 * M 0 0)⁻¹ := by
                rw [mul_comm (2 * M 0 0), mul_assoc, mul_inv_cancel₀ h2m0, mul_one]
            _ = M 0 1 * (2 * M 0 0)⁻¹ := by rw [hmul]
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
    · push Not at h00
      have h11 : M 1 1 = 0 := by linear_combination htr - h00
      have h01 : M 0 1 ≠ 0 := by
        intro h01
        apply hMne; ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
      have hsub : bad ⊆ {none} := by
        intro α hα
        cases α with
        | none => simp
        | some t =>
          have hev := (hmem_some t).mp hα
          simp [f, h10, h00] at hev
          exact absurd hev h01
      exact (Finset.card_le_card hsub).trans (by simp)

/-- For nonzero vector `u : Fin 2 → ZMod p`, at least `p` choices of `α : Option (ZMod p)` have `rowVec α · u ≠ 0`. -/
private lemma card_good_next_step {p : ℕ} [Fact p.Prime] (u : Fin 2 → ZMod p) (hu : u 0 ≠ 0 ∨ u 1 ≠ 0) :
    p ≤ (Finset.univ.filter fun α : Option (ZMod p) =>
      rowVec α 0 * u 0 + rowVec α 1 * u 1 ≠ 0).card := by
  let bad := Finset.univ.filter fun α : Option (ZMod p) =>
    rowVec α 0 * u 0 + rowVec α 1 * u 1 = 0
  have hcomp : (Finset.univ.filter fun α : Option (ZMod p) =>
      rowVec α 0 * u 0 + rowVec α 1 * u 1 ≠ 0).card + bad.card = p + 1 := by
    have hun : (Finset.univ.filter fun α : Option (ZMod p) =>
        rowVec α 0 * u 0 + rowVec α 1 * u 1 ≠ 0) ∪ bad = Finset.univ := by
      ext α; simp only [bad, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro (ne_or_eq _ 0)
    have hdj : Disjoint (Finset.univ.filter fun α : Option (ZMod p) =>
        rowVec α 0 * u 0 + rowVec α 1 * u 1 ≠ 0) bad := by
      rw [Finset.disjoint_left]; intro α h1 h2
      exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    rw [← Finset.card_union_of_disjoint hdj, hun]; simp [ZMod.card]
  suffices hbad : bad.card ≤ 1 by omega
  by_cases hu1 : u 1 ≠ 0
  · have hsub : bad ⊆ {some (-(u 0) * (u 1)⁻¹)} := by
      intro α hα
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hα
      cases α with
      | none => simp [rowVec] at hα; exact absurd hα hu1
      | some t =>
        simp only [rowVec, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at hα
        simp only [Finset.mem_singleton, Option.some.injEq]
        calc t = (t * u 1) * (u 1)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hu1, mul_one]
          _ = -(u 0) * (u 1)⁻¹ := by rw [show t * u 1 = -u 0 by linear_combination hα]
    exact (Finset.card_le_card hsub).trans (by simp)
  · push Not at hu1
    have hu0 : u 0 ≠ 0 := hu.resolve_right (not_not.mpr hu1)
    have hsub : bad ⊆ {none} := by
      intro α hα
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hα
      cases α with
      | none => simp
      | some t => simp [rowVec, hu1] at hα; exact absurd hα hu0
    exact (Finset.card_le_card hsub).trans (by simp)

/-- Prime-power lifting: for odd prime `p`, `e ≥ 1`, and primitive pure vector `v = ofVec x y z`,
there exists a Finset `S` of `≥ φ(p^e)` pairwise non-left-associate Hurwitz quaternions of norm `p^e`
such that `¬ intDvd p (q * v * conj q)` (and `¬ intDvd p q`) for all `q ∈ S`. -/
lemma exists_prime_pow_lifts {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (e : ℕ) (he : 1 ≤ e)
    (x y z : ℤ) (hprim : ¬ intDvd p (ofVec x y z)) :
    ∃ S : Finset HQ,
      Nat.totient (p ^ e) ≤ S.card ∧
      (∀ q ∈ S, norm q = p ^ e ∧ ¬ intDvd p q ∧ ¬ intDvd p (q * ofVec x y z * conj q)) ∧
      (∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ u : HQ, norm u = 1 → q₁ = u * q₂ → q₁ = q₂) := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨a₀, b₀, _, _, hab₀⟩ := Nat.sq_add_sq_zmodEq p (-1)
  set a : ZMod p := (a₀ : ZMod p)
  set b : ZMod p := (b₀ : ZMod p)
  have hab : a ^ 2 + b ^ 2 = -1 := by
    have h := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hab₀
    simpa [a, b] using h
  -- Choose a canonical prime quaternion π_α for each α : Option (ZMod p)
  choose π u_π hπ_norm hπ_u hπ_mat using fun α : Option (ZMod p) =>
    exists_prime_quat_for_row hp2 hab α
  -- Pairwise non-left-associate property of π_α
  have hπ_nla : ∀ α β : Option (ZMod p), ∀ u : HQ, norm u = 1 → π α = u * π β → α = β := by
    intro α β u hun heq
    have hM := congrArg (matMod p a b) heq
    rw [matMod_mul hp2 hab] at hM
    rcases hπ_u α with hu0 | hu1
    · set c := matMod p a b u 0 0 * u_π β 0 + matMod p a b u 0 1 * u_π β 1
      have h0 : u_π α 0 * rowVec α 0 = c * rowVec β 0 := by
        have h := congrFun (congrFun hM 0) 0
        simp only [Matrix.mul_apply, Fin.sum_univ_two, hπ_mat] at h
        dsimp only [c]; linear_combination h
      have h1 : u_π α 0 * rowVec α 1 = c * rowVec β 1 := by
        have h := congrFun (congrFun hM 0) 1
        simp only [Matrix.mul_apply, Fin.sum_univ_two, hπ_mat] at h
        dsimp only [c]; linear_combination h
      have hc0 : c ≠ 0 := by
        intro hc
        rcases rowVec_ne_zero α with hr0 | hr1
        · rw [hc, zero_mul] at h0; exact mul_ne_zero hu0 hr0 h0
        · rw [hc, zero_mul] at h1; exact mul_ne_zero hu0 hr1 h1
      have hr0' : rowVec α 0 = c * (u_π α 0)⁻¹ * rowVec β 0 := by
        calc rowVec α 0 = (u_π α 0)⁻¹ * (u_π α 0 * rowVec α 0) := by
              rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
          _ = c * (u_π α 0)⁻¹ * rowVec β 0 := by rw [h0]; ring
      have hr1' : rowVec α 1 = c * (u_π α 0)⁻¹ * rowVec β 1 := by
        calc rowVec α 1 = (u_π α 0)⁻¹ * (u_π α 0 * rowVec α 1) := by
              rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
          _ = c * (u_π α 0)⁻¹ * rowVec β 1 := by rw [h1]; ring
      exact rowVec_prop_eq (mul_ne_zero hc0 (inv_ne_zero hu0)) hr0' hr1'
    · set c := matMod p a b u 1 0 * u_π β 0 + matMod p a b u 1 1 * u_π β 1
      have h0 : u_π α 1 * rowVec α 0 = c * rowVec β 0 := by
        have h := congrFun (congrFun hM 1) 0
        simp only [Matrix.mul_apply, Fin.sum_univ_two, hπ_mat] at h
        dsimp only [c]; linear_combination h
      have h1 : u_π α 1 * rowVec α 1 = c * rowVec β 1 := by
        have h := congrFun (congrFun hM 1) 1
        simp only [Matrix.mul_apply, Fin.sum_univ_two, hπ_mat] at h
        dsimp only [c]; linear_combination h
      have hc0 : c ≠ 0 := by
        intro hc
        rcases rowVec_ne_zero α with hr0 | hr1
        · rw [hc, zero_mul] at h0; exact mul_ne_zero hu1 hr0 h0
        · rw [hc, zero_mul] at h1; exact mul_ne_zero hu1 hr1 h1
      have hr0' : rowVec α 0 = c * (u_π α 1)⁻¹ * rowVec β 0 := by
        calc rowVec α 0 = (u_π α 1)⁻¹ * (u_π α 1 * rowVec α 0) := by
              rw [← mul_assoc, inv_mul_cancel₀ hu1, one_mul]
          _ = c * (u_π α 1)⁻¹ * rowVec β 0 := by rw [h0]; ring
      have hr1' : rowVec α 1 = c * (u_π α 1)⁻¹ * rowVec β 1 := by
        calc rowVec α 1 = (u_π α 1)⁻¹ * (u_π α 1 * rowVec α 1) := by
              rw [← mul_assoc, inv_mul_cancel₀ hu1, one_mul]
          _ = c * (u_π α 1)⁻¹ * rowVec β 1 := by rw [h1]; ring
      exact rowVec_prop_eq (mul_ne_zero hc0 (inv_ne_zero hu1)) hr0' hr1'
  -- Helper: matrix U = !![u0*u1, -u0^2; u1^2, -u0*u1] is nonzero when u ≠ 0
  have hU_ne : ∀ u : Fin 2 → ZMod p, (u 0 ≠ 0 ∨ u 1 ≠ 0) →
      (!![u 0 * u 1, -(u 0 ^ 2); u 1 ^ 2, -(u 0 * u 1)] : Matrix (Fin 2) (Fin 2) (ZMod p)) ≠ 0 := by
    intro u hu h0
    rcases hu with h | h
    · have h01 := congrFun (congrFun h0 0) 1
      simp at h01; exact h h01
    · have h10 := congrFun (congrFun h0 1) 0
      simp at h10; exact h h10
  -- Prove by induction on k where e = k + 1, also tracking the rank-1 matrix of q*v*conj q!
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' he
  -- Induction invariant on k: S has ≥ (p-1)*p^k elements, each with q*v*conj q having nonzero mod-p matrix
  -- of the form sc * U(col_q) where col_q is the column vector of matMod q!
  suffices hind : ∀ k : ℕ, ∃ S : Finset HQ,
      (p - 1) * p ^ k ≤ S.card ∧
      (∀ q ∈ S, norm q = p ^ (k + 1) ∧ ¬ intDvd p q ∧ ¬ intDvd p (q * ofVec x y z * conj q) ∧
        ∃ (col : Fin 2 → ZMod p) (sc : ZMod p), (col 0 ≠ 0 ∨ col 1 ≠ 0) ∧ sc ≠ 0 ∧
          matMod p a b (q * ofVec x y z * conj q) =
            sc • !![col 0 * col 1, -(col 0 ^ 2); col 1 ^ 2, -(col 0 * col 1)] ∧
          ∃ rw_ : Fin 2 → ZMod p, (rw_ 0 ≠ 0 ∨ rw_ 1 ≠ 0) ∧ ∀ i j, matMod p a b q i j = col i * rw_ j) ∧
      (∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ u : HQ, norm u = 1 → q₁ = u * q₂ → q₁ = q₂) by
    obtain ⟨S, hcard, hprop, hnla⟩ := hind k
    refine ⟨S, ?_, fun q hq => ⟨(hprop q hq).1, (hprop q hq).2.1, (hprop q hq).2.2.1⟩, hnla⟩
    have htot : Nat.totient (p ^ (k + 1)) = (p - 1) * p ^ k := by
      rw [Nat.totient_prime_pow hp (Nat.succ_pos k)]; simp [mul_comm]
    rw [htot]; exact hcard
  intro k
  induction k with
  | zero =>
    let Mv := matMod p a b (ofVec x y z)
    have hMv_ne : Mv ≠ 0 := by
      intro h; exact hprim ((matMod_eq_zero_iff hp2 hab _).mp h)
    have hMv_tr : Mv 0 0 + Mv 1 1 = 0 := by
      simp [Mv, matMod, ofVec]
    let good := Finset.univ.filter fun α : Option (ZMod p) =>
      -Mv 0 1 * rowVec α 0 ^ 2 + 2 * Mv 0 0 * rowVec α 0 * rowVec α 1 + Mv 1 0 * rowVec α 1 ^ 2 ≠ 0
    have hgood_card : p - 1 ≤ good.card := card_good_first_step hp2 Mv hMv_ne hMv_tr
    refine ⟨good.image π, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective good (fun α β h => hπ_nla α β 1 norm_one (by simpa using h))]
      simpa using hgood_card
    · intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨α, hα, rfl⟩ := hq
      have hqval : -Mv 0 1 * rowVec α 0 ^ 2 + 2 * Mv 0 0 * rowVec α 0 * rowVec α 1 +
          Mv 1 0 * rowVec α 1 ^ 2 ≠ 0 := (Finset.mem_filter.mp hα).2
      have hconj_mat : matMod p a b (π α * ofVec x y z * conj (π α)) =
          (-Mv 0 1 * rowVec α 0 ^ 2 + 2 * Mv 0 0 * rowVec α 0 * rowVec α 1 +
            Mv 1 0 * rowVec α 1 ^ 2) •
          !![u_π α 0 * u_π α 1, -(u_π α 0 ^ 2); u_π α 1 ^ 2, -(u_π α 0 * u_π α 1)] := by
        rw [matMod_mul hp2 hab, matMod_mul hp2 hab, matMod_conj]
        exact rank_one_conj_formula (matMod p a b (π α)) Mv (u_π α) (rowVec α) (hπ_mat α) hMv_tr
      have hπ_prim : ¬ intDvd p (π α) := by
        rw [← matMod_eq_zero_iff hp2 hab]
        intro h0
        rcases hπ_u α with hu | hu <;> rcases rowVec_ne_zero α with hr | hr
        · exact mul_ne_zero hu hr (by rw [← hπ_mat α 0 0, h0]; rfl)
        · exact mul_ne_zero hu hr (by rw [← hπ_mat α 0 1, h0]; rfl)
        · exact mul_ne_zero hu hr (by rw [← hπ_mat α 1 0, h0]; rfl)
        · exact mul_ne_zero hu hr (by rw [← hπ_mat α 1 1, h0]; rfl)
      have hw_prim : ¬ intDvd p (π α * ofVec x y z * conj (π α)) := by
        rw [← matMod_eq_zero_iff hp2 hab, hconj_mat]
        intro h0
        exact hU_ne (u_π α) (hπ_u α) ((smul_eq_zero.mp h0).resolve_left hqval)
      exact ⟨by simpa using hπ_norm α, hπ_prim, hw_prim, u_π α, _, hπ_u α, hqval, hconj_mat,
        rowVec α, rowVec_ne_zero α, hπ_mat α⟩
    · intro q₁ hq₁ q₂ hq₂ u hun heq
      rw [Finset.mem_image] at hq₁ hq₂
      obtain ⟨α₁, _, rfl⟩ := hq₁
      obtain ⟨α₂, _, rfl⟩ := hq₂
      rw [hπ_nla α₁ α₂ u hun heq]
  | succ k ih =>
    obtain ⟨S, hScard, hSprop, hSnla⟩ := ih
    -- For each q ∈ S, choose col_q, sc_q, rw_q from hSprop
    let goodNext (q : HQ) (hq : q ∈ S) : Finset (Option (ZMod p)) :=
      let col := (hSprop q hq).2.2.2.choose
      Finset.univ.filter fun α : Option (ZMod p) => rowVec α 0 * col 0 + rowVec α 1 * col 1 ≠ 0
    let pairs := S.attach.sigma fun q => goodNext q.1 q.2
    let f : ((q : {x // x ∈ S}) × Option (ZMod p)) → HQ := fun t => π t.2 * t.1.1
    -- Every element of pairs produces a valid next-level quaternion
    have hpair_prop : ∀ t ∈ pairs,
        norm (f t) = p ^ (k + 2) ∧ ¬ intDvd p (f t) ∧ ¬ intDvd p (f t * ofVec x y z * conj (f t)) ∧
        ∃ (col : Fin 2 → ZMod p) (sc : ZMod p), (col 0 ≠ 0 ∨ col 1 ≠ 0) ∧ sc ≠ 0 ∧
          matMod p a b (f t * ofVec x y z * conj (f t)) =
            sc • !![col 0 * col 1, -(col 0 ^ 2); col 1 ^ 2, -(col 0 * col 1)] ∧
          ∃ rw_ : Fin 2 → ZMod p, (rw_ 0 ≠ 0 ∨ rw_ 1 ≠ 0) ∧ ∀ i j, matMod p a b (f t) i j = col i * rw_ j := by
      intro t ht
      rcases t with ⟨⟨q, hq⟩, α⟩
      have hα : α ∈ goodNext q hq := (Finset.mem_sigma.mp ht).2
      dsimp only [f]
      have hq_norm := (hSprop q hq).1
      set col := (hSprop q hq).2.2.2.choose
      have hcol_spec := (hSprop q hq).2.2.2.choose_spec
      obtain ⟨sc, hcol_ne, hsc_ne, hqv_mat, rw_, hrw_ne, hq_mat⟩ := hcol_spec
      have hdot_ne : rowVec α 0 * col 0 + rowVec α 1 * col 1 ≠ 0 := (Finset.mem_filter.mp hα).2
      set dot := rowVec α 0 * col 0 + rowVec α 1 * col 1
      -- Matrix of π α * q is (dot • u_π α) * rw_ᵀ
      have hprod_mat : ∀ i j, matMod p a b (π α * q) i j = u_π α i * (dot * rw_ j) := by
        intro i j
        rw [matMod_mul hp2 hab]
        simp only [Matrix.mul_apply, Fin.sum_univ_two, hπ_mat, hq_mat]
        dsimp only [dot]; ring
      -- Matrix of (π α * q) * v * conj (π α * q) = π α * (q * v * conj q) * conj (π α)
      have hconj_eq : (π α * q) * ofVec x y z * conj (π α * q) =
          π α * (q * ofVec x y z * conj q) * conj (π α) := by
        rw [conj_mul]; noncomm_ring
      have hconj_mat : matMod p a b ((π α * q) * ofVec x y z * conj (π α * q)) =
          (sc * dot ^ 2) • !![u_π α 0 * u_π α 1, -(u_π α 0 ^ 2); u_π α 1 ^ 2, -(u_π α 0 * u_π α 1)] := by
        rw [hconj_eq, matMod_mul hp2 hab, matMod_mul hp2 hab, matMod_conj, hqv_mat]
        set M := sc • (!![col 0 * col 1, -(col 0 ^ 2); col 1 ^ 2, -(col 0 * col 1)] : Matrix (Fin 2) (Fin 2) (ZMod p))
        have hMtr : M 0 0 + M 1 1 = 0 := by simp [M]
        have hform := rank_one_conj_formula (matMod p a b (π α)) M (u_π α) (rowVec α) (hπ_mat α) hMtr
        rw [hform]
        congr 1
        simp only [M, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue]
        dsimp only [dot]; ring
      have hnorm : norm (π α * q) = p ^ (k + 2) := by
        rw [norm_mul, hπ_norm, hq_norm, ← pow_succ']
      have hprim_pq : ¬ intDvd p (π α * q) := by
        rw [← matMod_eq_zero_iff hp2 hab]
        intro h0
        rcases hπ_u α with hu | hu <;> rcases hrw_ne with hr | hr
        · exact mul_ne_zero hu (mul_ne_zero hdot_ne hr) (by rw [← hprod_mat 0 0, h0]; rfl)
        · exact mul_ne_zero hu (mul_ne_zero hdot_ne hr) (by rw [← hprod_mat 0 1, h0]; rfl)
        · exact mul_ne_zero hu (mul_ne_zero hdot_ne hr) (by rw [← hprod_mat 1 0, h0]; rfl)
        · exact mul_ne_zero hu (mul_ne_zero hdot_ne hr) (by rw [← hprod_mat 1 1, h0]; rfl)
      have hprim_w : ¬ intDvd p ((π α * q) * ofVec x y z * conj (π α * q)) := by
        rw [← matMod_eq_zero_iff hp2 hab, hconj_mat]
        intro h0
        exact hU_ne (u_π α) (hπ_u α) ((smul_eq_zero.mp h0).resolve_left (mul_ne_zero hsc_ne (pow_ne_zero 2 hdot_ne)))
      refine ⟨hnorm, hprim_pq, hprim_w, u_π α, sc * dot ^ 2, hπ_u α,
        mul_ne_zero hsc_ne (pow_ne_zero 2 hdot_ne), hconj_mat, fun j => dot * rw_ j, ?_, hprod_mat⟩
      rcases hrw_ne with h0 | h1
      · exact Or.inl (mul_ne_zero hdot_ne h0)
      · exact Or.inr (mul_ne_zero hdot_ne h1)
    -- Pairwise non-left-associate on pairs -> also implies f is injective on pairs!
    have hpair_nla : ∀ t₁ ∈ pairs, ∀ t₂ ∈ pairs, ∀ u : HQ, norm u = 1 →
        f t₁ = u * f t₂ → t₁ = t₂ := by
      intro t₁ ht₁ t₂ ht₂ u hun heq
      rcases t₁ with ⟨⟨q₁, hq₁⟩, α₁⟩
      rcases t₂ with ⟨⟨q₂, hq₂⟩, α₂⟩
      dsimp only [f] at heq
      -- Take conjugate: conj q₁ * conj (π α₁) = conj q₂ * (conj (π α₂) * conj u)
      have hc : conj (π α₁ * q₁) = conj q₁ * conj (π α₁) := conj_mul _ _
      have hc2 : conj (π α₁ * q₁) = conj q₂ * (conj (π α₂) * conj u) := by
        rw [heq, conj_mul, conj_mul, mul_assoc]
      have hodd : Odd (p ^ (k + 1)) := Odd.pow (hp.odd_of_ne_two hp2)
      have hprim_c : ∀ l : ℕ, l.Prime → l ∣ p ^ (k + 1) → ¬ intDvd l (conj (π α₁ * q₁)) := by
        intro l hl hldvd ⟨t, ht⟩
        have hlp : l = p := (Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow hldvd)
        subst hlp
        apply (hpair_prop ⟨⟨q₁, hq₁⟩, α₁⟩ ht₁).2.1
        refine ⟨conj t, ?_⟩
        have := congrArg conj ht
        rw [conj_conj, conj_mul, conj_ofInt, mul_ofInt] at this; exact this
      obtain ⟨u₀, hu₀n, hq2c⟩ := unique_left_divisor hodd hprim_c
        ⟨conj (π α₁), hc⟩ ⟨conj (π α₂) * conj u, hc2⟩
        (by rw [norm_conj, (hSprop q₁ hq₁).1]) (by rw [norm_conj, (hSprop q₂ hq₂).1])
      have hq2eq : q₂ = conj u₀ * q₁ := by
        have := congrArg conj hq2c
        rw [conj_conj, conj_mul, conj_conj] at this; exact this
      have hqeq : q₂ = q₁ := hSnla q₂ hq₂ q₁ hq₁ (conj u₀) (by rwa [norm_conj]) hq2eq
      rcases hqeq with rfl
      have hq1ne : q₂ ≠ 0 := fun h => by
        have := (hSprop q₂ hq₁).1; rw [h, (norm_eq_zero_iff 0).mpr rfl] at this
        exact pow_ne_zero _ hp.ne_zero this.symm
      have hπeq : π α₁ = u * π α₂ :=
        mul_right_cancel_of_ne_zero hq1ne (by rw [heq, mul_assoc])
      have hαeq : α₁ = α₂ := hπ_nla α₁ α₂ u hun hπeq
      subst hαeq; rfl
    have hfinj : Set.InjOn f pairs := fun t₁ ht₁ t₂ ht₂ heq =>
      hpair_nla t₁ ht₁ t₂ ht₂ 1 norm_one (by simpa using heq)
    refine ⟨pairs.image f, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn hfinj, Finset.card_sigma]
      have hge : ∀ q ∈ S.attach, p ≤ (goodNext q.1 q.2).card := fun q _ =>
        card_good_next_step _ (hSprop q.1 q.2).2.2.2.choose_spec.choose_spec.1
      calc (p - 1) * p ^ (k + 1) = (p - 1) * p ^ k * p := by ring
        _ ≤ S.card * p := Nat.mul_le_mul_right p hScard
        _ = ∑ _q ∈ S.attach, p := by rw [Finset.sum_const, Finset.card_attach, smul_eq_mul]
        _ ≤ ∑ q ∈ S.attach, (goodNext q.1 q.2).card := Finset.sum_le_sum hge
    · intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨t, ht, rfl⟩ := hq
      exact hpair_prop t ht
    · intro q₁ hq₁ q₂ hq₂ u hun heq
      rw [Finset.mem_image] at hq₁ hq₂
      obtain ⟨t₁, ht₁, rfl⟩ := hq₁
      obtain ⟨t₂, ht₂, rfl⟩ := hq₂
      rw [hpair_nla t₁ ht₁ t₂ ht₂ u hun heq]

/-- Multiplying a pure vector `v` by `q * · * conj q` with `gcd(p, norm q) = 1` preserves `¬ intDvd p`. -/
private lemma not_intDvd_conj_of_coprime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q v : HQ} (hcop : Nat.Coprime p (norm q)) (hv : ¬ intDvd p v) :
    ¬ intDvd p (q * v * conj q) := by
  intro ⟨t, ht⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h1 : ofInt ((norm q : ℤ) ^ 2) * v = ofInt (p : ℤ) * (conj q * t * q) := by
    calc ofInt ((norm q : ℤ) ^ 2) * v
        = ofInt (norm q : ℤ) * (v * ofInt (norm q : ℤ)) := by
            rw [mul_ofInt, ← mul_assoc, ofInt_mul_ofInt]; ring_nf
      _ = (conj q * q) * (v * (conj q * q)) := by rw [conj_mul_self]
      _ = conj q * (q * v * conj q) * q := by noncomm_ring
      _ = conj q * (ofInt (p : ℤ) * t) * q := by rw [ht]
      _ = ofInt (p : ℤ) * (conj q * t * q) := by
            rw [← mul_assoc (conj q), mul_ofInt]; noncomm_ring
  rw [ofInt_mul, ofInt_mul] at h1
  have hcopZ : IsCoprime (p : ℤ) ((norm q : ℤ) ^ 2) := by
    have : Nat.Coprime p (norm q ^ 2) := hcop.pow_right 2
    simpa [Nat.cast_pow] using this.isCoprime
  have hdiv : ∀ z w : ℤ, (norm q : ℤ) ^ 2 * z = (p : ℤ) * w → (p : ℤ) ∣ z := fun z w h =>
    hcopZ.dvd_of_dvd_mul_left ⟨w, h⟩
  apply hv
  rw [intDvd_iff_coords p v hodd]
  exact ⟨hdiv _ _ (congrArg HQ.a h1), hdiv _ _ (congrArg HQ.b h1),
    hdiv _ _ (congrArg HQ.c h1), hdiv _ _ (congrArg HQ.d h1)⟩

/-- General odd `s` lifting: for odd `s ≥ 1` and pure vector `v = ofVec x y z` not divisible by any
prime dividing `s`, there exist `≥ φ(s)` pairwise non-left-associate Hurwitz quaternions `q` of norm `s`
such that `q * v * conj q` is not divisible by any prime dividing `s`. -/
lemma exists_odd_lifts {s : ℕ} (hs : Odd s) :
    ∀ (x y z : ℤ), (∀ p : ℕ, p.Prime → p ∣ s → ¬ intDvd p (ofVec x y z)) →
      ∃ S : Finset HQ,
        Nat.totient s ≤ S.card ∧
        (∀ q ∈ S, norm q = s ∧ ∀ p : ℕ, p.Prime → p ∣ s → ¬ intDvd p (q * ofVec x y z * conj q)) ∧
        (∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ u : HQ, norm u = 1 → q₁ = u * q₂ → q₁ = q₂) := by
  classical
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro x y z hprim
    by_cases hs1 : s = 1
    · subst hs1
      refine ⟨{1}, by simp, ?_, by simp⟩
      intro q hq; rw [Finset.mem_singleton.mp hq]
      exact ⟨norm_one, fun p hp hp1 => absurd hp1 hp.not_dvd_one⟩
    · have hspos : 0 < s := by obtain ⟨k, rfl⟩ := hs; omega
      obtain ⟨p, hp, hps⟩ := Nat.exists_prime_and_dvd hs1
      haveI : Fact p.Prime := ⟨hp⟩
      have hp2 : p ≠ 2 := by
        intro h; subst h; obtain ⟨k, hk⟩ := hps; obtain ⟨m, hm⟩ := hs; omega
      set e := s.factorization p
      have he : 1 ≤ e := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp
        ((Nat.support_factorization s).symm ▸ Nat.mem_primeFactors.mpr ⟨hp, hps, hspos.ne'⟩))
      have hpe_dvd : p ^ e ∣ s := Nat.ordProj_dvd s p
      obtain ⟨s', hs'eq⟩ := hpe_dvd
      have hp_ndvd_s' : ¬ p ∣ s' := by
        intro h
        have h1 : p ^ (e + 1) ∣ s := by rw [hs'eq, pow_succ]; exact mul_dvd_mul_left (p ^ e) h
        have hle := (hp.pow_dvd_iff_le_factorization hspos.ne').mp h1
        omega
      have hcop : Nat.Coprime (p ^ e) s' :=
        (hp.coprime_iff_not_dvd.mpr hp_ndvd_s').pow_left e
      have hs'odd : Odd s' := by
        rcases Nat.even_or_odd s' with ⟨k, rfl⟩ | h
        · obtain ⟨m, hm⟩ := hs; rw [hs'eq] at hm
          have : p ^ e * (k + k) = 2 * (p ^ e * k) := by ring
          omega
        · exact h
      have hs'lt : s' < s := by
        have hpe_gt : 1 < p ^ e := one_lt_pow₀ hp.one_lt (by omega)
        have hs'pos : 0 < s' := by obtain ⟨k, rfl⟩ := hs'odd; omega
        rw [hs'eq]; nlinarith
      -- Apply IH to s'
      have hprim_s' : ∀ l : ℕ, l.Prime → l ∣ s' → ¬ intDvd l (ofVec x y z) := fun l hl hls' =>
        hprim l hl (hs'eq ▸ dvd_mul_of_dvd_right hls' (p ^ e))
      obtain ⟨S', hS'card, hS'prop, hS'nla⟩ := ih s' hs'lt hs'odd x y z hprim_s'
      -- For each q' ∈ S', q' * v * conj q' = ofVec x' y' z' is primitive at p -> apply exists_prime_pow_lifts
      have hlift_for : ∀ q' ∈ S', ∃ Sp : Finset HQ,
          Nat.totient (p ^ e) ≤ Sp.card ∧
          (∀ qp ∈ Sp, norm qp = p ^ e ∧ ¬ intDvd p qp ∧
            ¬ intDvd p ((qp * q') * ofVec x y z * conj (qp * q'))) ∧
          (∀ qp₁ ∈ Sp, ∀ qp₂ ∈ Sp, ∀ u : HQ, norm u = 1 → qp₁ = u * qp₂ → qp₁ = qp₂) := by
        intro q' hq'
        obtain ⟨x', y', z', hv'⟩ := conj_ofVec_is_ofVec q' x y z
        have hprim_p' : ¬ intDvd p (ofVec x' y' z') := by
          rw [← hv']
          exact not_intDvd_conj_of_coprime hp hp2
            (by rw [(hS'prop q' hq').1]; exact hp.coprime_iff_not_dvd.mpr hp_ndvd_s')
            (hprim p hp hps)
        obtain ⟨Sp, hSpc, hSpp, hSpn⟩ := exists_prime_pow_lifts hp2 e he x' y' z' hprim_p'
        refine ⟨Sp, hSpc, fun qp hqp => ⟨(hSpp qp hqp).1, (hSpp qp hqp).2.1, ?_⟩, hSpn⟩
        have hconj : (qp * q') * ofVec x y z * conj (qp * q') = qp * ofVec x' y' z' * conj qp := by
          rw [conj_mul, ← hv']; noncomm_ring
        rw [hconj]; exact (hSpp qp hqp).2.2
      choose Sp hSp_card hSp_prop hSp_nla using hlift_for
      let pairs := S'.attach.sigma fun q' => Sp q'.1 q'.2
      let f : ((q' : {x // x ∈ S'}) × HQ) → HQ := fun t => t.2 * t.1.1
      -- Helper: ¬ intDvd l (qp * q') for all l ∣ s'
      have hpair_prim_s' : ∀ t ∈ pairs, ∀ l : ℕ, l.Prime → l ∣ s' →
          ¬ intDvd l (f t * ofVec x y z * conj (f t)) := by
        intro t ht l hl hls'
        rcases t with ⟨⟨q', hq'⟩, qp⟩
        have hqp : qp ∈ Sp q' hq' := (Finset.mem_sigma.mp ht).2
        dsimp only [f]
        have hl2 : l ≠ 2 := by
          intro h; subst h; obtain ⟨k, hk⟩ := hls'; obtain ⟨m, hm⟩ := hs'odd; omega
        have hl_ne_p : l ≠ p := fun h => hp_ndvd_s' (h ▸ hls')
        have hcop_l : Nat.Coprime l (norm qp) := by
          rw [(hSp_prop q' hq' qp hqp).1]
          exact ((Nat.coprime_primes hl hp).mpr hl_ne_p).pow_right e
        have hconj : (qp * q') * ofVec x y z * conj (qp * q') =
            qp * (q' * ofVec x y z * conj q') * conj qp := by
          rw [conj_mul]; noncomm_ring
        rw [hconj]
        exact not_intDvd_conj_of_coprime hl hl2 hcop_l ((hS'prop q' hq').2 l hl hls')
      -- Pairwise non-left-associate on pairs
      have hpair_nla : ∀ t₁ ∈ pairs, ∀ t₂ ∈ pairs, ∀ u : HQ, norm u = 1 →
          f t₁ = u * f t₂ → t₁ = t₂ := by
        intro t₁ ht₁ t₂ ht₂ u hun heq
        rcases t₁ with ⟨⟨q₁', hq₁'⟩, qp₁⟩
        rcases t₂ with ⟨⟨q₂', hq₂'⟩, qp₂⟩
        have hqp₁ : qp₁ ∈ Sp q₁' hq₁' := (Finset.mem_sigma.mp ht₁).2
        have hqp₂ : qp₂ ∈ Sp q₂' hq₂' := (Finset.mem_sigma.mp ht₂).2
        dsimp only [f] at heq
        -- conj (qp₁ * q₁') = conj q₁' * conj qp₁ = conj q₂' * (conj qp₂ * conj u)
        have hc1 : conj (qp₁ * q₁') = conj q₁' * conj qp₁ := conj_mul _ _
        have hc2 : conj (qp₁ * q₁') = conj q₂' * (conj qp₂ * conj u) := by
          rw [heq, conj_mul, conj_mul, mul_assoc]
        have hprim_c : ∀ l : ℕ, l.Prime → l ∣ s' → ¬ intDvd l (conj (qp₁ * q₁')) := by
          intro l hl hls' ⟨t, ht⟩
          apply hpair_prim_s' ⟨⟨q₁', hq₁'⟩, qp₁⟩ ht₁ l hl hls'
          have h1 : qp₁ * q₁' = ofInt (l : ℤ) * conj t := by
            have := congrArg conj ht
            rw [conj_conj, conj_mul, conj_ofInt, mul_ofInt] at this; exact this
          refine ⟨conj t * ofVec x y z * conj (qp₁ * q₁'), ?_⟩
          dsimp only [f]; rw [h1]; noncomm_ring
        obtain ⟨u₀, hu₀n, hq2c⟩ := unique_left_divisor hs'odd hprim_c
          ⟨conj qp₁, hc1⟩ ⟨conj qp₂ * conj u, hc2⟩
          (by rw [norm_conj, (hS'prop q₁' hq₁').1]) (by rw [norm_conj, (hS'prop q₂' hq₂').1])
        have hq2eq : q₂' = conj u₀ * q₁' := by
          have := congrArg conj hq2c
          rw [conj_conj, conj_mul, conj_conj] at this; exact this
        have hqeq : q₂' = q₁' := hS'nla q₂' hq₂' q₁' hq₁' (conj u₀) (by rwa [norm_conj]) hq2eq
        rcases hqeq with rfl
        have hq1ne : q₂' ≠ 0 := fun h => by
          have := (hS'prop q₂' hq₁').1; rw [h, (norm_eq_zero_iff 0).mpr rfl] at this
          obtain ⟨k, hk⟩ := hs'odd; omega
        have hqpeq : qp₁ = u * qp₂ :=
          mul_right_cancel_of_ne_zero hq1ne (by rw [heq, mul_assoc])
        have hqpeq' : qp₁ = qp₂ := hSp_nla q₂' hq₁' qp₁ hqp₁ qp₂ hqp₂ u hun hqpeq
        subst hqpeq'; rfl
      have hfinj : Set.InjOn f pairs := fun t₁ ht₁ t₂ ht₂ heq =>
        hpair_nla t₁ ht₁ t₂ ht₂ 1 norm_one (by simpa using heq)
      refine ⟨pairs.image f, ?_, ?_, ?_⟩
      · rw [Finset.card_image_of_injOn hfinj, Finset.card_sigma, hs'eq, Nat.totient_mul hcop]
        calc Nat.totient (p ^ e) * Nat.totient s'
            = Nat.totient s' * Nat.totient (p ^ e) := mul_comm _ _
          _ ≤ S'.card * Nat.totient (p ^ e) := Nat.mul_le_mul_right _ hS'card
          _ = ∑ _q' ∈ S'.attach, Nat.totient (p ^ e) := by
                rw [Finset.sum_const, Finset.card_attach, smul_eq_mul]
          _ ≤ ∑ q' ∈ S'.attach, (Sp q'.1 q'.2).card :=
                Finset.sum_le_sum fun q' _ => hSp_card q'.1 q'.2
      · intro q hq
        rw [Finset.mem_image] at hq
        obtain ⟨t, ht, rfl⟩ := hq
        rcases t with ⟨⟨q', hq'⟩, qp⟩
        have hqp : qp ∈ Sp q' hq' := (Finset.mem_sigma.mp ht).2
        refine ⟨by dsimp only [f]; rw [norm_mul, (hSp_prop q' hq' qp hqp).1, (hS'prop q' hq').1, ← hs'eq], ?_⟩
        intro l hl hls
        rw [hs'eq] at hls
        rcases hl.dvd_mul.mp hls with hlpe | hls'
        · have hlp : l = p := (Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow hlpe)
          subst hlp; exact (hSp_prop q' hq' qp hqp).2.2
        · exact hpair_prim_s' ⟨⟨q', hq'⟩, qp⟩ ht l hl hls'
      · intro q₁ hq₁ q₂ hq₂ u hun heq
        rw [Finset.mem_image] at hq₁ hq₂
        obtain ⟨t₁, ht₁, rfl⟩ := hq₁
        obtain ⟨t₂, ht₂, rfl⟩ := hq₂
        rw [hpair_nla t₁ ht₁ t₂ ht₂ u hun heq]

/-- Finset of all signed integer representations `(x, y, z) ∈ ℤ³` with `x² + y² + z² = m`. -/
noncomputable def rep3Z (m : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  let box := Finset.Icc (-(m : ℤ)) (m : ℤ)
  (box ×ˢ (box ×ˢ box)).filter fun v => v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = (m : ℤ)

lemma mem_rep3Z_iff (m : ℕ) (v : ℤ × ℤ × ℤ) :
    v ∈ rep3Z m ↔ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = (m : ℤ) := by
  simp only [rep3Z, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_iff_right_iff_imp]
  intro h
  have h1 : -(m : ℤ) ≤ v.1 ∧ v.1 ≤ (m : ℤ) := by
    have hsq : v.1 ^ 2 ≤ (m : ℤ) := by nlinarith [sq_nonneg v.2.1, sq_nonneg v.2.2]
    exact ⟨by nlinarith [sq_nonneg (v.1 + 1)], by nlinarith [sq_nonneg (v.1 - 1)]⟩
  have h2 : -(m : ℤ) ≤ v.2.1 ∧ v.2.1 ≤ (m : ℤ) := by
    have hsq : v.2.1 ^ 2 ≤ (m : ℤ) := by nlinarith [sq_nonneg v.1, sq_nonneg v.2.2]
    exact ⟨by nlinarith [sq_nonneg (v.2.1 + 1)], by nlinarith [sq_nonneg (v.2.1 - 1)]⟩
  have h3 : -(m : ℤ) ≤ v.2.2 ∧ v.2.2 ≤ (m : ℤ) := by
    have hsq : v.2.2 ^ 2 ≤ (m : ℤ) := by nlinarith [sq_nonneg v.1, sq_nonneg v.2.1]
    exact ⟨by nlinarith [sq_nonneg (v.2.2 + 1)], by nlinarith [sq_nonneg (v.2.2 - 1)]⟩
  exact ⟨h1, h2, h3⟩

/-- Main Hurwitz quaternion lifting theorem: for squarefree `d` and odd `s`,
`(rep3Z d).card * Nat.totient s ≤ (rep3Z (d * s ^ 2)).card`. -/
theorem r3_mul_sq_ge_mul_totient {d s : ℕ} (hd_sf : Squarefree d) (hs : Odd s) :
    (rep3Z d).card * Nat.totient s ≤ (rep3Z (d * s ^ 2)).card := by
  classical
  -- Every v ∈ rep3Z d is not divisible by any prime p (since d is squarefree!)
  have hprim_v : ∀ v ∈ rep3Z d, ∀ p : ℕ, p.Prime → p ∣ s → ¬ intDvd p (ofVec v.1 v.2.1 v.2.2) := by
    intro v hv p hp hps ⟨t, ht⟩
    have hnd : norm (ofVec v.1 v.2.1 v.2.2) = d := by
      have h1 := norm_ofVec v.1 v.2.1 v.2.2
      rw [(mem_rep3Z_iff d v).mp hv] at h1
      exact_mod_cast h1
    have hsq : p ^ 2 ∣ d := by
      rw [← hnd, ht, norm_mul, norm_ofInt]
      exact dvd_mul_right _ _
    exact hp.not_isUnit (hd_sf p (by simpa [sq] using hsq))
  -- For each v ∈ rep3Z d, get S(v) of size ≥ φ(s) pairwise non-left-associate
  choose S hScard hSprop hSnla using fun (v : {x // x ∈ rep3Z d}) =>
    exists_odd_lifts hs v.1.1 v.1.2.1 v.1.2.2 (hprim_v v.1 v.2)
  -- Expand S(v) by left multiplication by the 24 Hurwitz units -> T(v) of size ≥ 24 * φ(s)
  let T (v : {x // x ∈ rep3Z d}) : Finset HQ := (unitsFinset ×ˢ S v).image fun p => p.1 * p.2
  have hTcard : ∀ v : {x // x ∈ rep3Z d}, 24 * Nat.totient s ≤ (T v).card := by
    intro v
    have hinj : Set.InjOn (fun p : HQ × HQ => p.1 * p.2) ((unitsFinset ×ˢ S v : Finset (HQ × HQ)) : Set (HQ × HQ)) := by
      intro p₁ hp₁ p₂ hp₂ heq
      rw [Finset.mem_coe, Finset.mem_product] at hp₁ hp₂
      have hu₁ : norm p₁.1 = 1 := (mem_unitsFinset_iff _).mp hp₁.1
      have hu₂ : norm p₂.1 = 1 := (mem_unitsFinset_iff _).mp hp₂.1
      dsimp only at heq
      have hq2eq : p₂.2 = (conj p₂.1 * p₁.1) * p₁.2 := by
        calc p₂.2 = (conj p₂.1 * p₂.1) * p₂.2 := by rw [conj_mul_self, hu₂, Nat.cast_one, ofInt_one, one_mul]
          _ = conj p₂.1 * (p₂.1 * p₂.2) := mul_assoc _ _ _
          _ = conj p₂.1 * (p₁.1 * p₁.2) := by rw [heq]
          _ = (conj p₂.1 * p₁.1) * p₁.2 := (mul_assoc _ _ _).symm
      have h2eq : p₂.2 = p₁.2 := hSnla v p₂.2 hp₂.2 p₁.2 hp₁.2 (conj p₂.1 * p₁.1)
        (by rw [norm_mul, norm_conj, hu₂, hu₁, mul_one]) hq2eq
      have hq1ne : p₁.2 ≠ 0 := fun h => by
        have := (hSprop v p₁.2 hp₁.2).1; rw [h, (norm_eq_zero_iff 0).mpr rfl] at this
        obtain ⟨k, hk⟩ := hs; omega
      have h1eq : p₁.1 = p₂.1 := mul_right_cancel_of_ne_zero hq1ne (by rw [heq, h2eq])
      exact Prod.ext h1eq h2eq.symm
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, card_unitsFinset]
    exact Nat.mul_le_mul_left 24 (hScard v)
  have hTprop : ∀ (v : {x // x ∈ rep3Z d}) (q : HQ), q ∈ T v →
      norm q = s ∧ ∀ p : ℕ, p.Prime → p ∣ s → ¬ intDvd p (q * ofVec v.1.1 v.1.2.1 v.1.2.2 * conj q) := by
    intro v q hq
    rw [Finset.mem_image] at hq
    obtain ⟨⟨u, q₀⟩, hmem, rfl⟩ := hq
    rw [Finset.mem_product] at hmem
    have hun : norm u = 1 := (mem_unitsFinset_iff _).mp hmem.1
    refine ⟨by rw [norm_mul, hun, one_mul, (hSprop v q₀ hmem.2).1], ?_⟩
    intro p hp hps ⟨t, ht⟩
    apply (hSprop v q₀ hmem.2).2 p hp hps
    refine ⟨conj u * t * u, ?_⟩
    have huc : conj u * u = 1 := by rw [conj_mul_self, hun, Nat.cast_one, ofInt_one]
    have hcu : u * conj u = 1 := by rw [mul_conj_self, hun, Nat.cast_one, ofInt_one]
    calc q₀ * ofVec v.1.1 v.1.2.1 v.1.2.2 * conj q₀
        = (conj u * u) * (q₀ * ofVec v.1.1 v.1.2.1 v.1.2.2 * conj q₀) * (conj u * u) := by
            rw [huc, one_mul, mul_one]
      _ = conj u * ((u * q₀) * ofVec v.1.1 v.1.2.1 v.1.2.2 * conj (u * q₀)) * u := by
            rw [conj_mul]; noncomm_ring
      _ = conj u * (ofInt (p : ℤ) * t) * u := by rw [ht]
      _ = ofInt (p : ℤ) * (conj u * t * u) := by
            rw [← mul_assoc (conj u), mul_ofInt]; noncomm_ring
  -- Define total domain and map Φ : Σ v, T v → rep3Z (d * s^2)
  let Dom := (rep3Z d).attach.sigma T
  let Φ : ((v : {x // x ∈ rep3Z d}) × HQ) → ℤ × ℤ × ℤ := fun t =>
    let w := t.2 * ofVec t.1.1.1 t.1.1.2.1 t.1.1.2.2 * conj t.2
    (w.b / 2, w.c / 2, w.d / 2)
  have hΦ_vec : ∀ t : ((v : {x // x ∈ rep3Z d}) × HQ),
      ofVec (Φ t).1 (Φ t).2.1 (Φ t).2.2 = t.2 * ofVec t.1.1.1 t.1.1.2.1 t.1.1.2.2 * conj t.2 := by
    intro t
    obtain ⟨x', y', z', h⟩ := conj_ofVec_is_ofVec t.2 t.1.1.1 t.1.1.2.1 t.1.1.2.2
    dsimp only [Φ]
    rw [h]
    apply HQ.ext <;> simp [ofVec]
  have hΦ_mem : ∀ t ∈ Dom, Φ t ∈ rep3Z (d * s ^ 2) := by
    intro t ht
    have hqt : t.2 ∈ T t.1 := (Finset.mem_sigma.mp ht).2
    rw [mem_rep3Z_iff, ← norm_ofVec, hΦ_vec]
    have hnd : norm (ofVec t.1.1.1 t.1.1.2.1 t.1.1.2.2) = d := by
      have h1 := norm_ofVec t.1.1.1 t.1.1.2.1 t.1.1.2.2
      rw [(mem_rep3Z_iff d t.1.1).mp t.1.2] at h1
      exact_mod_cast h1
    rw [norm_mul, norm_mul, norm_conj, (hTprop t.1 t.2 hqt).1, hnd]
    push_cast; ring
  -- Bound every fiber size by ≤ 24 using unique_left_divisor!
  have hfiber : ∀ w ∈ rep3Z (d * s ^ 2), (Dom.filter fun t => Φ t = w).card ≤ 24 := by
    intro w _
    by_cases hemp : (Dom.filter fun t => Φ t = w).Nonempty
    · obtain ⟨t₀, ht₀⟩ := hemp
      obtain ⟨ht₀Dom, hΦ₀⟩ := Finset.mem_filter.mp ht₀
      have hqt₀ : t₀.2 ∈ T t₀.1 := (Finset.mem_sigma.mp ht₀Dom).2
      have hw_eq : ofVec w.1 w.2.1 w.2.2 = t₀.2 * ofVec t₀.1.1.1 t₀.1.1.2.1 t₀.1.1.2.2 * conj t₀.2 := by
        rw [← hΦ₀, hΦ_vec]
      -- Every t in the fiber has t.2 = t₀.2 * u for a unique u ∈ unitsFinset, and t.1 is uniquely determined by t.2!
      have hinj_q : ∀ t ∈ Dom.filter (fun t => Φ t = w), ∃ u ∈ unitsFinset, t.2 = t₀.2 * u := by
        intro t ht
        obtain ⟨htDom, hΦt⟩ := Finset.mem_filter.mp ht
        have hqt : t.2 ∈ T t.1 := (Finset.mem_sigma.mp htDom).2
        have hwt : ofVec w.1 w.2.1 w.2.2 = t.2 * ofVec t.1.1.1 t.1.1.2.1 t.1.1.2.2 * conj t.2 := by
          rw [← hΦt, hΦ_vec]
        have hprim_w : ∀ p : ℕ, p.Prime → p ∣ s → ¬ intDvd p (ofVec w.1 w.2.1 w.2.2) := by
          rw [hw_eq]; exact (hTprop t₀.1 t₀.2 hqt₀).2
        obtain ⟨u, hun, hu_eq⟩ := unique_left_divisor hs hprim_w
          ⟨ofVec t₀.1.1.1 t₀.1.1.2.1 t₀.1.1.2.2 * conj t₀.2, by rw [hw_eq, mul_assoc]⟩
          ⟨ofVec t.1.1.1 t.1.1.2.1 t.1.1.2.2 * conj t.2, by rw [hwt, mul_assoc]⟩
          (hTprop t₀.1 t₀.2 hqt₀).1 (hTprop t.1 t.2 hqt).1
        exact ⟨u, (mem_unitsFinset_iff u).mpr hun, hu_eq⟩
      have hq_inj : Set.InjOn (fun t : ((v : {x // x ∈ rep3Z d}) × HQ) => t.2)
          (Dom.filter fun t => Φ t = w) := by
        intro t₁ ht₁ t₂ ht₂ hqeq
        obtain ⟨ht₁Dom, hΦ₁⟩ := Finset.mem_filter.mp ht₁
        obtain ⟨ht₂Dom, hΦ₂⟩ := Finset.mem_filter.mp ht₂
        have hqne : t₁.2 ≠ 0 := fun h => by
          have := (hTprop t₁.1 t₁.2 (Finset.mem_sigma.mp ht₁Dom).2).1
          rw [h, (norm_eq_zero_iff 0).mpr rfl] at this
          obtain ⟨k, hk⟩ := hs; omega
        have hcqne : conj t₁.2 ≠ 0 := fun h => by
          have := congrArg conj h; rw [conj_conj, conj_zero] at this; exact hqne this
        have hveq : ofVec t₁.1.1.1 t₁.1.1.2.1 t₁.1.1.2.2 = ofVec t₂.1.1.1 t₂.1.1.2.1 t₂.1.1.2.2 := by
          dsimp only at hqeq
          have h1 : t₁.2 * ofVec t₁.1.1.1 t₁.1.1.2.1 t₁.1.1.2.2 * conj t₁.2 =
              t₁.2 * ofVec t₂.1.1.1 t₂.1.1.2.1 t₂.1.1.2.2 * conj t₁.2 := by
            rw [← hΦ_vec t₁, hΦ₁, ← hΦ₂, hΦ_vec t₂, hqeq]
          exact mul_left_cancel_of_ne_zero hqne (mul_right_cancel_of_ne_zero hcqne h1)
        rcases t₁ with ⟨⟨⟨x₁, y₁, z₁⟩, h₁⟩, q₁⟩
        rcases t₂ with ⟨⟨⟨x₂, y₂, z₂⟩, h₂⟩, q₂⟩
        dsimp only at hveq hqeq
        have hb := congrArg HQ.b hveq
        have hc := congrArg HQ.c hveq
        have hd := congrArg HQ.d hveq
        simp only [ofVec] at hb hc hd
        have hx : x₁ = x₂ := by omega
        have hy : y₁ = y₂ := by omega
        have hz : z₁ = z₂ := by omega
        subst hx hy hz hqeq; rfl
      calc (Dom.filter fun t => Φ t = w).card
          = ((Dom.filter fun t => Φ t = w).image fun t => t.2).card :=
              (Finset.card_image_of_injOn hq_inj).symm
        _ ≤ (unitsFinset.image fun u => t₀.2 * u).card := by
              refine Finset.card_le_card fun q hq => ?_
              rw [Finset.mem_image] at hq ⊢
              obtain ⟨t, ht, rfl⟩ := hq
              obtain ⟨u, hu, heq⟩ := hinj_q t ht
              exact ⟨u, hu, heq.symm⟩
        _ ≤ unitsFinset.card := Finset.card_image_le
        _ = 24 := card_unitsFinset
    · rw [Finset.not_nonempty_iff_eq_empty.mp hemp]; simp
  -- Double count Dom via fibers of Φ
  have hcount : Dom.card ≤ 24 * (rep3Z (d * s ^ 2)).card := by
    have hmaps : ∀ t ∈ Dom, Φ t ∈ rep3Z (d * s ^ 2) := hΦ_mem
    have hsum := Finset.card_eq_sum_card_fiberwise hmaps
    rw [hsum]
    calc ∑ w ∈ rep3Z (d * s ^ 2), (Dom.filter fun t => Φ t = w).card
        ≤ ∑ _w ∈ rep3Z (d * s ^ 2), 24 := Finset.sum_le_sum hfiber
      _ = 24 * (rep3Z (d * s ^ 2)).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hDom_ge : 24 * ((rep3Z d).card * Nat.totient s) ≤ Dom.card := by
    rw [Finset.card_sigma]
    calc 24 * ((rep3Z d).card * Nat.totient s)
        = (rep3Z d).card * (24 * Nat.totient s) := by ring
      _ = ∑ _v ∈ (rep3Z d).attach, (24 * Nat.totient s) := by
            rw [Finset.sum_const, Finset.card_attach, smul_eq_mul]
      _ ≤ ∑ v ∈ (rep3Z d).attach, (T v).card := Finset.sum_le_sum fun v _ => hTcard v
  omega

end HQ

end E940.QuaternionLift

end ModQuaternionLift

section ModSiegel

open Complex Real Filter Topology Finset BigOperators
open scoped ComplexOrder

namespace E940.Siegel

/-!
### Part 1: Abel summation and analytic continuation bounds for `LFunction χ`
-/

/-- Partial sums of a nontrivial Dirichlet character are bounded by its modulus. -/
lemma norm_char_partialSum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 N, χ k‖ ≤ (q : ℝ) := by
  have hqpos : 0 < q := NeZero.pos q
  have hzero : ∑ j : ZMod q, χ j = 0 := χ.sum_eq_zero_of_ne_one hχ
  have hblock : ∀ m : ℕ, ∑ k ∈ Finset.Ico (m * q + 1) ((m + 1) * q + 1), χ k = 0 := by
    intro m
    have hmq : (m + 1) * q = m * q + q := by ring
    have hbij : ∑ k ∈ Finset.Ico (m * q + 1) ((m + 1) * q + 1), χ k =
        ∑ r ∈ Finset.range q, χ ((m * q + 1 + r : ℕ) : ZMod q) := by
      refine Finset.sum_bij (fun k _ => k - (m * q + 1)) ?_ ?_ ?_ ?_
      · intro k hk; rw [Finset.mem_Ico] at hk; rw [Finset.mem_range]; omega
      · intro a ha b hb hab; rw [Finset.mem_Ico] at ha hb; omega
      · intro r hr; rw [Finset.mem_range] at hr
        exact ⟨m * q + 1 + r, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk; rw [Finset.mem_Ico] at hk
        congr 1; congr 1; omega
    rw [hbij]
    have hshift : ∑ r ∈ Finset.range q, χ ((m * q + 1 + r : ℕ) : ZMod q) =
        ∑ j : ZMod q, χ j := by
      have heq : (fun r : ℕ => χ ((m * q + 1 + r : ℕ) : ZMod q)) =
          (fun r : ℕ => χ ((r + 1 : ℕ) : ZMod q)) := by
        ext r; congr 1; push_cast; simp [add_comm]
      rw [heq, ← Finset.sum_coe_sort (Finset.range q)]
      refine Fintype.sum_equiv
        (Equiv.ofBijective (fun r : Finset.range q => ((r.1 + 1 : ℕ) : ZMod q)) ?_)
        _ _ (fun _ => rfl)
      constructor
      · intro a b hab
        have ha := Finset.mem_range.mp a.2
        have hb := Finset.mem_range.mp b.2
        have hmod : (a.1 + 1) % q = (b.1 + 1) % q :=
          (ZMod.natCast_eq_natCast_iff' (a.1 + 1) (b.1 + 1) q).mp hab
        apply Subtype.ext
        by_cases ha1 : a.1 + 1 = q
        · by_cases hb1 : b.1 + 1 = q
          · omega
          · rw [ha1, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hmod; omega
        · by_cases hb1 : b.1 + 1 = q
          · rw [hb1, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hmod; omega
          · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod; omega
      · intro z
        by_cases hz : z.val = 0
        · refine ⟨⟨q - 1, Finset.mem_range.mpr (by omega)⟩, ?_⟩
          dsimp only
          rw [show q - 1 + 1 = q by omega, ZMod.natCast_self]
          exact ((ZMod.val_eq_zero z).mp hz).symm
        · refine ⟨⟨z.val - 1, Finset.mem_range.mpr (by have := z.val_lt; omega)⟩, ?_⟩
          dsimp only
          rw [show z.val - 1 + 1 = z.val by omega, ZMod.natCast_zmod_val]
    rw [hshift, hzero]
  have hfull : ∀ M : ℕ, ∑ k ∈ Finset.Ico 1 (M * q + 1), χ k = 0 := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have hmq : (M + 1) * q = M * q + q := by ring
      have hsplit : Finset.Ico 1 ((M + 1) * q + 1) =
          Finset.Ico 1 (M * q + 1) ∪ Finset.Ico (M * q + 1) ((M + 1) * q + 1) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
      rw [hsplit, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 1 (M * q + 1) ((M + 1) * q + 1)),
        ih, hblock M, add_zero]
  set M := N / q with hMdef
  have hdiv : N = M * q + N % q := by
    rw [hMdef, mul_comm]
    exact (Nat.div_add_mod N q).symm
  have hmodlt : N % q < q := Nat.mod_lt N hqpos
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := rfl
  have hsplit : Finset.Ico 1 (N + 1) = Finset.Ico 1 (M * q + 1) ∪ Finset.Ico (M * q + 1) (N + 1) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
  rw [hIcc, hsplit, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 1 (M * q + 1) (N + 1)),
    hfull M, zero_add]
  calc ‖∑ k ∈ Finset.Ico (M * q + 1) (N + 1), χ k‖
      ≤ ∑ k ∈ Finset.Ico (M * q + 1) (N + 1), ‖χ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Ico (M * q + 1) (N + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => χ.norm_le_one _
    _ = ((Finset.Ico (M * q + 1) (N + 1)).card : ℝ) := by simp
    _ ≤ (q : ℝ) := by
        rw [Nat.card_Ico]
        exact_mod_cast (show N + 1 - (M * q + 1) ≤ q by omega)

/-- Mean value bound on `((n+1):ℂ)^(-s) - ((n+2):ℂ)^(-s)`. -/
lemma norm_cpow_neg_sub_le (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ‖((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)‖ ≤
      ‖s‖ * ((n + 1 : ℝ) ^ (-(s.re + 1))) := by
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ (-s)
  have hsne : -s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hdiff : ∀ t ∈ Set.Icc ((n + 1 : ℝ)) ((n + 2 : ℝ)),
      HasDerivAt f ((-s) * (t : ℂ) ^ (-s - 1)) t := by
    intro t ht
    have htpos : 0 < t := by linarith [ht.1, show (0 : ℝ) < (n + 1 : ℝ) by positivity]
    have h1 := hasDerivAt_ofReal_cpow_const (x := t) htpos.ne' (r := -s) hsne
    simpa [f, mul_comm] using h1
  have hbound : ∀ t ∈ Set.Icc ((n + 1 : ℝ)) ((n + 2 : ℝ)),
      ‖(-s) * (t : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * ((n + 1 : ℝ) ^ (-(s.re + 1))) := by
    intro t ht
    have htpos : 0 < t := by linarith [ht.1, show (0 : ℝ) < (n + 1 : ℝ) by positivity]
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    simp only [sub_re, neg_re, one_re]
    have hexp : -s.re - 1 = -(s.re + 1) := by ring
    rw [hexp]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
    exact Real.rpow_le_rpow_of_nonpos (by positivity) ht.1 (by linarith)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hdiff t ht).hasDerivWithinAt) hbound (convex_Icc _ _)
    (Set.right_mem_Icc.mpr (by linarith : (n + 1 : ℝ) ≤ n + 2))
    (Set.left_mem_Icc.mpr (by linarith : (n + 1 : ℝ) ≤ n + 2))
  have h1 : f (n + 1 : ℝ) = ((n + 1 : ℕ) : ℂ) ^ (-s) := by simp [f]
  have h2 : f (n + 2 : ℝ) = ((n + 2 : ℕ) : ℂ) ^ (-s) := by simp [f]
  rw [h1, h2] at hmvt
  have hdist : ‖(n + 1 : ℝ) - (n + 2 : ℝ)‖ = 1 := by
    rw [show (n + 1 : ℝ) - (n + 2 : ℝ) = -1 by ring, norm_neg, norm_one]
  rw [hdist, mul_one] at hmvt
  exact hmvt

/-- Partial sums of `S(n+1) * ((n+1)^(-s) - (n+2)^(-s))` telescope to `∑ χ(k)/k^s`. -/
lemma abel_partial_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (∑ k ∈ Finset.Icc 1 (n + 1), χ k) *
        (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)) =
      (∑ k ∈ Finset.Icc 1 N, χ k * ((k : ℂ) ^ (-s))) -
        (∑ k ∈ Finset.Icc 1 N, χ k) * (((N + 1 : ℕ) : ℂ) ^ (-s)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem : N + 1 ∉ Finset.Icc 1 N := by simp
    rw [hIcc, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem]
    ring

/-- Helper: `∑ (n + 1 : ℝ)^(-p)` is summable for `p > 1`. -/
lemma summable_nat_add_one_rpow_neg {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ => ((n + 1 : ℝ) ^ (-p))) := by
  have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ (-p))) := by
    rw [Real.summable_nat_rpow]; linarith
  have h2 := (summable_nat_add_iff 1).mpr h1
  simpa [Nat.cast_add, Nat.cast_one] using h2

/-- Helper: telescoping sum `∑ (n + 1 + c)⁻¹ - (n + 2 + c)⁻¹ = (c + 1)⁻¹`. -/
lemma hasSum_inv_sub_inv_shift (c : ℕ) :
    HasSum (fun n : ℕ => (((n + c + 1 : ℝ)⁻¹) - ((n + c + 2 : ℝ)⁻¹))) (((c + 1 : ℝ)⁻¹)) := by
  have hnonneg : ∀ n : ℕ, 0 ≤ (((n + c + 1 : ℝ)⁻¹) - ((n + c + 2 : ℝ)⁻¹)) := fun n =>
    sub_nonneg.mpr (inv_anti₀ (by positivity) (by linarith))
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, (((n + c + 1 : ℝ)⁻¹) - ((n + c + 2 : ℝ)⁻¹)) =
      ((c + 1 : ℝ)⁻¹) - ((N + c + 1 : ℝ)⁻¹) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast; ring
  simp_rw [hpart]
  have hlim : Tendsto (fun N : ℕ => ((N + c + 1 : ℝ)⁻¹)) atTop (𝓝 0) := by
    refine tendsto_inv_atTop_zero.comp ?_
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) + ((c : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    convert h1 using 1; ext N; ring
  simpa using tendsto_const_nhds.sub hlim

/-- The Abel-summed series equals `DirichletCharacter.LFunction χ s` for all `0 < s.re`. -/
lemma LFunction_eq_abel_tsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s =
      ∑' n : ℕ, (∑ k ∈ Finset.Icc 1 (n + 1), χ k) *
        (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)) := by
  let S : ℕ → ℂ := fun n => ∑ k ∈ Finset.Icc 1 (n + 1), χ k
  let term : ℕ → ℂ → ℂ := fun n z => S n * (((n + 1 : ℕ) : ℂ) ^ (-z) - ((n + 2 : ℕ) : ℂ) ^ (-z))
  let g : ℂ → ℂ := fun z => ∑' n : ℕ, term n z
  have hterm_bound : ∀ (n : ℕ) (z : ℂ), 0 < z.re →
      ‖term n z‖ ≤ (q : ℝ) * ‖z‖ * ((n + 1 : ℝ) ^ (-(z.re + 1))) := by
    intro n z hz
    dsimp only [term, S]
    rw [norm_mul]
    have h1 := norm_char_partialSum_le χ hχ (n + 1)
    have h2 := norm_cpow_neg_sub_le n z hz
    calc ‖∑ k ∈ Finset.Icc 1 (n + 1), χ k‖ * ‖((n + 1 : ℕ) : ℂ) ^ (-z) - ((n + 2 : ℕ) : ℂ) ^ (-z)‖
        ≤ (q : ℝ) * (‖z‖ * ((n + 1 : ℝ) ^ (-(z.re + 1)))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (q : ℝ) * ‖z‖ * ((n + 1 : ℝ) ^ (-(z.re + 1))) := by ring
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUnif : TendstoLocallyUniformlyOn (fun N z => ∑ n ∈ Finset.range N, term n z) g atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hUopen]
    intro K hKU hKcomp
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · simp [tendstoUniformlyOn_empty]
    obtain ⟨z₀, hz₀K, hz₀min⟩ := hKcomp.exists_isMinOn hKne Complex.continuous_re.continuousOn
    obtain ⟨z₁, hz₁K, hz₁max⟩ := hKcomp.exists_isMaxOn hKne continuous_norm.continuousOn
    set δ := z₀.re
    have hδ : 0 < δ := hKU hz₀K
    set R := ‖z₁‖
    have hMsum : Summable (fun n : ℕ => (q : ℝ) * R * ((n + 1 : ℝ) ^ (-(δ + 1)))) :=
      (summable_nat_add_one_rpow_neg (by linarith)).mul_left _
    refine tendstoUniformlyOn_tsum_nat hMsum fun n z hzK => ?_
    have hzδ : δ ≤ z.re := hz₀min hzK
    have hzR : ‖z‖ ≤ R := hz₁max hzK
    calc ‖term n z‖ ≤ (q : ℝ) * ‖z‖ * ((n + 1 : ℝ) ^ (-(z.re + 1))) :=
          hterm_bound n z (lt_of_lt_of_le hδ hzδ)
      _ ≤ (q : ℝ) * R * ((n + 1 : ℝ) ^ (-(δ + 1))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hzR (by positivity))
            (Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith))
            (by positivity) (by positivity)
  have hdiffN : ∀ N : ℕ, DifferentiableOn ℂ (fun z => ∑ n ∈ Finset.range N, term n z) U := by
    intro N
    refine DifferentiableOn.fun_sum fun n _ => ?_
    refine (differentiableOn_const _).mul (DifferentiableOn.sub ?_ ?_)
    · intro z _
      have h1 : 0 < (((n + 1 : ℕ) : ℂ)).re := by simp; positivity
      exact ((differentiableAt_const _).cpow differentiableAt_id.neg (Or.inl h1)).differentiableWithinAt
    · intro z _
      have h2 : 0 < (((n + 2 : ℕ) : ℂ)).re := by simp; positivity
      exact ((differentiableAt_const _).cpow differentiableAt_id.neg (Or.inl h2)).differentiableWithinAt
  have hdiffg : DifferentiableOn ℂ g U :=
    hUnif.differentiableOn (Eventually.of_forall hdiffN) hUopen
  have heq_gt : ∀ z : ℂ, 1 < z.re → DirichletCharacter.LFunction χ z = g z := by
    intro z hz
    rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
    have hsumL : Summable (LSeries.term (fun n : ℕ => χ n) z) :=
      DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz
    have hlimL : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), LSeries.term (fun n : ℕ => χ n) z k)
        atTop (𝓝 (LSeries (fun n : ℕ => χ n) z)) :=
      (hsumL.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have hsumG : Summable (fun n : ℕ => term n z) :=
      Summable.of_norm_bounded ((summable_nat_add_one_rpow_neg (by linarith : 1 < z.re + 1)).mul_left ((q : ℝ) * ‖z‖))
        (fun n => hterm_bound n z (by linarith))
    have hrewrite : ∀ N : ℕ, ∑ n ∈ Finset.range N, term n z =
        (∑ k ∈ Finset.range (N + 1), LSeries.term (fun n : ℕ => χ n) z k) -
          (∑ k ∈ Finset.Icc 1 N, χ k) * (((N + 1 : ℕ) : ℂ) ^ (-z)) := by
      intro N
      rw [abel_partial_sum χ z N]
      congr 1
      have h0 : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [h0, Finset.sum_insert (by simp), LSeries.term_zero, zero_add]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk0 : k ≠ 0 := by rw [Finset.mem_Icc] at hk; omega
      rw [LSeries.term_of_ne_zero hk0, cpow_neg, div_eq_mul_inv]
    have hrem : Tendsto (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, χ k) * (((N + 1 : ℕ) : ℂ) ^ (-z)))
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (g := fun N : ℕ => (q : ℝ) * (((N + 1 : ℕ) : ℝ) ^ (-z.re)))
        (fun _ => norm_nonneg _) (fun N => ?_) ?_
      · rw [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos N), neg_re]
        exact mul_le_mul_of_nonneg_right (norm_char_partialSum_le χ hχ N) (by positivity)
      · have hpow : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ (-z.re)) atTop (𝓝 0) :=
          (tendsto_rpow_neg_atTop (by linarith : 0 < z.re)).comp
            ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
        simpa using hpow.const_mul (q : ℝ)
    have hlimG' : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, term n z)
        atTop (𝓝 (LSeries (fun n : ℕ => χ n) z - 0)) := by
      simpa only [← hrewrite] using hlimL.sub hrem
    rw [sub_zero] at hlimG'
    exact tendsto_nhds_unique hlimG' hsumG.hasSum.tendsto_sum_nat
  have hUconn : IsPreconnected U := Convex.isPreconnected fun x hx y hy a b ha hb hab => by
    simp only [U, Set.mem_ofPred_eq, add_re, real_smul, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at hx hy ⊢
    rcases lt_or_eq_of_le ha with ha' | rfl <;> nlinarith
  have hAnL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hUopen
  have hAng : AnalyticOnNhd ℂ g U := hdiffg.analyticOnNhd hUopen
  have hEqOn : Set.EqOn (DirichletCharacter.LFunction χ) g U := by
    refine hAnL.eqOn_of_preconnected_of_eventuallyEq hAng hUconn (show (2 : ℂ) ∈ U by simp [U]) ?_
    have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hmem] with z hz
    exact heq_gt z hz
  exact hEqOn hs

/-- Elementary upper bound `∑' n : ℕ, (n + 1 : ℝ) ^ (-(3/2 : ℝ)) ≤ 3`. -/
lemma tsum_rpow_neg_three_halves_le :
    ∑' n : ℕ, ((n + 1 : ℝ) ^ (-(3 / 2 : ℝ))) ≤ 3 := by
  have hsum : Summable (fun n : ℕ => ((n + 1 : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    summable_nat_add_one_rpow_neg (by norm_num)
  have hstep : ∀ n : ℕ, ((n + 2 : ℝ) ^ (-(3 / 2 : ℝ))) ≤
      2 * ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) - (n + 2 : ℝ) ^ (-(1 / 2 : ℝ))) := by
    intro n
    have ha : (0 : ℝ) < n + 1 := by positivity
    have hb : (0 : ℝ) < n + 2 := by positivity
    have hsq1 : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.mpr ha
    have hsq2 : 0 < Real.sqrt (n + 2) := Real.sqrt_pos.mpr hb
    have hr1 : (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (n + 1))⁻¹ := by
      rw [Real.rpow_neg ha.le, Real.sqrt_eq_rpow]
    have hr2 : (n + 2 : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (n + 2))⁻¹ := by
      rw [Real.rpow_neg hb.le, Real.sqrt_eq_rpow]
    have hr3 : (n + 2 : ℝ) ^ (-(3 / 2 : ℝ)) = ((n + 2) * Real.sqrt (n + 2))⁻¹ := by
      rw [Real.rpow_neg hb.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add hb, Real.rpow_one, Real.sqrt_eq_rpow]
    rw [hr1, hr2, hr3]
    have hdiff : (Real.sqrt (n + 1))⁻¹ - (Real.sqrt (n + 2))⁻¹ =
        1 / (Real.sqrt (n + 1) * Real.sqrt (n + 2) * (Real.sqrt (n + 1) + Real.sqrt (n + 2))) := by
      have hsqdiff : Real.sqrt (n + 2) ^ 2 - Real.sqrt (n + 1) ^ 2 = 1 := by
        rw [Real.sq_sqrt hb.le, Real.sq_sqrt ha.le]; ring
      field_simp
      nlinarith [hsqdiff]
    rw [hdiff]
    have hle_sq : Real.sqrt (n + 1) ≤ Real.sqrt (n + 2) := Real.sqrt_le_sqrt (by linarith)
    have hden : Real.sqrt (n + 1) * Real.sqrt (n + 2) * (Real.sqrt (n + 1) + Real.sqrt (n + 2)) ≤
        2 * ((n + 2) * Real.sqrt (n + 2)) := by
      have hs2 : Real.sqrt (n + 2) * Real.sqrt (n + 2) = n + 2 := Real.mul_self_sqrt hb.le
      have hprod : Real.sqrt (n + 1) * (Real.sqrt (n + 1) + Real.sqrt (n + 2)) ≤ 2 * (n + 2) := by
        have hs1 : Real.sqrt (n + 1) * Real.sqrt (n + 1) = n + 1 := Real.mul_self_sqrt ha.le
        nlinarith [hle_sq, hs1, hs2]
      calc Real.sqrt (n + 1) * Real.sqrt (n + 2) * (Real.sqrt (n + 1) + Real.sqrt (n + 2))
          = Real.sqrt (n + 1) * (Real.sqrt (n + 1) + Real.sqrt (n + 2)) * Real.sqrt (n + 2) := by ring
        _ ≤ 2 * (n + 2) * Real.sqrt (n + 2) := mul_le_mul_of_nonneg_right hprod hsq2.le
        _ = 2 * ((n + 2) * Real.sqrt (n + 2)) := by ring
    rw [inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), ((n + 1 : ℝ) ^ (-(3 / 2 : ℝ))) ≤ 3 := by
    intro N
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_add, Real.one_rpow]
    have htele : ∑ n ∈ Finset.range N, ((n + 2 : ℝ) ^ (-(3 / 2 : ℝ))) ≤
        2 * (1 - ((N + 1 : ℝ) ^ (-(1 / 2 : ℝ)))) := by
      calc ∑ n ∈ Finset.range N, ((n + 2 : ℝ) ^ (-(3 / 2 : ℝ)))
          ≤ ∑ n ∈ Finset.range N, 2 * ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) - (n + 2 : ℝ) ^ (-(1 / 2 : ℝ))) :=
            Finset.sum_le_sum fun n _ => hstep n
        _ = 2 * ∑ n ∈ Finset.range N, ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) - (n + 2 : ℝ) ^ (-(1 / 2 : ℝ))) := by
            rw [Finset.mul_sum]
        _ = 2 * (1 - ((N + 1 : ℝ) ^ (-(1 / 2 : ℝ)))) := by
            congr 1
            induction N with
            | zero => simp
            | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
    have hnonneg : (0 : ℝ) ≤ (N + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    have hrew : ∑ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ) + 1) ^ (-(3 / 2 : ℝ)) =
        ∑ n ∈ Finset.range N, ((n + 2 : ℝ) ^ (-(3 / 2 : ℝ))) := by
      refine Finset.sum_congr rfl fun k _ => ?_; push_cast; ring_nf
    rw [hrew]; linarith
  exact le_of_tendsto ((hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1))
    (Eventually.of_forall hpart)

/-- Explicit bound on `‖LFunction χ s‖` for `1/2 ≤ s.re`. -/
lemma norm_LFunction_le_of_re_ge_half {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 3 * (q : ℝ) * ‖s‖ := by
  rw [LFunction_eq_abel_tsum χ hχ (by linarith)]
  have hsum : Summable (fun n : ℕ => (q : ℝ) * ‖s‖ * ((n + 1 : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    (summable_nat_add_one_rpow_neg (by norm_num)).mul_left _
  have hbound : ∀ n : ℕ, ‖(∑ k ∈ Finset.Icc 1 (n + 1), χ k) *
      (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s))‖ ≤
      (q : ℝ) * ‖s‖ * ((n + 1 : ℝ) ^ (-(3 / 2 : ℝ))) := by
    intro n
    rw [norm_mul]
    have h1 := norm_char_partialSum_le χ hχ (n + 1)
    have h2 := norm_cpow_neg_sub_le n s (by linarith)
    have h3 : ((n + 1 : ℝ) ^ (-(s.re + 1))) ≤ ((n + 1 : ℝ) ^ (-(3 / 2 : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
    calc ‖∑ k ∈ Finset.Icc 1 (n + 1), χ k‖ * ‖((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)‖
        ≤ (q : ℝ) * (‖s‖ * ((n + 1 : ℝ) ^ (-(s.re + 1)))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ ≤ (q : ℝ) * (‖s‖ * ((n + 1 : ℝ) ^ (-(3 / 2 : ℝ)))) := by gcongr
      _ = (q : ℝ) * ‖s‖ * ((n + 1 : ℝ) ^ (-(3 / 2 : ℝ))) := by ring
  have hnorm_sum : Summable (fun n : ℕ => ‖(∑ k ∈ Finset.Icc 1 (n + 1), χ k) *
      (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hsum
  calc ‖∑' n : ℕ, (∑ k ∈ Finset.Icc 1 (n + 1), χ k) *
          (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s))‖
      ≤ ∑' n : ℕ, ‖(∑ k ∈ Finset.Icc 1 (n + 1), χ k) *
          (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s))‖ :=
        norm_tsum_le_tsum_norm hnorm_sum
    _ ≤ ∑' n : ℕ, (q : ℝ) * ‖s‖ * ((n + 1 : ℝ) ^ (-(3 / 2 : ℝ))) :=
        hnorm_sum.tsum_le_tsum hbound hsum
    _ = (q : ℝ) * ‖s‖ * ∑' n : ℕ, ((n + 1 : ℝ) ^ (-(3 / 2 : ℝ))) := tsum_mul_left
    _ ≤ (q : ℝ) * ‖s‖ * 3 := mul_le_mul_of_nonneg_left tsum_rpow_neg_three_halves_le (by positivity)
    _ = 3 * (q : ℝ) * ‖s‖ := by ring

/-- Harmonic sum upper bound `∑_{k=1}^N 1/k ≤ 1 + log N`. -/
lemma harmonic_le_one_add_log (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ Finset.Icc 1 N, ((k : ℝ)⁻¹) ≤ 1 + Real.log (N : ℝ) := by
  induction N with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp
    | succ m =>
      have hm : 0 < m + 1 := Nat.succ_pos m
      have hIcc : Finset.Icc 1 (m + 2) = insert (m + 2) (Finset.Icc 1 (m + 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp)]
      have h1 := ih hm
      have hlog : ((m + 2 : ℝ)⁻¹) ≤ Real.log (m + 2 : ℝ) - Real.log (m + 1 : ℝ) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        have hsub := Real.one_sub_inv_le_log_of_pos
          (div_pos (by positivity : (0 : ℝ) < m + 2) (by positivity : (0 : ℝ) < m + 1))
        have heq : 1 - ((m + 2 : ℝ) / (m + 1 : ℝ))⁻¹ = (m + 2 : ℝ)⁻¹ := by field_simp; ring
        linarith
      have hcast : ((m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
      have hcast1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      rw [hcast1] at h1
      linarith

/-- Logarithmic upper bound `‖LFunction χ 1‖ ≤ 3 + log q`. -/
lemma norm_LFunction_one_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤ 3 + Real.log (q : ℝ) := by
  have hqpos : 0 < q := NeZero.pos q
  rw [LFunction_eq_abel_tsum χ hχ (by simp)]
  let f : ℕ → ℂ := fun n => (∑ k ∈ Finset.Icc 1 (n + 1), χ k) *
    (((n + 1 : ℕ) : ℂ) ^ (-(1 : ℂ)) - ((n + 2 : ℕ) : ℂ) ^ (-(1 : ℂ)))
  have hf_bound : ∀ n : ℕ, ‖f n‖ ≤ (q : ℝ) * (((n + 1 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹)) := by
    intro n
    dsimp only [f]
    rw [norm_mul]
    have hdiff : ((n + 1 : ℕ) : ℂ) ^ (-(1 : ℂ)) - ((n + 2 : ℕ) : ℂ) ^ (-(1 : ℂ)) =
        ((((n + 1 : ℝ)⁻¹ - (n + 2 : ℝ)⁻¹ : ℝ)) : ℂ) := by
      simp only [cpow_neg_one, ofReal_sub, ofReal_inv, ofReal_add, ofReal_natCast, ofReal_one,
        Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      norm_num
    have hnn : 0 ≤ (n + 1 : ℝ)⁻¹ - (n + 2 : ℝ)⁻¹ :=
      sub_nonneg.mpr (inv_anti₀ (by positivity) (by linarith))
    rw [hdiff, Complex.norm_real, Real.norm_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_right (norm_char_partialSum_le χ hχ (n + 1)) hnn
  have htele0 : HasSum (fun n : ℕ => (((n + 1 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹))) 1 := by
    simpa using hasSum_inv_sub_inv_shift 0
  have hf_sum : Summable f := Summable.of_norm_bounded (htele0.summable.mul_left _) hf_bound
  rw [← hf_sum.sum_add_tsum_nat_add q]
  have hhead : ∑ n ∈ Finset.range q, f n =
      (∑ k ∈ Finset.Icc 1 q, χ k * ((k : ℂ) ^ (-(1 : ℂ)))) -
        (∑ k ∈ Finset.Icc 1 q, χ k) * (((q + 1 : ℕ) : ℂ) ^ (-(1 : ℂ))) :=
    abel_partial_sum χ 1 q
  have hhead_norm : ‖∑ n ∈ Finset.range q, f n‖ ≤ (1 + Real.log (q : ℝ)) + 1 := by
    rw [hhead]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · calc ‖∑ k ∈ Finset.Icc 1 q, χ k * ((k : ℂ) ^ (-(1 : ℂ)))‖
          ≤ ∑ k ∈ Finset.Icc 1 q, ‖χ k * ((k : ℂ) ^ (-(1 : ℂ)))‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.Icc 1 q, ((k : ℝ)⁻¹) := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [norm_mul, cpow_neg_one, norm_inv, Complex.norm_natCast]
            exact mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
        _ ≤ 1 + Real.log (q : ℝ) := harmonic_le_one_add_log q hqpos
    · rw [norm_mul, cpow_neg_one, norm_inv, Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
      calc ‖∑ k ∈ Finset.Icc 1 q, χ k‖ * ((q : ℝ) + 1)⁻¹
          ≤ (q : ℝ) * ((q : ℝ) + 1)⁻¹ :=
            mul_le_mul_of_nonneg_right (norm_char_partialSum_le χ hχ q) (by positivity)
        _ ≤ 1 := by rw [mul_inv_le_iff₀ (by positivity)]; linarith
  have htail_norm : ‖∑' n : ℕ, f (n + q)‖ ≤ 1 := by
    have hsum_shift : Summable (fun n : ℕ => f (n + q)) := (summable_nat_add_iff q).mpr hf_sum
    have htele_q := hasSum_inv_sub_inv_shift q
    have hbound_q : ∀ n : ℕ, ‖f (n + q)‖ ≤ (q : ℝ) * (((n + q + 1 : ℝ)⁻¹) - ((n + q + 2 : ℝ)⁻¹)) := by
      intro n
      have h := hf_bound (n + q)
      have he1 : ((n + q : ℕ) : ℝ) + 1 = (n : ℝ) + (q : ℝ) + 1 := by push_cast; ring
      have he2 : ((n + q : ℕ) : ℝ) + 2 = (n : ℝ) + (q : ℝ) + 2 := by push_cast; ring
      rwa [he1, he2] at h
    calc ‖∑' n : ℕ, f (n + q)‖
        ≤ ∑' n : ℕ, ‖f (n + q)‖ := norm_tsum_le_tsum_norm hsum_shift.norm
      _ ≤ ∑' n : ℕ, (q : ℝ) * (((n + q + 1 : ℝ)⁻¹) - ((n + q + 2 : ℝ)⁻¹)) :=
          hsum_shift.norm.tsum_le_tsum hbound_q (htele_q.summable.mul_left _)
      _ = (q : ℝ) * ((q + 1 : ℝ)⁻¹) := by rw [tsum_mul_left, htele_q.tsum_eq]
      _ ≤ 1 := by rw [mul_inv_le_iff₀ (by positivity)]; linarith
  calc ‖(∑ n ∈ Finset.range q, f n) + ∑' n : ℕ, f (n + q)‖
      ≤ ‖∑ n ∈ Finset.range q, f n‖ + ‖∑' n : ℕ, f (n + q)‖ := norm_add_le _ _
    _ ≤ ((1 + Real.log (q : ℝ)) + 1) + 1 := add_le_add hhead_norm htail_norm
    _ = 3 + Real.log (q : ℝ) := by ring

/-- Real characters take values in `{-1, 0, 1}` (in particular real values). -/
lemma real_char_im_eq_zero {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ2 : χ ^ 2 = 1) (k : ZMod q) :
    (χ k).im = 0 ∧ ((χ k).re = 0 ∨ (χ k).re = 1 ∨ (χ k).re = -1) := by
  have hsq : χ k ^ 2 = 0 ∨ χ k ^ 2 = 1 := by
    by_cases hu : IsUnit k
    · right
      have h1 : (χ ^ 2) k = (1 : DirichletCharacter ℂ q) k := congrFun (congrArg DFunLike.coe hχ2) k
      rw [MulChar.pow_apply' χ (by norm_num : (2 : ℕ) ≠ 0), MulChar.one_apply hu] at h1
      exact h1
    · left
      rw [MulChar.map_nonunit χ hu]; simp
  rcases hsq with h0 | h1
  · have hz : χ k = 0 := sq_eq_zero_iff.mp h0
    simp [hz]
  · rcases sq_eq_one_iff.mp h1 with h | h <;> simp [h]

/-- For a real nontrivial character `χ`, `LFunction χ x` is real for real `x > 0`. -/
lemma LFunction_im_eq_zero_of_real {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hχ2 : χ ^ 2 = 1) {x : ℝ} (hx : 0 < x) :
    (DirichletCharacter.LFunction χ (x : ℂ)).im = 0 := by
  rw [LFunction_eq_abel_tsum χ hχ (by simpa using hx)]
  have hterm : ∀ n : ℕ, (((∑ k ∈ Finset.Icc 1 (n + 1), χ k) *
      (((n + 1 : ℕ) : ℂ) ^ (-(x : ℂ)) - ((n + 2 : ℕ) : ℂ) ^ (-(x : ℂ))))).im = 0 := by
    intro n
    have hS : (∑ k ∈ Finset.Icc 1 (n + 1), χ k).im = 0 := by
      rw [Complex.im_sum]
      exact Finset.sum_eq_zero fun k _ => (real_char_im_eq_zero hχ2 _).1
    have hc1 : (((n + 1 : ℕ) : ℂ) ^ (-(x : ℂ))).im = 0 := by
      rw [← ofReal_natCast, ← ofReal_neg, ← ofReal_cpow (by positivity), ofReal_im]
    have hc2 : (((n + 2 : ℕ) : ℂ) ^ (-(x : ℂ))).im = 0 := by
      rw [← ofReal_natCast, ← ofReal_neg, ← ofReal_cpow (by positivity), ofReal_im]
    rw [Complex.mul_im, Complex.sub_im, hS, hc1, hc2]; ring
  have hsum : Summable (fun n : ℕ => (∑ k ∈ Finset.Icc 1 (n + 1), χ k) *
      (((n + 1 : ℕ) : ℂ) ^ (-(x : ℂ)) - ((n + 2 : ℕ) : ℂ) ^ (-(x : ℂ)))) := by
    refine Summable.of_norm_bounded ((summable_nat_add_one_rpow_neg (by linarith : 1 < x + 1)).mul_left ((q : ℝ) * ‖(x : ℂ)‖)) ?_
    intro n
    rw [norm_mul]
    have h1 := norm_char_partialSum_le χ hχ (n + 1)
    have h2 := norm_cpow_neg_sub_le n (x : ℂ) (by simpa using hx)
    simp only [ofReal_re] at h2
    calc _ ≤ (q : ℝ) * (‖(x : ℂ)‖ * ((n + 1 : ℝ) ^ (-(x + 1)))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [Complex.im_tsum hsum]
  simp_rw [hterm]
  simp

/-- `LFunction χ x` is strictly positive for real `x ≥ 1` when `χ` is real and nontrivial. -/
lemma LFunction_re_pos_of_one_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hχ2 : χ ^ 2 = 1) {x : ℝ} (hx : 1 ≤ x) :
    0 < (DirichletCharacter.LFunction χ (x : ℂ)).re := by
  have hpos3 : 0 < (DirichletCharacter.LFunction χ (3 : ℂ)).re := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ (by norm_num)]
    have hsum : Summable (LSeries.term (fun n : ℕ => χ n) 3) :=
      DirichletCharacter.LSeriesSummable_of_one_lt_re χ (by norm_num)
    rw [LSeries, ← hsum.sum_add_tsum_nat_add 2]
    have hhead : ∑ n ∈ Finset.range 2, LSeries.term (fun n : ℕ => χ n) 3 n = 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one, LSeries.term_zero, zero_add,
        LSeries.term_of_ne_zero one_ne_zero]
      simp
    rw [hhead, add_re, one_re]
    have htail : ‖∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) 3 (n + 2)‖ ≤ 1 / 2 := by
      have hshift : Summable (fun n : ℕ => LSeries.term (fun n : ℕ => χ n) 3 (n + 2)) :=
        (summable_nat_add_iff 2).mpr hsum
      have htele0 : HasSum (fun n : ℕ => (((n + 1 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹))) 1 := by
        simpa using hasSum_inv_sub_inv_shift 0
      have hb : ∀ n : ℕ, ‖LSeries.term (fun n : ℕ => χ n) 3 (n + 2)‖ ≤
          (1 / 2 : ℝ) * (((n + 1 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹)) := by
        intro n
        rw [LSeries.term_of_ne_zero (by omega), norm_div, Complex.norm_natCast_cpow_of_pos (by omega)]
        have h3 : ((3 : ℂ).re) = 3 := by norm_num
        rw [h3]
        have h1 : ‖χ (n + 2 : ℕ)‖ ≤ 1 := χ.norm_le_one _
        have h2 : ((n + 2 : ℕ) : ℝ) ^ (3 : ℝ) = ((n + 2 : ℝ) ^ 3) := by
          push_cast; exact Real.rpow_natCast _ 3
        rw [h2]
        have hstep : (1 : ℝ) / ((n + 2 : ℝ) ^ 3) ≤ (1 / 2 : ℝ) * (((n + 1 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹)) := by
          have hsub : ((n + 1 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹) = 1 / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
            field_simp; ring
          rw [hsub, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have hcub : 2 * ((n + 1 : ℝ) * (n + 2)) ≤ (n + 2 : ℝ) ^ 3 := by
            have hsq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
            have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            nlinarith
          linarith
        exact (div_le_div_of_nonneg_right h1 (by positivity)).trans hstep
      calc ‖∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) 3 (n + 2)‖
          ≤ ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => χ n) 3 (n + 2)‖ := norm_tsum_le_tsum_norm hshift.norm
        _ ≤ ∑' n : ℕ, (1 / 2 : ℝ) * (((n + 1 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹)) :=
            hshift.norm.tsum_le_tsum hb (htele0.summable.mul_left _)
        _ = (1 / 2 : ℝ) * ∑' n : ℕ, (((n + 1 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹)) := tsum_mul_left
        _ = 1 / 2 := by rw [htele0.tsum_eq, mul_one]
    have hre_le : |(∑' n : ℕ, LSeries.term (fun n : ℕ => χ n) 3 (n + 2)).re| ≤ 1 / 2 :=
      (Complex.abs_re_le_norm _).trans htail
    linarith [(abs_le.mp hre_le).1]
  have hne : ∀ t : ℝ, 1 ≤ t → (DirichletCharacter.LFunction χ (t : ℂ)).re ≠ 0 := by
    intro t ht hzero
    have him : (DirichletCharacter.LFunction χ (t : ℂ)).im = 0 :=
      LFunction_im_eq_zero_of_real hχ hχ2 (by linarith)
    have h0 : DirichletCharacter.LFunction χ (t : ℂ) = 0 := Complex.ext hzero him
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl hχ) (by simpa using ht) h0
  by_contra hle
  push Not at hle
  have hlt : (DirichletCharacter.LFunction χ (x : ℂ)).re < 0 := lt_of_le_of_ne hle (hne x hx)
  let g : ℝ → ℝ := fun t => (DirichletCharacter.LFunction χ (t : ℂ)).re
  have hcont : Continuous g :=
    Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal)
  rcases le_total x 3 with hx3 | h3x
  · have h0mem : (0 : ℝ) ∈ Set.Icc (g x) (g 3) := ⟨hlt.le, hpos3.le⟩
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc hx3 hcont.continuousOn h0mem
    exact hne t (le_trans hx ht.1) hgt
  · have h0mem : (0 : ℝ) ∈ Set.Icc (g x) (g 3) := ⟨hlt.le, hpos3.le⟩
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' h3x hcont.continuousOn h0mem
    exact hne t (by linarith [ht.1]) hgt

/-- `riemannZeta x` is real and negative for `0 < x < 1`. -/
lemma riemannZeta_neg_of_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (riemannZeta (x : ℂ)).im = 0 ∧ (riemannZeta (x : ℂ)).re < 0 := by
  let Φ : ZMod 2 → ℂ := fun j => if j = 0 then -1 else 1
  have hsumΦ : ∑ j : ZMod 2, Φ j = 0 := by
    rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide, Finset.sum_pair (by decide)]
    simp [Φ]
  have hdiffΦ : Differentiable ℂ (ZMod.LFunction Φ) := fun s =>
    ZMod.differentiableAt_LFunction Φ s (Or.inr hsumΦ)
  have hrel : ∀ s : ℂ, 1 < s.re → ZMod.LFunction Φ s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
    intro s hs
    rw [ZMod.LFunction_eq_LSeries Φ hs, ← LSeries_one_eq_riemannZeta hs]
    have hsum1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
    have hterm_eq : ∀ n : ℕ, LSeries.term (fun k : ℕ => Φ k) s n =
        LSeries.term 1 s n - 2 * (if 2 ∣ n then LSeries.term 1 s n else 0) := by
      intro n
      by_cases hn : n = 0
      · subst hn; simp [LSeries.term_zero]
      · simp only [LSeries.term_of_ne_zero hn, Pi.one_apply, Φ]
        by_cases h2 : 2 ∣ n
        · have hz : (n : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff n 2).mpr h2
          simp [h2, hz]; ring
        · have hz : (n : ZMod 2) ≠ 0 := fun h => h2 ((ZMod.natCast_eq_zero_iff n 2).mp h)
          simp [h2, hz]
    have heven_sum : ∑' n : ℕ, (if 2 ∣ n then LSeries.term 1 s n else 0) =
        (2 : ℂ) ^ (-s) * LSeries 1 s := by
      have heq : (∑' n : ℕ, if 2 ∣ n then LSeries.term 1 s n else 0) =
          ∑' m : ℕ, LSeries.term 1 s (2 * m) := by
        refine tsum_eq_tsum_of_ne_zero_bij (fun m => 2 * m.1) ?_ ?_ ?_
        · intro a b hab; dsimp only at hab; exact Subtype.ext (by omega)
        · intro n hn
          simp only [Function.mem_support, ne_eq] at hn
          by_cases h2 : 2 ∣ n
          · obtain ⟨m, rfl⟩ := h2
            have hm : LSeries.term 1 s (2 * m) ≠ 0 := by
              simpa [dvd_mul_right] using hn
            exact ⟨⟨m, hm⟩, rfl⟩
          · simp [h2] at hn
        · intro m; simp [dvd_mul_right]
      rw [heq, LSeries, ← tsum_mul_left]
      congr 1; ext m
      by_cases hm : m = 0
      · subst hm; simp [LSeries.term_zero]
      · rw [LSeries.term_of_ne_zero (by omega), LSeries.term_of_ne_zero hm]
        simp only [Pi.one_apply, Nat.cast_mul, Nat.cast_ofNat]
        have hcpow : ((2 : ℂ) * (m : ℂ)) ^ s = (2 : ℂ) ^ s * (m : ℂ) ^ s := by
          have := Complex.mul_cpow_ofReal_nonneg (a := (2 : ℝ)) (b := (m : ℝ)) (by norm_num) (by positivity) (r := s)
          simpa using this
        rw [hcpow, cpow_neg]
        ring
    have hsum_if : Summable (fun n : ℕ => if 2 ∣ n then LSeries.term 1 s n else 0) :=
      Summable.of_norm_bounded hsum1.norm (fun n => by split_ifs <;> simp)
    rw [LSeries, show (fun n => LSeries.term (fun k : ℕ => Φ k) s n) =
        (fun n => LSeries.term 1 s n - 2 * (if 2 ∣ n then LSeries.term 1 s n else 0)) from funext hterm_eq,
      hsum1.tsum_sub (hsum_if.mul_left 2), tsum_mul_left, heven_sum]
    have h2pow : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num), cpow_one]
    rw [h2pow, LSeries]; ring
  have hrel_all : ∀ s : ℂ, s ≠ 1 → ZMod.LFunction Φ s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
    let U : Set ℂ := {s : ℂ | s ≠ 1}
    have hUopen : IsOpen U := isOpen_ne
    have hUconn : IsPreconnected U :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
    have hAn1 : AnalyticOnNhd ℂ (ZMod.LFunction Φ) U := hdiffΦ.differentiableOn.analyticOnNhd hUopen
    have hAn2 : AnalyticOnNhd ℂ (fun s => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) U := by
      refine DifferentiableOn.analyticOnNhd ?_ hUopen
      intro s hs
      have h1 : DifferentiableAt ℂ (fun z : ℂ => 1 - (2 : ℂ) ^ (1 - z)) s :=
        (differentiableAt_const 1).sub ((differentiableAt_const (2 : ℂ)).cpow
          ((differentiableAt_const 1).sub differentiableAt_id) (Or.inl (by norm_num)))
      exact (h1.mul (differentiableAt_riemannZeta hs)).differentiableWithinAt
    have hEqOn : Set.EqOn (ZMod.LFunction Φ) (fun s => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) U := by
      refine hAn1.eqOn_of_preconnected_of_eventuallyEq hAn2 hUconn (show (2 : ℂ) ≠ 1 by norm_num) ?_
      have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
      filter_upwards [hmem] with z hz
      exact hrel z hz
    exact fun s hs => hEqOn hs
  have heta_pos : (ZMod.LFunction Φ (x : ℂ)).im = 0 ∧ 0 < (ZMod.LFunction Φ (x : ℂ)).re := by
    let g : ℂ → ℂ := fun z => ∑' m : ℕ, (((2 * m + 1 : ℕ) : ℂ) ^ (-z) - ((2 * m + 2 : ℕ) : ℂ) ^ (-z))
    let V : Set ℂ := {z : ℂ | 0 < z.re}
    have hVopen : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
    have hterm_b : ∀ (m : ℕ) (z : ℂ), 0 < z.re →
        ‖((2 * m + 1 : ℕ) : ℂ) ^ (-z) - ((2 * m + 2 : ℕ) : ℂ) ^ (-z)‖ ≤
          ‖z‖ * ((2 * m + 1 : ℝ) ^ (-(z.re + 1))) := fun m z hz => by
      simpa [Nat.cast_add, Nat.cast_mul] using norm_cpow_neg_sub_le (2 * m) z hz
    have hUnif : TendstoLocallyUniformlyOn (fun N z => ∑ m ∈ Finset.range N,
        (((2 * m + 1 : ℕ) : ℂ) ^ (-z) - ((2 * m + 2 : ℕ) : ℂ) ^ (-z))) g atTop V := by
      rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hVopen]
      intro K hKV hKcomp
      rcases K.eq_empty_or_nonempty with rfl | hKne
      · simp [tendstoUniformlyOn_empty]
      obtain ⟨z₀, hz₀K, hz₀min⟩ := hKcomp.exists_isMinOn hKne Complex.continuous_re.continuousOn
      obtain ⟨z₁, hz₁K, hz₁max⟩ := hKcomp.exists_isMaxOn hKne continuous_norm.continuousOn
      set δ := z₀.re
      have hδ : 0 < δ := hKV hz₀K
      have hMsum : Summable (fun m : ℕ => ‖z₁‖ * ((m + 1 : ℝ) ^ (-(δ + 1)))) :=
        (summable_nat_add_one_rpow_neg (by linarith)).mul_left _
      refine tendstoUniformlyOn_tsum_nat hMsum fun m z hzK => ?_
      calc ‖((2 * m + 1 : ℕ) : ℂ) ^ (-z) - ((2 * m + 2 : ℕ) : ℂ) ^ (-z)‖
          ≤ ‖z‖ * ((2 * m + 1 : ℝ) ^ (-(z.re + 1))) := hterm_b m z (lt_of_lt_of_le hδ (hz₀min hzK))
        _ ≤ ‖z₁‖ * ((m + 1 : ℝ) ^ (-(δ + 1))) := by
            refine mul_le_mul (hz₁max hzK) ?_ (by positivity) (norm_nonneg _)
            calc ((2 * m + 1 : ℝ) ^ (-(z.re + 1)))
                ≤ ((2 * m + 1 : ℝ) ^ (-(δ + 1))) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) m])
                    (by have hle : z₀.re ≤ z.re := hz₀min hzK; dsimp only [δ]; linarith)
              _ ≤ ((m + 1 : ℝ) ^ (-(δ + 1))) :=
                  Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have hdiffg : DifferentiableOn ℂ g V := by
      refine hUnif.differentiableOn (Eventually.of_forall fun N => ?_) hVopen
      refine DifferentiableOn.fun_sum fun m _ => DifferentiableOn.sub ?_ ?_
      · intro z _; exact ((differentiableAt_const _).cpow differentiableAt_id.neg
          (Or.inl (by simp; positivity : 0 < (((2 * m + 1 : ℕ) : ℂ)).re))).differentiableWithinAt
      · intro z _; exact ((differentiableAt_const _).cpow differentiableAt_id.neg
          (Or.inl (by simp; positivity : 0 < (((2 * m + 2 : ℕ) : ℂ)).re))).differentiableWithinAt
    have heq_gt : ∀ z : ℂ, 1 < z.re → ZMod.LFunction Φ z = g z := by
      intro z hz
      rw [ZMod.LFunction_eq_LSeries Φ hz]
      have hsumL := ZMod.LSeriesSummable_of_one_lt_re Φ hz
      have hlimL : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (2 * N + 1), LSeries.term (fun n : ℕ => Φ n) z k)
          atTop (𝓝 (LSeries (fun n : ℕ => Φ n) z)) :=
        (hsumL.hasSum.tendsto_sum_nat).comp (tendsto_atTop_mono (fun N => show N ≤ 2 * N + 1 by omega) tendsto_id)
      have hsumG : Summable (fun m : ℕ => ((2 * m + 1 : ℕ) : ℂ) ^ (-z) - ((2 * m + 2 : ℕ) : ℂ) ^ (-z)) := by
        refine Summable.of_norm_bounded ((summable_nat_add_one_rpow_neg (by linarith : 1 < z.re + 1)).mul_left ‖z‖) ?_
        intro m
        refine (hterm_b m z (by linarith)).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg z))
        exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      have hpair : ∀ N : ℕ, ∑ k ∈ Finset.range (2 * N + 1), LSeries.term (fun n : ℕ => Φ n) z k =
          ∑ m ∈ Finset.range N, (((2 * m + 1 : ℕ) : ℂ) ^ (-z) - ((2 * m + 2 : ℕ) : ℂ) ^ (-z)) := by
        intro N
        induction N with
        | zero => simp [LSeries.term_zero]
        | succ N ih =>
          rw [show 2 * (N + 1) + 1 = (2 * N + 1) + 1 + 1 by omega,
            Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
          have h1 : LSeries.term (fun n : ℕ => Φ n) z (2 * N + 1) = ((2 * N + 1 : ℕ) : ℂ) ^ (-z) := by
            rw [LSeries.term_of_ne_zero (by omega)]
            have hz1 : ((2 * N + 1 : ℕ) : ZMod 2) ≠ 0 := by
              rw [ne_eq, ZMod.natCast_eq_zero_iff]; omega
            dsimp only [Φ]
            rw [if_neg hz1, cpow_neg, one_div]
          have h2 : LSeries.term (fun n : ℕ => Φ n) z (2 * N + 1 + 1) = -((2 * N + 2 : ℕ) : ℂ) ^ (-z) := by
            rw [show 2 * N + 1 + 1 = 2 * N + 2 by omega, LSeries.term_of_ne_zero (by omega)]
            have hz2 : ((2 * N + 2 : ℕ) : ZMod 2) = 0 := by
              rw [ZMod.natCast_eq_zero_iff]; omega
            dsimp only [Φ]
            rw [if_pos hz2, cpow_neg, neg_div, one_div]
          rw [h1, h2]; ring
      simp_rw [hpair] at hlimL
      exact tendsto_nhds_unique hlimL hsumG.hasSum.tendsto_sum_nat
    have hVconn : IsPreconnected V := Convex.isPreconnected fun a ha b hb u v hu hv huv => by
      simp only [V, Set.mem_ofPred_eq, add_re, real_smul, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at ha hb ⊢
      rcases lt_or_eq_of_le hu with hu' | rfl <;> nlinarith
    have hEqV : ZMod.LFunction Φ (x : ℂ) = g (x : ℂ) := by
      have hEqOn := (hdiffΦ.differentiableOn.analyticOnNhd hVopen).eqOn_of_preconnected_of_eventuallyEq
        (hdiffg.analyticOnNhd hVopen) hVconn (show (2 : ℂ) ∈ V by simp [V])
        (Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp))
          fun z hz => heq_gt z hz)
      exact hEqOn (show (x : ℂ) ∈ V by simpa [V] using hx0)
    rw [hEqV]
    have hsumx : Summable (fun m : ℕ => ((2 * m + 1 : ℕ) : ℂ) ^ (-(x : ℂ)) - ((2 * m + 2 : ℕ) : ℂ) ^ (-(x : ℂ))) := by
      refine Summable.of_norm_bounded ((summable_nat_add_one_rpow_neg (by linarith : 1 < x + 1)).mul_left ‖(x : ℂ)‖) ?_
      intro m
      refine (hterm_b m (x : ℂ) (by simpa using hx0)).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      simp only [ofReal_re]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have hreal_m : ∀ m : ℕ, (((2 * m + 1 : ℕ) : ℂ) ^ (-(x : ℂ)) - ((2 * m + 2 : ℕ) : ℂ) ^ (-(x : ℂ))) =
        ((((2 * m + 1 : ℝ) ^ (-x) - (2 * m + 2 : ℝ) ^ (-x) : ℝ)) : ℂ) := by
      intro m
      rw [← ofReal_natCast, ← ofReal_natCast, ← ofReal_neg, ← ofReal_cpow (by positivity),
        ← ofReal_cpow (by positivity), ← ofReal_sub]
      push_cast; rfl
    have hre_pos_m : ∀ m : ℕ, 0 < ((2 * m + 1 : ℝ) ^ (-x) - (2 * m + 2 : ℝ) ^ (-x)) := by
      intro m
      rw [sub_pos]
      exact Real.rpow_lt_rpow_of_neg (by positivity) (by linarith) (by linarith)
    constructor
    · rw [Complex.im_tsum hsumx]
      simp_rw [hreal_m, ofReal_im]
      simp
    · rw [Complex.re_tsum hsumx]
      have hsum_re : Summable (fun m : ℕ => ((2 * m + 1 : ℝ) ^ (-x) - (2 * m + 2 : ℝ) ^ (-x))) := by
        have := Complex.reCLM.summable hsumx
        simp_rw [Complex.reCLM_apply, hreal_m, ofReal_re] at this
        exact this
      have htsum : (∑' m : ℕ, ((((2 * m + 1 : ℕ) : ℂ) ^ (-(x : ℂ)) - ((2 * m + 2 : ℕ) : ℂ) ^ (-(x : ℂ)))).re) =
          ∑' m : ℕ, ((2 * m + 1 : ℝ) ^ (-x) - (2 * m + 2 : ℝ) ^ (-x)) := by
        congr 1; ext m; rw [hreal_m, ofReal_re]
      rw [htsum]
      exact hsum_re.tsum_pos (fun m => (hre_pos_m m).le) 0 (hre_pos_m 0)
  have hxne : (x : ℂ) ≠ 1 := by exact_mod_cast hx1.ne
  have heq := hrel_all (x : ℂ) hxne
  have hfac : (1 - (2 : ℂ) ^ (1 - (x : ℂ))) = ((1 - (2 : ℝ) ^ (1 - x) : ℝ) : ℂ) := by
    rw [← ofReal_one, ← ofReal_sub, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      ← ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2), ofReal_sub, ofReal_one]
  have hfac_neg : 1 - (2 : ℝ) ^ (1 - x) < 0 := by
    have : (1 : ℝ) < (2 : ℝ) ^ (1 - x) := Real.one_lt_rpow (by norm_num) (by linarith)
    linarith
  rw [hfac] at heq
  have him_eq := congrArg Complex.im heq
  have hre_eq := congrArg Complex.re heq
  simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, mul_re, sub_zero] at him_eq hre_eq
  rw [heta_pos.1] at him_eq
  have hzim : (riemannZeta (x : ℂ)).im = 0 := by
    rcases mul_eq_zero.mp him_eq.symm with h | h
    · linarith
    · exact h
  have hzre : (riemannZeta (x : ℂ)).re < 0 := by nlinarith [heta_pos.2]
  exact ⟨hzim, hzre⟩

/-!
### Part 2: Estermann's Lemma and Siegel's Theorem
-/

/-- The entire function `z ↦ (z - 1) * riemannZeta z` updated to `1` at `z = 1`. -/
noncomputable def zetaTimesSubOne (z : ℂ) : ℂ :=
  Function.update (fun w : ℂ => (w - 1) * riemannZeta w) 1 1 z

lemma differentiable_zetaTimesSubOne : Differentiable ℂ zetaTimesSubOne := by
  have hcont : ContinuousAt zetaTimesSubOne 1 := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hev : zetaTimesSubOne =ᶠ[𝓝[≠] (1 : ℂ)] fun w => (w - 1) * riemannZeta w := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact Function.update_of_ne hw _ _
    have htend : Tendsto zetaTimesSubOne (𝓝[≠] (1 : ℂ)) (𝓝 1) :=
      riemannZeta_residue_one.congr' hev.symm
    rw [Metric.tendsto_nhdsWithin_nhds] at htend
    obtain ⟨δ, hδ, hball⟩ := htend ε hε
    refine ⟨δ, hδ, fun w hw => ?_⟩
    rw [show zetaTimesSubOne 1 = 1 from Function.update_self 1 1 _]
    by_cases h1 : w = 1
    · subst h1; simp [zetaTimesSubOne, hε]
    · exact hball h1 hw
  have hdiff_ne : DifferentiableOn ℂ zetaTimesSubOne (Set.univ \ {1}) := by
    intro z hz
    have hne : z ≠ 1 := by simpa using hz.2
    have hev : zetaTimesSubOne =ᶠ[𝓝 z] fun w => (w - 1) * riemannZeta w := by
      filter_upwards [isOpen_ne.mem_nhds hne] with w hw
      exact Function.update_of_ne hw _ _
    have hd : DifferentiableAt ℂ (fun w => (w - 1) * riemannZeta w) z :=
      (differentiableAt_id.sub (differentiableAt_const 1)).mul (differentiableAt_riemannZeta hne)
    exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
  have hdiffOn : DifferentiableOn ℂ zetaTimesSubOne Set.univ :=
    (Complex.differentiableOn_compl_singleton_and_continuousAt_iff Filter.univ_mem).mp ⟨hdiff_ne, hcont⟩
  exact differentiableOn_univ.mp hdiffOn

lemma zetaTimesSubOne_one : zetaTimesSubOne 1 = 1 := Function.update_self 1 1 _

lemma zetaTimesSubOne_ne_one {z : ℂ} (hz : z ≠ 1) :
    zetaTimesSubOne z = (z - 1) * riemannZeta z := Function.update_of_ne hz _ _

/-- Bound on `‖riemannZeta z‖` on the circle `‖z - 2‖ = 3/2`. -/
lemma exists_zeta_sphere_bound :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2 : ℝ), ‖riemannZeta z‖ ≤ C₀ := by
  have hcomp : IsCompact (Metric.sphere (2 : ℂ) (3 / 2 : ℝ)) := isCompact_sphere _ _
  have hne : (Metric.sphere (2 : ℂ) (3 / 2 : ℝ)).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  have hcont : ContinuousOn (fun z => ‖riemannZeta z‖) (Metric.sphere (2 : ℂ) (3 / 2 : ℝ)) := by
    refine ContinuousOn.norm fun z hz => ?_
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, Metric.mem_sphere, dist_eq_norm] at hz
      norm_num at hz
    exact (differentiableAt_riemannZeta hz1).continuousAt.continuousWithinAt
  obtain ⟨z₀, _, hmax⟩ := hcomp.exists_isMaxOn hne hcont
  exact ⟨max 1 ‖riemannZeta z₀‖, le_max_left _ _, fun z hz => (hmax hz).trans (le_max_right _ _)⟩

/-- Convolution of four multiplicative functions with prime values `1, x, y, x*y` in `{-1, 0, 1}` is nonnegative. -/
lemma conv4_prime_pow_nonneg (x y : ℝ) (hx : x = 0 ∨ x = 1 ∨ x = -1) (hy : y = 0 ∨ y = 1 ∨ y = -1)
    (k : ℕ) :
    0 ≤ ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1 - a),
      ∑ c ∈ Finset.range (k + 1 - a - b), x ^ a * y ^ b * (x * y) ^ c := by
  -- Helper: convolution of 1 and (-1) at m is 1 if even, 0 if odd, always ≥ 0
  have h1m1 : ∀ m : ℕ, 0 ≤ ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rcases Nat.even_or_odd m with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · have : ∑ j ∈ Finset.range (r + r + 1 + 1), (-1 : ℝ) ^ j = 0 := by
          clear ih
          induction r with
          | zero => simp [Finset.sum_range_succ]
          | succ r ih' =>
            rw [show (r + 1) + (r + 1) + 1 + 1 = (r + r + 1 + 1) + 1 + 1 by omega,
              Finset.sum_range_succ, Finset.sum_range_succ, ih']
            have h1 : (-1 : ℝ) ^ (r + r + 1 + 1) = 1 := by
              rw [show r + r + 1 + 1 = 2 * (r + 1) by omega, pow_mul]; norm_num
            have h2 : (-1 : ℝ) ^ (r + r + 1 + 1 + 1) = -1 := by
              rw [pow_succ, h1]; norm_num
            linarith
        linarith
      · rw [Finset.sum_range_succ]
        have h1 : (-1 : ℝ) ^ (2 * r + 1 + 1) = 1 := by
          rw [show 2 * r + 1 + 1 = 2 * (r + 1) by omega, pow_mul]; norm_num
        linarith
  -- Helper: alternating triangular sum T(m) = ∑_{b=0}^m ∑_{c=0}^{m-b} (-1)^(b+c)
  have htri_val : ∀ m : ℕ,
      (∑ b ∈ Finset.range (m + 1), ∑ c ∈ Finset.range (m + 1 - b), (-1 : ℝ) ^ (b + c)) =
        if Even m then ((m / 2 + 1 : ℕ) : ℝ) else -((m / 2 + 1 : ℕ) : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hsplit : (∑ b ∈ Finset.range (m + 2), ∑ c ∈ Finset.range (m + 2 - b), (-1 : ℝ) ^ (b + c)) =
          (∑ b ∈ Finset.range (m + 1), ∑ c ∈ Finset.range (m + 1 - b), (-1 : ℝ) ^ (b + c)) +
          ((m + 2 : ℕ) : ℝ) * (-1 : ℝ) ^ (m + 1) := by
        rw [Finset.sum_range_succ]
        have hlast : ∑ c ∈ Finset.range (m + 2 - (m + 1)), (-1 : ℝ) ^ ((m + 1) + c) = (-1 : ℝ) ^ (m + 1) := by
          rw [show m + 2 - (m + 1) = 1 by omega]; simp
        rw [hlast]
        have hinner : ∑ b ∈ Finset.range (m + 1), ∑ c ∈ Finset.range (m + 2 - b), (-1 : ℝ) ^ (b + c) =
            (∑ b ∈ Finset.range (m + 1), ∑ c ∈ Finset.range (m + 1 - b), (-1 : ℝ) ^ (b + c)) +
            ∑ _b ∈ Finset.range (m + 1), (-1 : ℝ) ^ (m + 1) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun b hb => ?_
          rw [Finset.mem_range] at hb
          rw [show m + 2 - b = (m + 1 - b) + 1 by omega, Finset.sum_range_succ]
          congr 1; congr 1; omega
        rw [hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast; ring
      rw [hsplit, ih]
      rcases Nat.even_or_odd m with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · have hev : Even (r + r) := ⟨r, rfl⟩
        have hnev : ¬ Even (r + r + 1) := by intro ⟨t, ht⟩; omega
        rw [if_pos hev, if_neg hnev]
        have hp : (-1 : ℝ) ^ (r + r + 1) = -1 := by
          rw [pow_succ, show r + r = 2 * r by omega, pow_mul]; norm_num
        rw [hp, show (r + r) / 2 = r by omega, show (r + r + 1) / 2 = r by omega]
        push_cast; ring
      · have hnev : ¬ Even (2 * r + 1) := by intro ⟨t, ht⟩; omega
        have hev : Even (2 * r + 1 + 1) := ⟨r + 1, by omega⟩
        rw [if_neg hnev, if_pos hev]
        have hp : (-1 : ℝ) ^ (2 * r + 1 + 1) = 1 := by
          rw [show 2 * r + 1 + 1 = 2 * (r + 1) by omega, pow_mul]; norm_num
        rw [hp, show (2 * r + 1) / 2 = r by omega, show (2 * r + 1 + 1) / 2 = r + 1 by omega]
        push_cast; ring
  have hsum_tri_nn : ∀ n : ℕ,
      0 ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
        ∑ c ∈ Finset.range (n + 1 - a - b), (-1 : ℝ) ^ (b + c) := by
    intro n
    have hrew : (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
        ∑ c ∈ Finset.range (n + 1 - a - b), (-1 : ℝ) ^ (b + c)) =
        ∑ m ∈ Finset.range (n + 1),
          (if Even m then ((m / 2 + 1 : ℕ) : ℝ) else -((m / 2 + 1 : ℕ) : ℝ)) := by
      rw [← Finset.sum_range_reflect (fun m =>
        if Even m then ((m / 2 + 1 : ℕ) : ℝ) else -((m / 2 + 1 : ℕ) : ℝ)) (n + 1)]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mem_range] at ha
      have hm : n + 1 - 1 - a = n - a := by omega
      rw [hm, ← htri_val (n - a)]
      have hlen : n - a + 1 = n + 1 - a := by omega
      rw [hlen]
    rw [hrew]
    have hval : ∀ n : ℕ, (∑ m ∈ Finset.range (n + 1),
        (if Even m then ((m / 2 + 1 : ℕ) : ℝ) else -((m / 2 + 1 : ℕ) : ℝ))) =
        if Even n then ((n / 2 + 1 : ℕ) : ℝ) else 0 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        rcases Nat.even_or_odd m with ⟨r, rfl⟩ | ⟨r, rfl⟩
        · have hev : Even (r + r) := ⟨r, rfl⟩
          have hnev : ¬ Even (r + r + 1) := by intro ⟨t, ht⟩; omega
          simp only [hev, hnev, ↓reduceIte, show (r + r) / 2 = r by omega, show (r + r + 1) / 2 = r by omega]
          ring
        · have hnev : ¬ Even (2 * r + 1) := by intro ⟨t, ht⟩; omega
          have hev : Even (2 * r + 1 + 1) := ⟨r + 1, by omega⟩
          simp only [hev, hnev, ↓reduceIte]
          ring
    rw [hval n]
    split_ifs <;> positivity
  have hcube_tri : ∀ f : ℕ → ℕ → ℕ → ℝ,
      (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1 - a),
        ∑ c ∈ Finset.range (k + 1 - a - b), f a b c) =
      ∑ p ∈ ((Finset.range (k + 1) ×ˢ Finset.range (k + 1)) ×ˢ Finset.range (k + 1)).filter
        (fun p => p.1.1 + p.1.2 + p.2 ≤ k), f p.1.1 p.1.2 p.2 := by
    intro f
    rw [Finset.sum_filter, Finset.sum_product, Finset.sum_product]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_range] at ha
    rw [← Finset.sum_subset (show Finset.range (k + 1 - a) ⊆ Finset.range (k + 1) by
      intro x hx; rw [Finset.mem_range] at hx ⊢; omega)]
    · refine Finset.sum_congr rfl fun b hb => ?_
      rw [Finset.mem_range] at hb
      rw [← Finset.sum_subset (show Finset.range (k + 1 - a - b) ⊆ Finset.range (k + 1) by
        intro x hx; rw [Finset.mem_range] at hx ⊢; omega)]
      · refine Finset.sum_congr rfl fun c hc => ?_
        rw [Finset.mem_range] at hc
        dsimp only; rw [if_pos (by omega)]
      · intro c hc hnc
        rw [Finset.mem_range] at hc hnc
        dsimp only; rw [if_neg (by omega)]
    · intro b hb hnb
      rw [Finset.mem_range] at hb hnb
      refine Finset.sum_eq_zero fun c _ => by dsimp only; rw [if_neg (by omega)]
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => by positivity
  · refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => by positivity
  · have hrew : (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1 - a),
        ∑ c ∈ Finset.range (k + 1 - a - b), (0 : ℝ) ^ a * (-1 : ℝ) ^ b * (0 * -1 : ℝ) ^ c) =
        ∑ b ∈ Finset.range (k + 1), (-1 : ℝ) ^ b := by
      rw [Finset.sum_eq_single 0]
      · simp only [pow_zero, one_mul, Nat.sub_zero, zero_mul]
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [Finset.sum_eq_single 0]
        · simp
        · intro c _ hc0; simp [zero_pow hc0]
        · intro h0; exfalso; apply h0; rw [Finset.mem_range] at hb ⊢; omega
      · intro a _ ha0
        refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => by simp [zero_pow ha0]
      · intro h0; exfalso; exact h0 (Finset.mem_range.mpr (Nat.succ_pos k))
    rw [hrew]; exact h1m1 k
  · refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => by positivity
  · refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => by positivity
  · -- (1, -1)
    convert hsum_tri_nn k using 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [one_pow, one_mul, one_mul, pow_add]
  · -- (-1, 0)
    have hrew : (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1 - a),
        ∑ c ∈ Finset.range (k + 1 - a - b), (-1 : ℝ) ^ a * (0 : ℝ) ^ b * (-1 * 0 : ℝ) ^ c) =
        ∑ a ∈ Finset.range (k + 1), (-1 : ℝ) ^ a := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.sum_eq_single 0]
      · simp only [pow_zero, mul_one, Nat.sub_zero, mul_zero]
        rw [Finset.sum_eq_single 0]
        · simp
        · intro c _ hc0; simp [zero_pow hc0]
        · intro h0; exfalso; apply h0; rw [Finset.mem_range] at ha ⊢; omega
      · intro b _ hb0
        refine Finset.sum_eq_zero fun c _ => by simp [zero_pow hb0]
      · intro h0; exfalso; apply h0; rw [Finset.mem_range] at ha ⊢; omega
    rw [hrew]; exact h1m1 k
  · -- (-1, 1): swap (a, b, c) -> (b, a, c) on the cube filter
    have hswap : (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1 - a),
        ∑ c ∈ Finset.range (k + 1 - a - b), (-1 : ℝ) ^ a * (1 : ℝ) ^ b * (-1 * 1 : ℝ) ^ c) =
        ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1 - a),
          ∑ c ∈ Finset.range (k + 1 - a - b), (-1 : ℝ) ^ (b + c) := by
      rw [hcube_tri, hcube_tri]
      refine Finset.sum_bij (fun p _ => ((p.1.2, p.1.1), p.2)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢; omega
      · intro p₁ _ p₂ _ heq
        rcases p₁ with ⟨⟨a₁, b₁⟩, c₁⟩; rcases p₂ with ⟨⟨a₂, b₂⟩, c₂⟩
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq; rfl
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
        exact ⟨((q.1.2, q.1.1), q.2), by simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega, rfl⟩
      · intro p _; simp [pow_add]
    rw [hswap]; exact hsum_tri_nn k
  · -- (-1, -1): rotate (a, b, c) -> (c, a, b) on the cube filter
    have hrot : (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1 - a),
        ∑ c ∈ Finset.range (k + 1 - a - b), (-1 : ℝ) ^ a * (-1 : ℝ) ^ b * (-1 * -1 : ℝ) ^ c) =
        ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1 - a),
          ∑ c ∈ Finset.range (k + 1 - a - b), (-1 : ℝ) ^ (b + c) := by
      rw [hcube_tri, hcube_tri]
      refine Finset.sum_bij (fun p _ => ((p.2, p.1.1), p.1.2)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢; omega
      · intro p₁ _ p₂ _ heq
        rcases p₁ with ⟨⟨a₁, b₁⟩, c₁⟩; rcases p₂ with ⟨⟨a₂, b₂⟩, c₂⟩
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq; rfl
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
        exact ⟨((q.1.2, q.2), q.1.1), by simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega, rfl⟩
      · intro p _; simp [show (-1 : ℝ) * -1 = 1 by norm_num, pow_add]
    rw [hrot]; exact hsum_tri_nn k

private noncomputable def charToAF {N : ℕ} (χ : DirichletCharacter ℂ N) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else χ n, by simp⟩

private lemma charToAF_isMultiplicative {N : ℕ} (χ : DirichletCharacter ℂ N) :
    (charToAF χ).IsMultiplicative := by
  refine ⟨by simp [charToAF], fun {m n} _ => ?_⟩
  by_cases hm : m = 0
  · subst hm; simp [charToAF]
  · by_cases hn : n = 0
    · subst hn; simp [charToAF]
    · have hmn : m * n ≠ 0 := mul_ne_zero hm hn
      simp [charToAF, hm, hn, hmn, map_mul]

private lemma charToAF_LSeries_eq {N : ℕ} (χ : DirichletCharacter ℂ N) (z : ℂ) :
    LSeries (charToAF χ ·) z = LSeries (fun n : ℕ => χ n) z := by
  refine LSeries_congr ?_ z
  intro n hn
  simp [charToAF, hn]

private lemma charToAF_LSeriesSummable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z : ℂ} (hz : 1 < z.re) : LSeriesSummable (charToAF χ ·) z := by
  refine (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz).congr fun n => ?_
  by_cases hn : n = 0
  · subst hn; simp [LSeries.term_zero]
  · simp [charToAF, hn]

private noncomputable def estChi3 {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    DirichletCharacter ℂ (q₁ * q₂) :=
  DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ *
  DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂

private noncomputable def estConv {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    ArithmeticFunction ℂ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
    charToAF χ₁ * charToAF χ₂ * charToAF (estChi3 χ₁ χ₂)

private lemma zetaAF_LSeriesSummable {z : ℂ} (hz : 1 < z.re) :
    LSeriesSummable (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) z := by
  refine (LSeriesSummable_one_iff.mpr hz).congr fun n => ?_
  by_cases hn : n = 0
  · subst hn; simp [LSeries.term_zero]
  · simp [LSeries.term_of_ne_zero hn, ArithmeticFunction.zeta_apply, hn, one_div]

private lemma zetaAF_LSeries_eq {z : ℂ} (hz : 1 < z.re) :
    LSeries (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) z = riemannZeta z := by
  rw [← LSeries_one_eq_riemannZeta hz]
  refine LSeries_congr ?_ z
  intro n hn
  simp [ArithmeticFunction.zeta_apply, hn]

private lemma estChi3_prime {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    {p : ℕ} (hp : p.Prime) :
    estChi3 χ₁ χ₂ p = χ₁ p * χ₂ p := by
  have : NeZero (q₁ * q₂) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩
  dsimp only [estChi3]
  rw [MulChar.mul_apply]
  by_cases h1 : p ∣ q₁
  · have hc1 : χ₁ p = 0 := χ₁.map_nonunit (by
      rw [ZMod.isUnit_iff_coprime]
      intro hcop
      have := Nat.dvd_gcd (dvd_refl p) h1
      rw [hcop] at this
      exact hp.not_dvd_one this)
    have hc3 : DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ p = 0 :=
      (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁).map_nonunit (by
        rw [ZMod.isUnit_iff_coprime]
        intro hcop
        have := Nat.dvd_gcd (dvd_refl p) (dvd_mul_of_dvd_left h1 q₂)
        rw [hcop] at this
        exact hp.not_dvd_one this)
    rw [hc1, hc3, zero_mul, zero_mul]
  · by_cases h2 : p ∣ q₂
    · have hc2 : χ₂ p = 0 := χ₂.map_nonunit (by
        rw [ZMod.isUnit_iff_coprime]
        intro hcop
        have := Nat.dvd_gcd (dvd_refl p) h2
        rw [hcop] at this
        exact hp.not_dvd_one this)
      have hc3 : DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂ p = 0 :=
        (DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂).map_nonunit (by
          rw [ZMod.isUnit_iff_coprime]
          intro hcop
          have := Nat.dvd_gcd (dvd_refl p) (dvd_mul_of_dvd_right h2 q₁)
          rw [hcop] at this
          exact hp.not_dvd_one this)
      rw [hc2, hc3, mul_zero, mul_zero]
    · have hcop : Nat.Coprime p (q₁ * q₂) :=
        (hp.coprime_iff_not_dvd.mpr h1).mul_right (hp.coprime_iff_not_dvd.mpr h2)
      have hu : IsUnit ((p : ℕ) : ZMod (q₁ * q₂)) := (ZMod.isUnit_iff_coprime p (q₁ * q₂)).mpr hcop
      have hpeq : ((p : ℕ) : ZMod (q₁ * q₂)) = (hu.unit : ZMod (q₁ * q₂)) := hu.unit_spec.symm
      rw [hpeq, DirichletCharacter.changeLevel_eq_cast_of_dvd χ₁ (dvd_mul_right q₁ q₂) hu.unit,
        DirichletCharacter.changeLevel_eq_cast_of_dvd χ₂ (dvd_mul_left q₂ q₁) hu.unit,
        ← hpeq, ZMod.cast_natCast (dvd_mul_right q₁ q₂) p, ZMod.cast_natCast (dvd_mul_left q₂ q₁) p]

private lemma estConv_isMultiplicative {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    (estConv χ₁ χ₂).IsMultiplicative := by
  have hz : ((ArithmeticFunction.zeta : ArithmeticFunction ℂ)).IsMultiplicative := by
    refine ⟨by simp [ArithmeticFunction.zeta_apply], fun {m n} _ => ?_⟩
    by_cases hm : m = 0
    · subst hm; simp [ArithmeticFunction.zeta_apply]
    · by_cases hn : n = 0
      · subst hn; simp [ArithmeticFunction.zeta_apply]
      · simp [ArithmeticFunction.zeta_apply, hm, hn, mul_ne_zero]
  exact ((hz.mul (charToAF_isMultiplicative χ₁)).mul
    (charToAF_isMultiplicative χ₂)).mul (charToAF_isMultiplicative (estChi3 χ₁ χ₂))

private lemma estConv_prime_pow_nonneg {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁₂ : χ₁ ^ 2 = 1) (hχ₂₂ : χ₂ ^ 2 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ estConv χ₁ χ₂ (p ^ k) := by
  let χ₃ := estChi3 χ₁ χ₂
  have h1 : ∀ (f g : ArithmeticFunction ℂ) (m : ℕ),
      (f * g) (p ^ m) = ∑ i ∈ Finset.range (m + 1), f (p ^ i) * g (p ^ (m - i)) := by
    intro f g m
    rw [ArithmeticFunction.mul_apply]
    symm
    refine Finset.sum_bij (fun i _ => (p ^ i, p ^ (m - i))) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [Nat.mem_divisorsAntidiagonal]
      exact ⟨by rw [← pow_add, show i + (m - i) = m by omega], pow_ne_zero m hp.ne_zero⟩
    · intro i₁ _ i₂ _ heq
      have hfst : p ^ i₁ = p ^ i₂ := congrArg Prod.fst heq
      exact Nat.pow_right_injective hp.two_le hfst
    · intro x hx
      rw [Nat.mem_divisorsAntidiagonal] at hx
      obtain ⟨i, him, hx1⟩ := (Nat.dvd_prime_pow hp).mp ⟨x.2, hx.1.symm⟩
      have hx2 : x.2 = p ^ (m - i) := by
        apply mul_left_cancel₀ (pow_ne_zero i hp.ne_zero)
        rw [← hx1, hx.1, hx1, ← pow_add, show i + (m - i) = m by omega]
      exact ⟨i, Finset.mem_range.mpr (by omega), Prod.ext hx1.symm hx2.symm⟩
    · intro _ _; rfl
  have hval : ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) (m : ℕ),
      charToAF χ (p ^ m) = (χ p) ^ m := fun {N} χ m => by
    simp [charToAF, hp.ne_zero, map_pow]
  have hstep1 : ∀ m : ℕ, ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * charToAF χ₁) (p ^ m) =
      ∑ i ∈ Finset.range (m + 1), (χ₁ p) ^ i := fun m => by
    rw [h1]
    have hrev : ∑ i ∈ Finset.range (m + 1), (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p ^ i) *
        charToAF χ₁ (p ^ (m - i)) = ∑ i ∈ Finset.range (m + 1), (χ₁ p) ^ (m - i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hval]; simp [ArithmeticFunction.zeta_apply, hp.ne_zero]
    rw [hrev]; exact Finset.sum_range_reflect (fun i => (χ₁ p) ^ i) (m + 1)
  have hstep2 : ∀ m : ℕ, (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * charToAF χ₁) *
      charToAF χ₂) (p ^ m) =
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1 - i), (χ₁ p) ^ i * (χ₂ p) ^ j := fun m => by
    rw [h1]
    have hrev : ∑ j ∈ Finset.range (m + 1),
        ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * charToAF χ₁) (p ^ j) *
          charToAF χ₂ (p ^ (m - j)) =
        ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (m - j + 1), (χ₁ p) ^ i * (χ₂ p) ^ j := by
      have hr := Finset.sum_range_reflect (fun j =>
        ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * charToAF χ₁) (p ^ (m - j)) *
          charToAF χ₂ (p ^ j)) (m + 1)
      calc ∑ j ∈ Finset.range (m + 1),
            ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * charToAF χ₁) (p ^ j) *
              charToAF χ₂ (p ^ (m - j))
          = ∑ j ∈ Finset.range (m + 1),
              ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * charToAF χ₁) (p ^ (m - (m + 1 - 1 - j))) *
                charToAF χ₂ (p ^ (m + 1 - 1 - j)) := by
              refine Finset.sum_congr rfl fun j hj => ?_
              rw [Finset.mem_range] at hj
              rw [show m + 1 - 1 - j = m - j by omega, show m - (m - j) = j by omega]
        _ = ∑ j ∈ Finset.range (m + 1),
              ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * charToAF χ₁) (p ^ (m - j)) *
                charToAF χ₂ (p ^ j) := hr
        _ = ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (m - j + 1), (χ₁ p) ^ i * (χ₂ p) ^ j :=
              Finset.sum_congr rfl fun j _ => by rw [hstep1, hval, Finset.sum_mul]
    rw [hrev, Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij (fun q _ => ⟨q.2, q.1⟩) ?_ ?_ ?_ ?_
    · intro q hq; simp only [Finset.mem_sigma, Finset.mem_range] at hq ⊢; omega
    · intro q₁ _ q₂ _ heq; rcases q₁ with ⟨a₁, b₁⟩; rcases q₂ with ⟨a₂, b₂⟩
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq; obtain ⟨rfl, rfl⟩ := heq; rfl
    · intro q hq; simp only [Finset.mem_sigma, Finset.mem_range] at hq
      exact ⟨⟨q.2, q.1⟩, by simp only [Finset.mem_sigma, Finset.mem_range]; omega, rfl⟩
    · intro _ _; rfl
  have hconv_val : estConv χ₁ χ₂ (p ^ k) =
      ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 - i),
        ∑ l ∈ Finset.range (k + 1 - i - j), (χ₁ p) ^ i * (χ₂ p) ^ j * (χ₃ p) ^ l := by
    dsimp only [estConv]; rw [h1]
    have h3 : ∑ l ∈ Finset.range (k + 1),
        (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * charToAF χ₁) *
          charToAF χ₂) (p ^ l) * charToAF χ₃ (p ^ (k - l)) =
        ∑ l ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k - l + 1),
          ∑ j ∈ Finset.range (k - l + 1 - i), (χ₁ p) ^ i * (χ₂ p) ^ j * (χ₃ p) ^ l := by
      have hr := Finset.sum_range_reflect (fun l =>
        (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * charToAF χ₁) *
          charToAF χ₂) (p ^ (k - l)) * charToAF χ₃ (p ^ l)) (k + 1)
      calc ∑ l ∈ Finset.range (k + 1),
            (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * charToAF χ₁) *
              charToAF χ₂) (p ^ l) * charToAF χ₃ (p ^ (k - l))
          = ∑ l ∈ Finset.range (k + 1),
              (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * charToAF χ₁) *
                charToAF χ₂) (p ^ (k - (k + 1 - 1 - l))) * charToAF χ₃ (p ^ (k + 1 - 1 - l)) := by
              refine Finset.sum_congr rfl fun l hl => ?_
              rw [Finset.mem_range] at hl
              rw [show k + 1 - 1 - l = k - l by omega, show k - (k - l) = l by omega]
        _ = ∑ l ∈ Finset.range (k + 1),
              (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * charToAF χ₁) *
                charToAF χ₂) (p ^ (k - l)) * charToAF χ₃ (p ^ l) := hr
        _ = ∑ l ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k - l + 1),
              ∑ j ∈ Finset.range (k - l + 1 - i), (χ₁ p) ^ i * (χ₂ p) ^ j * (χ₃ p) ^ l :=
              Finset.sum_congr rfl fun l _ => by
                rw [hstep2, hval, Finset.sum_mul]
                exact Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
    rw [h3]
    have hcube : ∀ f : ℕ → ℕ → ℕ → ℂ,
        (∑ x ∈ Finset.range (k + 1), ∑ y ∈ Finset.range (k + 1 - x),
          ∑ z ∈ Finset.range (k + 1 - x - y), f x y z) =
        ∑ q ∈ ((Finset.range (k + 1) ×ˢ Finset.range (k + 1)) ×ˢ Finset.range (k + 1)).filter
          (fun q => q.1.1 + q.1.2 + q.2 ≤ k), f q.1.1 q.1.2 q.2 := by
      intro f
      rw [Finset.sum_filter, Finset.sum_product, Finset.sum_product]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_range] at hx
      rw [← Finset.sum_subset (show Finset.range (k + 1 - x) ⊆ Finset.range (k + 1) by
        intro y hy; rw [Finset.mem_range] at hy ⊢; omega)]
      · refine Finset.sum_congr rfl fun y hy => ?_
        rw [Finset.mem_range] at hy
        rw [← Finset.sum_subset (show Finset.range (k + 1 - x - y) ⊆ Finset.range (k + 1) by
          intro z hz; rw [Finset.mem_range] at hz ⊢; omega)]
        · refine Finset.sum_congr rfl fun z hz => by rw [Finset.mem_range] at hz; dsimp only; rw [if_pos (by omega)]
        · intro z hz hnz; rw [Finset.mem_range] at hz hnz; dsimp only; rw [if_neg (by omega)]
      · intro y hy hny; rw [Finset.mem_range] at hy hny
        exact Finset.sum_eq_zero fun z _ => by dsimp only; rw [if_neg (by omega)]
    have hlhs_eq : (∑ l ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k - l + 1),
        ∑ j ∈ Finset.range (k - l + 1 - i), (χ₁ p) ^ i * (χ₂ p) ^ j * (χ₃ p) ^ l) =
        ∑ l ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k + 1 - l),
          ∑ j ∈ Finset.range (k + 1 - l - i), (χ₁ p) ^ i * (χ₂ p) ^ j * (χ₃ p) ^ l := by
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [Finset.mem_range] at hl
      rw [show k - l + 1 = k + 1 - l by omega]
    rw [hlhs_eq, hcube, hcube]
    refine Finset.sum_bij (fun q _ => ((q.1.2, q.2), q.1.1)) ?_ ?_ ?_ ?_
    · intro q hq; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq ⊢; omega
    · intro q₁ _ q₂ _ heq; rcases q₁ with ⟨⟨l₁, i₁⟩, j₁⟩; rcases q₂ with ⟨⟨l₂, i₂⟩, j₂⟩
      simp only [Prod.mk.injEq] at heq; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq; rfl
    · intro q hq; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
      exact ⟨((q.2, q.1.1), q.1.2), by simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega, rfl⟩
    · intro _ _; rfl
  rw [hconv_val, estChi3_prime χ₁ χ₂ hp]
  obtain ⟨hi1, hr1⟩ := real_char_im_eq_zero hχ₁₂ p
  obtain ⟨hi2, hr2⟩ := real_char_im_eq_zero hχ₂₂ p
  have hc1 : χ₁ p = ((χ₁ p).re : ℂ) := Complex.ext rfl (by simpa using hi1)
  have hc2 : χ₂ p = ((χ₂ p).re : ℂ) := Complex.ext rfl (by simpa using hi2)
  rw [hc1, hc2]
  have hcast : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 - i),
      ∑ l ∈ Finset.range (k + 1 - i - j),
        (((χ₁ p).re : ℂ) ^ i * ((χ₂ p).re : ℂ) ^ j * (((χ₁ p).re : ℂ) * ((χ₂ p).re : ℂ)) ^ l)) =
      (((∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 - i),
        ∑ l ∈ Finset.range (k + 1 - i - j),
          ((χ₁ p).re) ^ i * ((χ₂ p).re) ^ j * (((χ₁ p).re) * ((χ₂ p).re)) ^ l : ℝ)) : ℂ) := by
    push_cast; rfl
  rw [hcast, Complex.zero_le_real]
  exact conv4_prime_pow_nonneg _ _ hr1 hr2 k

/-- Helper 1 for Estermann: the 4-fold Dirichlet convolution `a = ζ * χ₁ * χ₂ * χ₃` is nonnegative,
has `a 1 = 1`, `LSeries a z = ζ(z) L₁(z) L₂(z) L₃(z)` for `Re z > 1`, and abscissa `≤ 1`. -/
private lemma estermann_conv_props {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hχ₁₂ : χ₁ ^ 2 = 1) (hχ₂₂ : χ₂ ^ 2 = 1) :
    estConv χ₁ χ₂ 1 = 1 ∧ (∀ n : ℕ, 0 ≤ estConv χ₁ χ₂ n) ∧
      (∀ z : ℂ, 1 < z.re →
        LSeries (estConv χ₁ χ₂ ·) z = riemannZeta z * DirichletCharacter.LFunction χ₁ z *
          DirichletCharacter.LFunction χ₂ z * DirichletCharacter.LFunction (estChi3 χ₁ χ₂) z) ∧
      LSeries.abscissaOfAbsConv (estConv χ₁ χ₂ ·) ≤ 1 := by
  have : NeZero (q₁ * q₂) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩
  let χ₃ := estChi3 χ₁ χ₂
  let a := estConv χ₁ χ₂
  have ha_mult : a.IsMultiplicative := estConv_isMultiplicative χ₁ χ₂
  have ha1 : a 1 = 1 := ha_mult.1
  have ha_nonneg : ∀ n : ℕ, 0 ≤ a n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [a]
    · rw [ha_mult.multiplicative_factorization a hn0]
      exact Finset.prod_nonneg fun p hp =>
        estConv_prime_pow_nonneg χ₁ χ₂ hχ₁₂ hχ₂₂
          (Nat.prime_of_mem_primeFactors (by simpa using hp)) (n.factorization p)
  have hLa_eq : ∀ z : ℂ, 1 < z.re →
      LSeries (a ·) z = riemannZeta z * DirichletCharacter.LFunction χ₁ z *
        DirichletCharacter.LFunction χ₂ z * DirichletCharacter.LFunction χ₃ z := by
    intro z hz
    have hsζ := zetaAF_LSeriesSummable hz
    have hs1 := charToAF_LSeriesSummable χ₁ hz
    have hs2 := charToAF_LSeriesSummable χ₂ hz
    have hs3 := charToAF_LSeriesSummable χ₃ hz
    have hmul1 := ArithmeticFunction.LSeriesSummable_mul hsζ hs1
    have hmul2 := ArithmeticFunction.LSeriesSummable_mul hmul1 hs2
    have h1 : LSeries (a ·) z =
        LSeries (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) z *
        LSeries (fun n => charToAF χ₁ n) z *
        LSeries (fun n => charToAF χ₂ n) z *
        LSeries (fun n => charToAF χ₃ n) z := by
      dsimp only [a, estConv]
      rw [ArithmeticFunction.LSeries_mul' hmul2 hs3, ArithmeticFunction.LSeries_mul' hmul1 hs2,
        ArithmeticFunction.LSeries_mul' hsζ hs1]
    rw [h1, zetaAF_LSeries_eq hz, charToAF_LSeries_eq, charToAF_LSeries_eq, charToAF_LSeries_eq,
      DirichletCharacter.LFunction_eq_LSeries χ₁ hz, DirichletCharacter.LFunction_eq_LSeries χ₂ hz,
      DirichletCharacter.LFunction_eq_LSeries χ₃ hz]
  have habs_le : LSeries.abscissaOfAbsConv (a ·) ≤ 1 := by
    refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun x hx => ?_
    have hz : 1 < (x : ℂ).re := by simpa using hx
    exact ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_mul (zetaAF_LSeriesSummable hz) (charToAF_LSeriesSummable χ₁ hz))
        (charToAF_LSeriesSummable χ₂ hz))
      (charToAF_LSeriesSummable χ₃ hz)
  exact ⟨ha1, ha_nonneg, hLa_eq, habs_le⟩

set_option maxHeartbeats 600000 in
/-- Core Estermann inequality for two real characters `χ₁` (mod `q₁`), `χ₂` (mod `q₂`) whose product `χ₃` (mod `q₁*q₂`) is nontrivial. -/
theorem estermann_ineq :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧
      ∀ {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
        (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
        (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₁₂ : χ₁ ^ 2 = 1) (hχ₂₂ : χ₂ ^ 2 = 1),
        letI : NeZero (q₁ * q₂) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩
        let χ₃ : DirichletCharacter ℂ (q₁ * q₂) :=
          DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ *
          DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂
        χ₃ ≠ 1 →
        ∀ β : ℝ, (7 / 8 : ℝ) ≤ β → β < 1 →
          let lam : ℝ := (DirichletCharacter.LFunction χ₁ 1 *
            DirichletCharacter.LFunction χ₂ 1 * DirichletCharacter.LFunction χ₃ 1).re
          let Fβ : ℝ := (riemannZeta (β : ℂ) * DirichletCharacter.LFunction χ₁ (β : ℂ) *
            DirichletCharacter.LFunction χ₂ (β : ℂ) * DirichletCharacter.LFunction χ₃ (β : ℂ)).re
          ∀ M : ℕ, 1 ≤ M →
            1 - lam * ((2 - β) ^ M) / (1 - β) -
              4 * C₁ * ((q₁ * q₂ : ℝ) ^ 2) * ((3 / 4 : ℝ) ^ M) ≤ Fβ := by
  obtain ⟨C₀, hC₀ge, hC₀⟩ := exists_zeta_sphere_bound
  refine ⟨1331 * C₀ + 54, by linarith, ?_⟩
  intro q₁ q₂ _ _ χ₁ χ₂ hχ₁ hχ₂ hχ₁₂ hχ₂₂ χ₃ hχ₃ β hβl hβu lam Fβ M hM1
  have : NeZero (q₁ * q₂) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩
  have hχ₃₂ : χ₃ ^ 2 = 1 := by
    dsimp only [χ₃]
    rw [mul_pow, ← map_pow, ← map_pow, hχ₁₂, hχ₂₂, map_one, map_one, one_mul]
  let a : ArithmeticFunction ℂ := estConv χ₁ χ₂
  obtain ⟨ha1, ha_nonneg, hLa_eq, habs_le⟩ := estermann_conv_props χ₁ χ₂ hχ₁₂ hχ₂₂
  -- Entire function H(z) = zetaTimesSubOne z * L₁ z * L₂ z * L₃ z, and G = dslope H 1
  let H : ℂ → ℂ := fun z => zetaTimesSubOne z * DirichletCharacter.LFunction χ₁ z *
    DirichletCharacter.LFunction χ₂ z * DirichletCharacter.LFunction χ₃ z
  have hHdiff : Differentiable ℂ H :=
    ((differentiable_zetaTimesSubOne.mul (DirichletCharacter.differentiable_LFunction hχ₁)).mul
      (DirichletCharacter.differentiable_LFunction hχ₂)).mul
      (DirichletCharacter.differentiable_LFunction hχ₃)
  let lamC : ℂ := DirichletCharacter.LFunction χ₁ 1 *
    DirichletCharacter.LFunction χ₂ 1 * DirichletCharacter.LFunction χ₃ 1
  have hH1 : H 1 = lamC := by simp [H, lamC, zetaTimesSubOne_one]
  let G : ℂ → ℂ := dslope H 1
  have hGdiff : Differentiable ℂ G := by
    have hOn := (Complex.differentiableOn_dslope (c := (1 : ℂ)) (s := Set.univ) Filter.univ_mem).mpr
      hHdiff.differentiableOn
    exact differentiableOn_univ.mp hOn
  have hG_ne : ∀ z : ℂ, z ≠ 1 →
      G z = riemannZeta z * DirichletCharacter.LFunction χ₁ z *
        DirichletCharacter.LFunction χ₂ z * DirichletCharacter.LFunction χ₃ z - lamC / (z - 1) := by
    intro z hz
    dsimp only [G]
    rw [dslope_of_ne _ hz, slope_def_field, hH1]
    dsimp only [H]
    rw [zetaTimesSubOne_ne_one hz]
    have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    field_simp
  -- lamC is real
  have hlam_im : lamC.im = 0 := by
    have h1 := LFunction_im_eq_zero_of_real hχ₁ hχ₁₂ one_pos
    have h2 := LFunction_im_eq_zero_of_real hχ₂ hχ₂₂ one_pos
    have h3 := LFunction_im_eq_zero_of_real hχ₃ hχ₃₂ one_pos
    simp only [lamC, ofReal_one] at h1 h2 h3 ⊢
    simp [Complex.mul_im, h1, h2, h3]
  have hlam_eq : lamC = (lam : ℂ) := Complex.ext rfl (by simpa using hlam_im)
  -- Sphere bound on G on |z - 2| = 3/2
  have hG_sphere : ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2 : ℝ),
      ‖G z‖ ≤ (1331 * C₀ + 54) * ((q₁ * q₂ : ℝ) ^ 2) := by
    intro z hz
    have hdist : ‖z - 2‖ = 3 / 2 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hzre : (1 / 2 : ℝ) ≤ z.re := by
      have : |z.re - 2| ≤ 3 / 2 := by
        have := Complex.abs_re_le_norm (z - 2)
        simpa [hdist] using this
      linarith [(abs_le.mp this).1]
    have hznorm : ‖z‖ ≤ 7 / 2 := by
      calc ‖z‖ = ‖(z - 2) + 2‖ := by ring_nf
        _ ≤ ‖z - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
        _ = 3 / 2 + 2 := by rw [hdist]; norm_num
        _ = 7 / 2 := by norm_num
    have hz1norm : (1 / 2 : ℝ) ≤ ‖z - 1‖ := by
      have htri : ‖z - 2‖ ≤ ‖z - 1‖ + ‖(-1 : ℂ)‖ := by
        have : z - 2 = (z - 1) + (-1) := by ring
        rw [this]; exact norm_add_le _ _
      rw [hdist, norm_neg, norm_one] at htri
      linarith
    have hz1 : z ≠ 1 := by
      intro h; rw [h, sub_self, norm_zero] at hz1norm; linarith
    rw [hG_ne z hz1]
    have hbζ : ‖riemannZeta z‖ ≤ C₀ := hC₀ z hz
    have hb1 : ‖DirichletCharacter.LFunction χ₁ z‖ ≤ 11 * (q₁ : ℝ) :=
      (norm_LFunction_le_of_re_ge_half χ₁ hχ₁ hzre).trans (by nlinarith [show (0 : ℝ) ≤ q₁ by positivity])
    have hb2 : ‖DirichletCharacter.LFunction χ₂ z‖ ≤ 11 * (q₂ : ℝ) :=
      (norm_LFunction_le_of_re_ge_half χ₂ hχ₂ hzre).trans (by nlinarith [show (0 : ℝ) ≤ q₂ by positivity])
    have hb3 : ‖DirichletCharacter.LFunction χ₃ z‖ ≤ 11 * ((q₁ * q₂ : ℕ) : ℝ) :=
      (norm_LFunction_le_of_re_ge_half χ₃ hχ₃ hzre).trans (by nlinarith [show (0 : ℝ) ≤ (q₁ * q₂ : ℕ) by positivity])
    have hbl1 : ‖DirichletCharacter.LFunction χ₁ 1‖ ≤ 3 * (q₁ : ℝ) := by
      simpa using norm_LFunction_le_of_re_ge_half χ₁ hχ₁ (s := 1) (by norm_num)
    have hbl2 : ‖DirichletCharacter.LFunction χ₂ 1‖ ≤ 3 * (q₂ : ℝ) := by
      simpa using norm_LFunction_le_of_re_ge_half χ₂ hχ₂ (s := 1) (by norm_num)
    have hbl3 : ‖DirichletCharacter.LFunction χ₃ 1‖ ≤ 3 * ((q₁ * q₂ : ℕ) : ℝ) := by
      simpa using norm_LFunction_le_of_re_ge_half χ₃ hχ₃ (s := 1) (by norm_num)
    have hF : ‖riemannZeta z * DirichletCharacter.LFunction χ₁ z *
        DirichletCharacter.LFunction χ₂ z * DirichletCharacter.LFunction χ₃ z‖ ≤
        1331 * C₀ * ((q₁ * q₂ : ℝ) ^ 2) := by
      rw [norm_mul, norm_mul, norm_mul]
      push_cast at hb3
      have h12 : ‖riemannZeta z‖ * ‖DirichletCharacter.LFunction χ₁ z‖ ≤ C₀ * (11 * q₁) :=
        mul_le_mul hbζ hb1 (norm_nonneg _) (by positivity)
      have h123 : ‖riemannZeta z‖ * ‖DirichletCharacter.LFunction χ₁ z‖ *
          ‖DirichletCharacter.LFunction χ₂ z‖ ≤ C₀ * (11 * q₁) * (11 * q₂) :=
        mul_le_mul h12 hb2 (norm_nonneg _) (by positivity)
      have h1234 : ‖riemannZeta z‖ * ‖DirichletCharacter.LFunction χ₁ z‖ *
          ‖DirichletCharacter.LFunction χ₂ z‖ * ‖DirichletCharacter.LFunction χ₃ z‖ ≤
          C₀ * (11 * q₁) * (11 * q₂) * (11 * (q₁ * q₂)) :=
        mul_le_mul h123 hb3 (norm_nonneg _) (by positivity)
      linarith
    have hL : ‖lamC / (z - 1)‖ ≤ 54 * ((q₁ * q₂ : ℝ) ^ 2) := by
      rw [norm_div]
      have hlam_b : ‖lamC‖ ≤ 27 * ((q₁ * q₂ : ℝ) ^ 2) := by
        dsimp only [lamC]; rw [norm_mul, norm_mul]; push_cast at hbl3
        have h12 := mul_le_mul hbl1 hbl2 (norm_nonneg _) (by positivity)
        have h123 := mul_le_mul h12 hbl3 (norm_nonneg _) (by positivity)
        linarith
      calc ‖lamC‖ / ‖z - 1‖ ≤ (27 * ((q₁ * q₂ : ℝ) ^ 2)) / (1 / 2) :=
            div_le_div₀ (by positivity) hlam_b (by norm_num) hz1norm
        _ = 54 * ((q₁ * q₂ : ℝ) ^ 2) := by ring
    exact (norm_sub_le _ _).trans (by linarith)
  -- Taylor series of G centered at 2 evaluated at β
  have hTaylor := Complex.hasSum_taylorSeries_of_entire hGdiff 2 (β : ℂ)
  -- Identify iteratedDeriv m G 2 using equality on {z | 1 < z.re}
  have hEqGt1 : Set.EqOn G (fun z => LSeries (a ·) z - lamC * (z - 1)⁻¹) {z : ℂ | 1 < z.re} := by
    intro z hz
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
    rw [hG_ne z hz1]
    exact congrArg (· - lamC * (z - 1)⁻¹) (hLa_eq z hz).symm |>.trans (by ring) |> fun h => by
      rw [div_eq_mul_inv]; exact h
  have hOpenGt1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2mem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by simp
  have hinv_deriv : ∀ m : ℕ, iteratedDeriv m (fun z : ℂ => lamC * (z - 1)⁻¹) (2 : ℂ) =
      lamC * ((-1 : ℂ) ^ m * (m.factorial : ℂ)) := by
    have hgen : ∀ m : ℕ, ∀ z : ℂ, z ≠ 1 →
        iteratedDeriv m (fun w : ℂ => lamC * (w - 1)⁻¹) z =
          lamC * ((-1 : ℂ) ^ m * (m.factorial : ℂ) * (z - 1) ^ (-(m + 1 : ℤ))) := by
      intro m
      induction m with
      | zero => intro z _; simp
      | succ m ih =>
        intro z hz
        rw [iteratedDeriv_succ]
        have hev : iteratedDeriv m (fun w : ℂ => lamC * (w - 1)⁻¹) =ᶠ[𝓝 z]
            fun w => lamC * ((-1 : ℂ) ^ m * (m.factorial : ℂ) * (w - 1) ^ (-(m + 1 : ℤ))) := by
          filter_upwards [isOpen_ne.mem_nhds hz] with w hw
          exact ih w hw
        rw [hev.deriv_eq]
        have hd : HasDerivAt (fun w : ℂ => lamC * ((-1 : ℂ) ^ m * (m.factorial : ℂ) * (w - 1) ^ (-(m + 1 : ℤ))))
            (lamC * ((-1 : ℂ) ^ m * (m.factorial : ℂ) * (((-(m + 1 : ℤ) : ℤ) : ℂ) * (z - 1) ^ (-(m + 1 : ℤ) - 1)))) z := by
          refine HasDerivAt.const_mul _ (HasDerivAt.const_mul _ ?_)
          have hsub : HasDerivAt (fun w : ℂ => w - 1) 1 z :=
            (hasDerivAt_id z).sub_const 1
          have hzpow := hasDerivAt_zpow (-(m + 1 : ℤ)) (z - 1) (Or.inl (sub_ne_zero.mpr hz))
          have hcomp := hzpow.comp z hsub
          simpa only [Function.comp_def, mul_one] using hcomp
        rw [hd.deriv]
        have hexp : (-(m + 1 : ℤ) - 1 : ℤ) = -((m + 1 : ℕ) + 1 : ℤ) := by omega
        rw [hexp, Nat.factorial_succ]
        push_cast
        ring
    intro m
    have h := hgen m 2 (by norm_num)
    rw [show (2 : ℂ) - 1 = 1 by norm_num, one_zpow, mul_one] at h
    exact h
  have hderivG : ∀ m : ℕ,
      iteratedDeriv m G 2 =
        iteratedDeriv m (LSeries (a ·)) 2 - lamC * ((-1 : ℂ) ^ m * (m.factorial : ℂ)) := by
    intro m
    rw [hEqGt1.iteratedDeriv_of_isOpen hOpenGt1 m h2mem]
    have hAn1 : AnalyticAt ℂ (LSeries (a ·)) 2 := by
      have hdiff : DifferentiableOn ℂ (LSeries (a ·)) {z : ℂ | 1 < z.re} := by
        have hEqRhs : Set.EqOn (LSeries (a ·))
            (fun z => riemannZeta z * DirichletCharacter.LFunction χ₁ z *
              DirichletCharacter.LFunction χ₂ z * DirichletCharacter.LFunction χ₃ z)
            {z : ℂ | 1 < z.re} := fun z hz => hLa_eq z hz
        refine DifferentiableOn.congr ?_ hEqRhs
        intro z hz
        have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
        exact ((((differentiableAt_riemannZeta hz1).mul
          (DirichletCharacter.differentiable_LFunction hχ₁ z)).mul
          (DirichletCharacter.differentiable_LFunction hχ₂ z)).mul
          (DirichletCharacter.differentiable_LFunction hχ₃ z)).differentiableWithinAt
      exact hdiff.analyticAt (hOpenGt1.mem_nhds h2mem)
    have hinvAn : AnalyticAt ℂ (fun z : ℂ => (z - 1)⁻¹) 2 :=
      (analyticAt_id.sub analyticAt_const).inv (by norm_num)
    have hAn2 : AnalyticAt ℂ (fun z : ℂ => lamC * (z - 1)⁻¹) 2 :=
      analyticAt_const.mul hinvAn
    change iteratedDeriv m ((LSeries (a ·)) - (fun z => lamC * (z - 1)⁻¹)) 2 = _
    rw [iteratedDeriv_sub (hAn1.contDiffAt.of_le le_top) (hAn2.contDiffAt.of_le le_top),
      hinv_deriv m]
  -- Each term in the Taylor series at β:
  let c : ℕ → ℂ := fun m => (m.factorial : ℂ)⁻¹ * ((β : ℂ) - 2) ^ m * iteratedDeriv m G 2
  have hTaylor' : HasSum c (G (β : ℂ)) :=
    hTaylor.congr_fun fun m => by simp [c, smul_eq_mul, mul_assoc]
  -- Split Taylor series at M: G β = (∑_{m < M} c m) + (∑'_{m} c (m + M))
  have hsplit : G (β : ℂ) = (∑ m ∈ Finset.range M, c m) + ∑' m : ℕ, c (m + M) :=
    hTaylor'.tsum_eq.symm.trans (hTaylor'.summable.sum_add_tsum_nat_add M).symm
  -- Real part of head sum:
  have hhead_re : ∀ m : ℕ, (c m).re =
      (((m.factorial : ℝ)⁻¹ * ((-1 : ℂ) ^ m * iteratedDeriv m (LSeries (a ·)) 2).re) - lam) *
        (2 - β) ^ m := by
    intro m
    dsimp only [c]
    rw [hderivG m]
    have hneg : ((β : ℂ) - 2) ^ m = (-1 : ℂ) ^ m * ((2 - β : ℝ) : ℂ) ^ m := by
      rw [← mul_pow]; congr 1; push_cast; ring
    have hfact_ne : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hrew : (m.factorial : ℂ)⁻¹ * ((β : ℂ) - 2) ^ m *
        (iteratedDeriv m (LSeries (a ·)) 2 - lamC * ((-1 : ℂ) ^ m * (m.factorial : ℂ))) =
        ((m.factorial : ℂ)⁻¹ * ((-1 : ℂ) ^ m * iteratedDeriv m (LSeries (a ·)) 2) - lamC) *
          ((2 - β : ℝ) : ℂ) ^ m := by
      rw [hneg]
      have hsq : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by rw [← mul_pow]; norm_num
      field_simp
      linear_combination -lamC * (m.factorial : ℂ) * ((2 - β : ℝ) : ℂ) ^ m * hsq
    rw [hrew, ← ofReal_pow, mul_re, ofReal_im, mul_zero, sub_zero, sub_re, ← ofReal_natCast,
      ← ofReal_inv, mul_re, ofReal_im, zero_mul, sub_zero, hlam_eq, ofReal_re, ofReal_re, ofReal_re]
  have hb_nonneg : ∀ m : ℕ, 0 ≤ ((-1 : ℂ) ^ m * iteratedDeriv m (LSeries (a ·)) 2).re := by
    intro m
    have hlt2 : (1 : EReal) < ((2 : ℝ) : EReal) := by
      change ((1 : ℝ) : EReal) < ((2 : ℝ) : EReal)
      exact EReal.coe_lt_coe_iff.mpr (by norm_num)
    have h := LSeries.iteratedDeriv_alternating ha_nonneg (x := (2 : ℝ))
      (lt_of_le_of_lt habs_le hlt2) m
    have h2c : ((2 : ℝ) : ℂ) = 2 := by norm_num
    rw [h2c] at h
    exact (Complex.le_def.mp h).1
  have hb0_ge_one : 1 ≤ (LSeries (a ·) 2).re := by
    have hsum : Summable (LSeries.term (a ·) 2) := by
      have hz2 : 1 < (2 : ℂ).re := by norm_num
      exact ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_mul
          (ArithmeticFunction.LSeriesSummable_mul (zetaAF_LSeriesSummable hz2) (charToAF_LSeriesSummable χ₁ hz2))
          (charToAF_LSeriesSummable χ₂ hz2))
        (charToAF_LSeriesSummable χ₃ hz2)
    have hsum_re : Summable (fun n : ℕ => (LSeries.term (a ·) 2 n).re) :=
      Complex.reCLM.summable hsum
    rw [LSeries, Complex.re_tsum hsum]
    have h1 : (LSeries.term (a ·) 2 1).re = 1 := by
      rw [LSeries.term_of_ne_zero one_ne_zero, ha1]; simp
    have hnn : ∀ n : ℕ, 0 ≤ (LSeries.term (a ·) 2 n).re := fun n =>
      (Complex.le_def.mp (LSeries.term_nonneg (ha_nonneg n) 2)).1
    have := hsum_re.le_tsum 1 (fun n _ => hnn n)
    linarith
  have hhead_ge : 1 - lam * ((2 - β) ^ M - 1) / (1 - β) ≤ (∑ m ∈ Finset.range M, c m).re := by
    rw [Complex.re_sum]
    simp_rw [hhead_re]
    -- Split sum of (b_m - lam) * (2 - β)^m
    have hsplit_sum : ∑ m ∈ Finset.range M,
        ((m.factorial : ℝ)⁻¹ * ((-1 : ℂ) ^ m * iteratedDeriv m (LSeries (a ·)) 2).re - lam) *
          (2 - β) ^ m =
        (∑ m ∈ Finset.range M, (m.factorial : ℝ)⁻¹ *
          ((-1 : ℂ) ^ m * iteratedDeriv m (LSeries (a ·)) 2).re * (2 - β) ^ m) -
        lam * (∑ m ∈ Finset.range M, (2 - β) ^ m) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => by ring
    rw [hsplit_sum]
    have hgeom : ∑ m ∈ Finset.range M, (2 - β) ^ m = ((2 - β) ^ M - 1) / (1 - β) := by
      have hne : (2 - β : ℝ) ≠ 1 := by linarith
      rw [geom_sum_eq hne]
      congr 1; ring
    rw [hgeom]
    have hfirst_ge : (if M = 0 then 0 else 1) ≤ ∑ m ∈ Finset.range M, (m.factorial : ℝ)⁻¹ *
        ((-1 : ℂ) ^ m * iteratedDeriv m (LSeries (a ·)) 2).re * (2 - β) ^ m := by
      cases M with
      | zero => simp
      | succ M =>
        simp only [Nat.succ_ne_zero, ↓reduceIte]
        rw [Finset.sum_range_succ']
        have hrest : 0 ≤ ∑ k ∈ Finset.range M, ((k + 1).factorial : ℝ)⁻¹ *
            ((-1 : ℂ) ^ (k + 1) * iteratedDeriv (k + 1) (LSeries (a ·)) 2).re * (2 - β) ^ (k + 1) :=
          Finset.sum_nonneg fun k _ => mul_nonneg (mul_nonneg (by positivity) (hb_nonneg _))
            (pow_nonneg (by linarith) _)
        simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_mul, mul_one,
          iteratedDeriv_zero]
        linarith
    cases M with
    | zero => omega
    | succ M =>
      simp only [Nat.succ_ne_zero, ↓reduceIte] at hfirst_ge
      rw [← mul_div_assoc]; linarith
  -- Tail bound using Cauchy estimate on sphere 2 (3/2)
  have htail_le : ‖∑' m : ℕ, c (m + M)‖ ≤ 4 * (1331 * C₀ + 54) * ((q₁ * q₂ : ℝ) ^ 2) * ((3 / 4 : ℝ) ^ M) := by
    have hcoeff : ∀ m : ℕ, ‖c m‖ ≤ (1331 * C₀ + 54) * ((q₁ * q₂ : ℝ) ^ 2) * ((3 / 4 : ℝ) ^ m) := by
      intro m
      dsimp only [c]
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
      have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m
        (by norm_num : (0 : ℝ) < 3 / 2) hGdiff.diffContOnCl hG_sphere
      have hβ2 : ‖(β : ℂ) - 2‖ ≤ 9 / 8 := by
        rw [show (β : ℂ) - 2 = ((β - 2 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
          Real.norm_eq_abs, abs_of_neg (by linarith)]
        linarith
      have hfac_pos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
      calc (m.factorial : ℝ)⁻¹ * ‖(β : ℂ) - 2‖ ^ m * ‖iteratedDeriv m G 2‖
          ≤ (m.factorial : ℝ)⁻¹ * (9 / 8 : ℝ) ^ m *
            ((m.factorial : ℝ) * ((1331 * C₀ + 54) * ((q₁ * q₂ : ℝ) ^ 2)) / (3 / 2 : ℝ) ^ m) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hβ2 m) (by positivity))
                hcauchy (norm_nonneg _) (by positivity)
        _ = (1331 * C₀ + 54) * ((q₁ * q₂ : ℝ) ^ 2) * ((3 / 4 : ℝ) ^ m) := by
              have hdiv : (9 / 8 : ℝ) ^ m / (3 / 2 : ℝ) ^ m = (3 / 4 : ℝ) ^ m := by
                rw [← div_pow]; norm_num
              have hne : (m.factorial : ℝ) ≠ 0 := hfac_pos.ne'
              calc (m.factorial : ℝ)⁻¹ * (9 / 8 : ℝ) ^ m *
                    ((m.factorial : ℝ) * ((1331 * C₀ + 54) * ((q₁ * q₂ : ℝ) ^ 2)) / (3 / 2 : ℝ) ^ m)
                  = ((m.factorial : ℝ)⁻¹ * (m.factorial : ℝ)) *
                    ((1331 * C₀ + 54) * ((q₁ * q₂ : ℝ) ^ 2)) *
                    ((9 / 8 : ℝ) ^ m / (3 / 2 : ℝ) ^ m) := by ring
                _ = (1331 * C₀ + 54) * ((q₁ * q₂ : ℝ) ^ 2) * ((3 / 4 : ℝ) ^ m) := by
                    rw [inv_mul_cancel₀ hne, one_mul, hdiv]
    have hshift : Summable (fun m : ℕ => c (m + M)) := (summable_nat_add_iff M).mpr hTaylor'.summable
    have hgeom_sum : Summable (fun m : ℕ => (1331 * C₀ + 54) * ((q₁ * q₂ : ℝ) ^ 2) * ((3 / 4 : ℝ) ^ (m + M))) := by
      have h1 : Summable (fun m : ℕ => (3 / 4 : ℝ) ^ m) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
      have h2 := (summable_nat_add_iff M).mpr h1
      exact h2.mul_left _
    calc ‖∑' m : ℕ, c (m + M)‖
        ≤ ∑' m : ℕ, ‖c (m + M)‖ := norm_tsum_le_tsum_norm hshift.norm
      _ ≤ ∑' m : ℕ, (1331 * C₀ + 54) * ((q₁ * q₂ : ℝ) ^ 2) * ((3 / 4 : ℝ) ^ (m + M)) :=
          hshift.norm.tsum_le_tsum (fun m => hcoeff (m + M)) hgeom_sum
      _ = (1331 * C₀ + 54) * ((q₁ * q₂ : ℝ) ^ 2) * ((3 / 4 : ℝ) ^ M * ∑' m : ℕ, (3 / 4 : ℝ) ^ m) := by
          simp_rw [pow_add, mul_comm ((3 / 4 : ℝ) ^ _ : ℝ) ((3 / 4 : ℝ) ^ M), ← mul_assoc, tsum_mul_left]
      _ = 4 * (1331 * C₀ + 54) * ((q₁ * q₂ : ℝ) ^ 2) * ((3 / 4 : ℝ) ^ M) := by
          rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
  -- Combine head and tail with G β = Fβ - lam / (β - 1) = Fβ + lam / (1 - β)
  have hGβ_re : (G (β : ℂ)).re = Fβ + lam / (1 - β) := by
    have hβne : (β : ℂ) ≠ 1 := by exact_mod_cast hβu.ne
    rw [hG_ne (β : ℂ) hβne, sub_re, hlam_eq]
    have hdiv : ((lam : ℂ) / ((β : ℂ) - 1)).re = -(lam / (1 - β)) := by
      rw [show (β : ℂ) - 1 = ((β - 1 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_div, ofReal_re]
      have : β - 1 = -(1 - β) := by ring
      rw [this, div_neg]
    dsimp only [Fβ]; linarith
  have hre_split : (G (β : ℂ)).re = (∑ m ∈ Finset.range M, c m).re + (∑' m : ℕ, c (m + M)).re := by
    rw [hsplit, add_re]
  have htail_re : -(4 * (1331 * C₀ + 54) * ((q₁ * q₂ : ℝ) ^ 2) * ((3 / 4 : ℝ) ^ M)) ≤
      (∑' m : ℕ, c (m + M)).re := by
    have := (abs_le.mp ((Complex.abs_re_le_norm _).trans htail_le)).1
    linarith
  have hcancel : lam * ((2 - β) ^ M - 1) / (1 - β) + lam / (1 - β) = lam * (2 - β) ^ M / (1 - β) := by
    have h1β : (1 - β : ℝ) ≠ 0 := by linarith
    field_simp; ring
  linarith

/-!
### Part 3: Jacobi Dirichlet Characters, Siegel's Theorem, and Dirichlet Hyperbola Limit
-/

/-- Existence of a quadratic nonresidue modulo an odd prime `p`. -/
lemma exists_legendreSym_eq_neg_one (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ r : ℕ, legendreSym p (r : ℤ) = -1 ∧ Nat.Coprime r p := by
  have hp : p.Prime := Fact.out
  obtain ⟨u, hu⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by
    rw [ZMod.ringChar_zmod_n]; exact hp2)
  have hu0 : u ≠ 0 := by
    intro h; subst h; exact hu ⟨0, by simp⟩
  have hleg : legendreSym p (u.val : ℤ) = -1 := by
    have h1 : (legendreSym p (u.val : ℤ)) = -1 := by
      rw [legendreSym.eq_neg_one_iff]
      simpa [ZMod.natCast_zmod_val] using hu
    exact h1
  have hcop : Nat.Coprime u.val p := by
    rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
    exact isUnit_iff_ne_zero.mpr hu0
  exact ⟨u.val, hleg, hcop⟩

/-- The quadratic Dirichlet character `n ↦ (n | d)` modulo any odd `d ≥ 3`. -/
def jacobiChar (d : ℕ) (hd : 1 < d) : DirichletCharacter ℂ d where
  toFun x := (jacobiSym (x.val : ℤ) d : ℂ)
  map_one' := by
    have : Fact (1 < d) := ⟨hd⟩
    simp [ZMod.val_one, jacobiSym.one_left]
  map_mul' x y := by
    have : NeZero d := ⟨by omega⟩
    have hmod : (((x * y).val : ℤ)) % (d : ℤ) = ((x.val : ℤ) * (y.val : ℤ)) % (d : ℤ) := by
      rw [ZMod.val_mul]
      push_cast
      rw [Int.emod_emod]
    rw [jacobiSym.mod_left' hmod, jacobiSym.mul_left]
    push_cast; rfl
  map_nonunit' x hx := by
    have : NeZero d := ⟨by omega⟩
    have hnc : Nat.gcd x.val d ≠ 1 := by
      intro h; exact hx ((ZMod.isUnit_iff_coprime x.val d).mpr h |> fun h' => by simpa [ZMod.natCast_zmod_val] using h')
    have hgcd : ((x.val : ℤ)).gcd d ≠ 1 := by
      rwa [Int.gcd_natCast_natCast]
    have h0 : jacobiSym (x.val : ℤ) d = 0 := jacobiSym.eq_zero_iff_not_coprime.mpr hgcd
    rw [h0, Int.cast_zero]

lemma jacobiChar_apply_nat (d : ℕ) (hd : 1 < d) (n : ℕ) :
    jacobiChar d hd (n : ZMod d) = (jacobiSym (n : ℤ) d : ℂ) := by
  have : NeZero d := ⟨by omega⟩
  change (jacobiSym ((n : ZMod d).val : ℤ) d : ℂ) = _
  have hmod : ((n % d : ℕ) : ℤ) = (n : ℤ) % (d : ℤ) := by omega
  rw [ZMod.val_natCast, hmod, ← jacobiSym.mod_left]

lemma jacobiChar_sq_eq_one (d : ℕ) (hd : 1 < d) : jacobiChar d hd ^ 2 = 1 := by
  have : NeZero d := ⟨by omega⟩
  ext x
  rw [MulChar.pow_apply' _ (by norm_num : (2 : ℕ) ≠ 0), MulChar.one_apply x.isUnit]
  have hcop : Nat.Coprime (x : ZMod d).val d := by
    rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]; exact x.isUnit
  have hsq : jacobiSym ((x : ZMod d).val : ℤ) d ^ 2 = 1 :=
    jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact hcop)
  change ((jacobiSym ((x : ZMod d).val : ℤ) d : ℂ) ^ 2) = 1
  exact_mod_cast hsq

/-- If `d₂` is odd squarefree with `q₁ < d₂`, then for any character `χ₁` mod `q₁`,
the product `changeLevel χ₁ * changeLevel (jacobiChar d₂)` mod `q₁ * d₂` is nontrivial. -/
lemma jacobiChar_prod_ne_one {q₁ d₂ : ℕ} [NeZero q₁] (hd₂_sf : Squarefree d₂)
    (hd₂_odd : Odd d₂) (hd₂_gt : q₁ < d₂) (χ₁ : DirichletCharacter ℂ q₁) :
    let hd₂ : 1 < d₂ := by have := NeZero.pos q₁; omega
    DirichletCharacter.changeLevel (dvd_mul_right q₁ d₂) χ₁ *
      DirichletCharacter.changeLevel (dvd_mul_left d₂ q₁) (jacobiChar d₂ hd₂) ≠ 1 := by
  intro hd₂ hEq
  have hq₁pos : 0 < q₁ := NeZero.pos q₁
  have hd₂pos : 0 < d₂ := by omega
  have hndvd : ¬ d₂ ∣ q₁ := fun h => by have := Nat.le_of_dvd hq₁pos h; omega
  -- Find a prime p ∣ d₂ with p ∤ q₁
  have hex_p : ∃ p : ℕ, p.Prime ∧ p ∣ d₂ ∧ ¬ p ∣ q₁ := by
    by_contra hall
    push Not at hall
    have hprod : d₂ = ∏ p ∈ d₂.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hd₂_sf).symm
    have hdvd : d₂ ∣ q₁ := by
      rw [hprod]
      refine Finset.prod_primes_dvd q₁ (fun p hp => Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors hp)) ?_
      intro p hp
      exact hall p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
    exact hndvd hdvd
  obtain ⟨p, hp, hpd₂, hnpq₁⟩ := hex_p
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h; subst h; obtain ⟨k, hk⟩ := hpd₂; obtain ⟨m, hm⟩ := hd₂_odd; omega
  obtain ⟨d', hd'⟩ := hpd₂
  have hnpd' : ¬ p ∣ d' := by
    intro h
    have hsq : p * p ∣ d₂ := by rw [hd']; exact mul_dvd_mul_left p h
    exact hp.not_isUnit (hd₂_sf p hsq)
  have hcop_rest : Nat.Coprime p (q₁ * d') :=
    (hp.coprime_iff_not_dvd.mpr hnpq₁).mul_right (hp.coprime_iff_not_dvd.mpr hnpd')
  obtain ⟨r, hleg, hrcop⟩ := exists_legendreSym_eq_neg_one p hp2
  let crt := Nat.chineseRemainder hcop_rest r 1
  set m : ℕ := crt.1
  have hm_p : m ≡ r [MOD p] := crt.2.1
  have hm_rest : m ≡ 1 [MOD q₁ * d'] := crt.2.2
  have hm_q1 : m ≡ 1 [MOD q₁] := hm_rest.of_dvd (dvd_mul_right q₁ d')
  have hm_d' : m ≡ 1 [MOD d'] := hm_rest.of_dvd (dvd_mul_left d' q₁)
  have hm_cop_p : Nat.Coprime m p := by
    rw [Nat.Coprime, Nat.ModEq.gcd_eq hm_p]; exact hrcop
  have hm_cop_rest : Nat.Coprime m (q₁ * d') := by
    rw [Nat.Coprime, Nat.ModEq.gcd_eq hm_rest]; simp
  have hm_cop_all : Nat.Coprime m (q₁ * d₂) := by
    rw [hd', show q₁ * (p * d') = p * (q₁ * d') by ring]
    exact hm_cop_p.mul_right hm_cop_rest
  have hunit : IsUnit ((m : ℕ) : ZMod (q₁ * d₂)) :=
    (ZMod.isUnit_iff_coprime m (q₁ * d₂)).mpr hm_cop_all
  have heval := congrFun (congrArg DFunLike.coe hEq) ((m : ℕ) : ZMod (q₁ * d₂))
  have hmeq : ((m : ℕ) : ZMod (q₁ * d₂)) = (hunit.unit : ZMod (q₁ * d₂)) := hunit.unit_spec.symm
  rw [MulChar.mul_apply, MulChar.one_apply hunit, hmeq,
    DirichletCharacter.changeLevel_eq_cast_of_dvd χ₁ (dvd_mul_right q₁ d₂) hunit.unit,
    DirichletCharacter.changeLevel_eq_cast_of_dvd (jacobiChar d₂ hd₂) (dvd_mul_left d₂ q₁) hunit.unit,
    ← hmeq] at heval
  have hcast1 : (ZMod.cast (m : ZMod (q₁ * d₂)) : ZMod q₁) = (1 : ZMod q₁) := by
    rw [ZMod.cast_natCast (dvd_mul_right q₁ d₂), ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact hm_q1
  have hcast2 : (ZMod.cast (m : ZMod (q₁ * d₂)) : ZMod d₂) = (m : ZMod d₂) :=
    ZMod.cast_natCast (dvd_mul_left d₂ q₁) m
  rw [hcast1, hcast2, map_one, one_mul, jacobiChar_apply_nat] at heval
  have hjac : jacobiSym (m : ℤ) d₂ = -1 := by
    have : NeZero p := ⟨hp.ne_zero⟩
    have hd'ne : d' ≠ 0 := by intro h; rw [h, mul_zero] at hd'; omega
    have : NeZero d' := ⟨hd'ne⟩
    rw [hd', jacobiSym.mul_right]
    have hjp : jacobiSym (m : ℤ) p = -1 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym]
      have hmod : ((m : ℤ) % (p : ℤ)) = ((r : ℤ) % (p : ℤ)) := by
        exact_mod_cast hm_p
      rw [legendreSym.mod, hmod, ← legendreSym.mod, hleg]
    have hjd' : jacobiSym (m : ℤ) d' = 1 := by
      have hmod : ((m : ℤ) % (d' : ℤ)) = ((1 : ℤ) % (d' : ℤ)) := by
        exact_mod_cast hm_d'
      rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]
    rw [hjp, hjd']; ring
  rw [hjac] at heval
  norm_num at heval

lemma jacobiChar_ne_one {d : ℕ} (hd_sf : Squarefree d) (hd_odd : Odd d) (hd_gt : 1 < d) :
    jacobiChar d hd_gt ≠ 1 := by
  have h := jacobiChar_prod_ne_one (q₁ := 1) hd_sf hd_odd hd_gt (1 : DirichletCharacter ℂ 1)
  intro heq
  apply h
  simp [heq]

set_option maxHeartbeats 600000 in
/-- Siegel's Theorem for Jacobi characters `jacobiChar d` with squarefree `d ≡ 3 (mod 8)`. -/
theorem siegel_theorem_jacobi (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) [NeZero d] (hd : 1 < d), Squarefree d → d % 8 = 3 →
      C * (d : ℝ) ^ (-ε) ≤ (DirichletCharacter.LFunction (jacobiChar d hd) 1).re := by
  obtain ⟨C₁, hC₁ge, hEst⟩ := estermann_ineq
  set η : ℝ := min (1 / 8) (ε / 16)
  have hηpos : 0 < η := lt_min (by norm_num) (by positivity)
  have hηle8 : η ≤ 1 / 8 := min_le_left _ _
  have hηle16 : η ≤ ε / 16 := min_le_right _ _
  -- Step 1: Produce a fixed anchor (q₁, χ₁, β) with F(β) ≤ 0 for all d₂ > q₁
  have hAnchor : ∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁) (β : ℝ),
      χ₁ ≠ 1 ∧ χ₁ ^ 2 = 1 ∧ 1 - η ≤ β ∧ β < 1 ∧
      ∀ (d₂ : ℕ) [NeZero d₂] (hd₂ : 1 < d₂), Squarefree d₂ → d₂ % 8 = 3 → q₁ < d₂ →
        letI : NeZero (q₁ * d₂) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne d₂)⟩
        let χ₃ : DirichletCharacter ℂ (q₁ * d₂) :=
          DirichletCharacter.changeLevel (dvd_mul_right q₁ d₂) χ₁ *
          DirichletCharacter.changeLevel (dvd_mul_left d₂ q₁) (jacobiChar d₂ hd₂)
        (riemannZeta (β : ℂ) * DirichletCharacter.LFunction χ₁ (β : ℂ) *
          DirichletCharacter.LFunction (jacobiChar d₂ hd₂) (β : ℂ) *
          DirichletCharacter.LFunction χ₃ (β : ℂ)).re ≤ 0 := by
    by_cases hex : ∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁) (β : ℝ),
        χ₁ ≠ 1 ∧ χ₁ ^ 2 = 1 ∧ 1 - η ≤ β ∧ β < 1 ∧
        DirichletCharacter.LFunction χ₁ (β : ℂ) = 0
    · obtain ⟨q₁, hnz, χ₁, β, hχ₁, hχ₁₂, hβl, hβu, hzero⟩ := hex
      refine ⟨q₁, hnz, χ₁, β, hχ₁, hχ₁₂, hβl, hβu, fun d₂ _ hd₂ _ _ _ => ?_⟩
      simp [hzero]
    · push Not at hex
      set t₀ : ℝ := 1 - η
      have hall_pos : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
          χ ≠ 1 → χ ^ 2 = 1 → 0 < (DirichletCharacter.LFunction χ (t₀ : ℂ)).re := by
        intro q _ χ hχ hχ2
        have hpos1 : 0 < (DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ)).re :=
          LFunction_re_pos_of_one_le hχ hχ2 le_rfl
        have hne : ∀ t ∈ Set.Icc t₀ 1, (DirichletCharacter.LFunction χ (t : ℂ)).re ≠ 0 := by
          intro t ht hzero
          have him : (DirichletCharacter.LFunction χ (t : ℂ)).im = 0 :=
            LFunction_im_eq_zero_of_real hχ hχ2 (by dsimp only [t₀] at ht; linarith [ht.1])
          have h0 : DirichletCharacter.LFunction χ (t : ℂ) = 0 := Complex.ext hzero him
          rcases lt_or_eq_of_le ht.2 with hlt | rfl
          · exact hex q inferInstance χ t hχ hχ2 ht.1 hlt h0
          · exact absurd hzero hpos1.ne'
        by_contra hle
        push Not at hle
        have hlt : (DirichletCharacter.LFunction χ (t₀ : ℂ)).re < 0 :=
          lt_of_le_of_ne hle (hne t₀ ⟨le_rfl, by dsimp only [t₀]; linarith⟩)
        let g : ℝ → ℝ := fun t => (DirichletCharacter.LFunction χ (t : ℂ)).re
        have hcont : Continuous g :=
          Complex.continuous_re.comp ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal)
        obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc (by dsimp only [t₀]; linarith : t₀ ≤ 1)
          hcont.continuousOn ⟨hlt.le, hpos1.le⟩
        exact hne t ht hgt
      have h3sf : Squarefree 3 := (Nat.prime_iff.mp (by decide : Nat.Prime 3)).squarefree
      have h3odd : Odd 3 := ⟨1, rfl⟩
      have h3gt : 1 < 3 := by omega
      have hχ1 : jacobiChar 3 h3gt ≠ 1 := jacobiChar_ne_one h3sf h3odd h3gt
      have hχ12 : jacobiChar 3 h3gt ^ 2 = 1 := jacobiChar_sq_eq_one 3 h3gt
      refine ⟨3, inferInstance, jacobiChar 3 h3gt, t₀, hχ1, hχ12, le_rfl, by dsimp only [t₀]; linarith, ?_⟩
      intro d₂ _ hd₂ hd₂_sf hd₂_mod hgt
      have hd₂_odd : Odd d₂ := ⟨d₂ / 2, by omega⟩
      have : NeZero (3 * d₂) := ⟨by omega⟩
      dsimp only
      let χ₃ : DirichletCharacter ℂ (3 * d₂) :=
        DirichletCharacter.changeLevel (dvd_mul_right 3 d₂) (jacobiChar 3 h3gt) *
        DirichletCharacter.changeLevel (dvd_mul_left d₂ 3) (jacobiChar d₂ hd₂)
      have hχ2 : jacobiChar d₂ hd₂ ≠ 1 := jacobiChar_ne_one hd₂_sf hd₂_odd hd₂
      have hχ22 : jacobiChar d₂ hd₂ ^ 2 = 1 := jacobiChar_sq_eq_one d₂ hd₂
      have hχ3 : χ₃ ≠ 1 := jacobiChar_prod_ne_one hd₂_sf hd₂_odd hgt (jacobiChar 3 h3gt)
      have hχ32 : χ₃ ^ 2 = 1 := by
        dsimp only [χ₃]
        rw [mul_pow, ← map_pow, ← map_pow, hχ12, hχ22, map_one, map_one, one_mul]
      have ⟨hzim, hzre⟩ := riemannZeta_neg_of_Ioo (x := t₀) (by dsimp only [t₀]; linarith) (by dsimp only [t₀]; linarith)
      have hi1 := LFunction_im_eq_zero_of_real hχ1 hχ12 (x := t₀) (by dsimp only [t₀]; linarith)
      have hi2 := LFunction_im_eq_zero_of_real hχ2 hχ22 (x := t₀) (by dsimp only [t₀]; linarith)
      have hi3 := LFunction_im_eq_zero_of_real hχ3 hχ32 (x := t₀) (by dsimp only [t₀]; linarith)
      have hr1 := hall_pos (jacobiChar 3 h3gt) hχ1 hχ12
      have hr2 := hall_pos (jacobiChar d₂ hd₂) hχ2 hχ22
      have hr3 := hall_pos χ₃ hχ3 hχ32
      have hre_prod : (riemannZeta (t₀ : ℂ) *
          DirichletCharacter.LFunction (jacobiChar 3 h3gt) (t₀ : ℂ) *
          DirichletCharacter.LFunction (jacobiChar d₂ hd₂) (t₀ : ℂ) *
          DirichletCharacter.LFunction χ₃ (t₀ : ℂ)).re =
          (riemannZeta (t₀ : ℂ)).re *
          (DirichletCharacter.LFunction (jacobiChar 3 h3gt) (t₀ : ℂ)).re *
          (DirichletCharacter.LFunction (jacobiChar d₂ hd₂) (t₀ : ℂ)).re *
          (DirichletCharacter.LFunction χ₃ (t₀ : ℂ)).re := by
        simp [Complex.mul_re, Complex.mul_im, hzim, hi1, hi2, hi3]
      change (riemannZeta (t₀ : ℂ) * DirichletCharacter.LFunction (jacobiChar 3 h3gt) (t₀ : ℂ) *
        DirichletCharacter.LFunction (jacobiChar d₂ hd₂) (t₀ : ℂ) *
        DirichletCharacter.LFunction χ₃ (t₀ : ℂ)).re ≤ 0
      rw [hre_prod]
      have hpos123 : 0 < (DirichletCharacter.LFunction (jacobiChar 3 h3gt) (t₀ : ℂ)).re *
          (DirichletCharacter.LFunction (jacobiChar d₂ hd₂) (t₀ : ℂ)).re *
          (DirichletCharacter.LFunction χ₃ (t₀ : ℂ)).re := by positivity
      nlinarith
  obtain ⟨q₁, hnz₁, χ₁, β, hχ₁, hχ₁₂, hβl, hβu, hFneg⟩ := hAnchor
  have hL1pos : 0 < (DirichletCharacter.LFunction χ₁ 1).re := by
    simpa using LFunction_re_pos_of_one_le hχ₁ hχ₁₂ (x := 1) le_rfl
  let K_exp : ℝ := Real.exp (2 * η) * (8 * C₁) ^ (4 * η) * (3 + 2 / ε) * (q₁ : ℝ) ^ ε *
    (DirichletCharacter.LFunction χ₁ 1).re
  have hKpos : 0 < K_exp := by
    have hq1pos : (0 : ℝ) < (q₁ : ℝ) := Nat.cast_pos.mpr (NeZero.pos q₁)
    positivity
  let c_big : ℝ := (1 - β) / (2 * K_exp)
  have hcbig_pos : 0 < c_big := div_pos (by linarith) (by positivity)
  have hbig : ∀ (d₂ : ℕ) [NeZero d₂] (hd₂ : 1 < d₂), Squarefree d₂ → d₂ % 8 = 3 → q₁ < d₂ →
      c_big * (d₂ : ℝ) ^ (-ε) ≤ (DirichletCharacter.LFunction (jacobiChar d₂ hd₂) 1).re := by
    intro d₂ _ hd₂ hd₂_sf hd₂_mod hgt
    have : NeZero (q₁ * d₂) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne d₂)⟩
    have hd₂_odd : Odd d₂ := ⟨d₂ / 2, by omega⟩
    let χ₂ := jacobiChar d₂ hd₂
    have hχ₂ : χ₂ ≠ 1 := jacobiChar_ne_one hd₂_sf hd₂_odd hd₂
    have hχ₂₂ : χ₂ ^ 2 = 1 := jacobiChar_sq_eq_one d₂ hd₂
    let χ₃ : DirichletCharacter ℂ (q₁ * d₂) :=
      DirichletCharacter.changeLevel (dvd_mul_right q₁ d₂) χ₁ *
      DirichletCharacter.changeLevel (dvd_mul_left d₂ q₁) χ₂
    have hχ₃ : χ₃ ≠ 1 := jacobiChar_prod_ne_one hd₂_sf hd₂_odd hgt χ₁
    have hχ₃₂ : χ₃ ^ 2 = 1 := by
      dsimp only [χ₃]
      rw [mul_pow, ← map_pow, ← map_pow, hχ₁₂, hχ₂₂, map_one, map_one, one_mul]
    set Q : ℝ := (q₁ * d₂ : ℝ)
    have hQge1 : 1 ≤ Q := by
      have h1 : (1 : ℝ) ≤ (q₁ : ℝ) := by exact_mod_cast NeZero.pos q₁
      have h2 : (1 : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast (by omega : 1 ≤ d₂)
      dsimp only [Q]; nlinarith
    have hA_ge : (1 : ℝ) ≤ 8 * C₁ * Q ^ 2 := by nlinarith
    have hlog43 : (1 / 4 : ℝ) ≤ Real.log (4 / 3 : ℝ) := by
      have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
      linarith
    have hlog43_pos : 0 < Real.log (4 / 3 : ℝ) := by linarith
    set R : ℝ := Real.log (8 * C₁ * Q ^ 2) / Real.log (4 / 3 : ℝ)
    have hRnn : 0 ≤ R := div_nonneg (Real.log_nonneg hA_ge) hlog43_pos.le
    set M : ℕ := Nat.ceil R + 1
    have hM1 : 1 ≤ M := by omega
    have hMge : R ≤ (M : ℝ) := by
      have := Nat.le_ceil R
      dsimp only [M]; push_cast; linarith
    have hMle : (M : ℝ) ≤ R + 2 := by
      have hlt : (Nat.ceil R : ℝ) < R + 1 := Nat.ceil_lt_add_one hRnn
      dsimp only [M]; push_cast; linarith
    have htail : 4 * C₁ * Q ^ 2 * ((3 / 4 : ℝ) ^ M) ≤ 1 / 2 := by
      have hpow : (8 * C₁ * Q ^ 2) ≤ (4 / 3 : ℝ) ^ M := by
        rw [← Real.rpow_natCast (4 / 3 : ℝ) M]
        have h1 : Real.log (8 * C₁ * Q ^ 2) ≤ (M : ℝ) * Real.log (4 / 3 : ℝ) := by
          have := mul_le_mul_of_nonneg_right hMge hlog43_pos.le
          rwa [div_mul_cancel₀ _ hlog43_pos.ne'] at this
        have h2 : Real.exp (Real.log (8 * C₁ * Q ^ 2)) ≤ Real.exp ((M : ℝ) * Real.log (4 / 3 : ℝ)) :=
          Real.exp_le_exp.mpr h1
        rw [Real.exp_log (by linarith)] at h2
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
        simpa [mul_comm] using h2
      have hinv : (3 / 4 : ℝ) ^ M = ((4 / 3 : ℝ) ^ M)⁻¹ := by
        rw [← inv_pow]; norm_num
      rw [hinv, mul_inv_le_iff₀ (by positivity)]
      linarith
    have hEstM := hEst χ₁ χ₂ hχ₁ hχ₂ hχ₁₂ hχ₂₂ hχ₃ β (by linarith) hβu M hM1
    have hF0 := hFneg d₂ hd₂ hd₂_sf hd₂_mod hgt
    have hhalf : (1 / 2 : ℝ) ≤
        (DirichletCharacter.LFunction χ₁ 1 * DirichletCharacter.LFunction χ₂ 1 *
          DirichletCharacter.LFunction χ₃ 1).re * ((2 - β) ^ M) / (1 - β) := by
      dsimp only [Q] at htail
      linarith
    have hi1 : (DirichletCharacter.LFunction χ₁ 1).im = 0 := by
      simpa using LFunction_im_eq_zero_of_real hχ₁ hχ₁₂ one_pos
    have hi2 : (DirichletCharacter.LFunction χ₂ 1).im = 0 := by
      simpa using LFunction_im_eq_zero_of_real hχ₂ hχ₂₂ one_pos
    have hi3 : (DirichletCharacter.LFunction χ₃ 1).im = 0 := by
      simpa using LFunction_im_eq_zero_of_real hχ₃ hχ₃₂ one_pos
    have hlam_re : (DirichletCharacter.LFunction χ₁ 1 * DirichletCharacter.LFunction χ₂ 1 *
        DirichletCharacter.LFunction χ₃ 1).re =
        (DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re *
        (DirichletCharacter.LFunction χ₃ 1).re := by
      simp [Complex.mul_re, Complex.mul_im, hi1, hi2, hi3]
    rw [hlam_re] at hhalf
    have hL3le : (DirichletCharacter.LFunction χ₃ 1).re ≤ (3 + 2 / ε) * Q ^ (ε / 2) := by
      have h1 : (DirichletCharacter.LFunction χ₃ 1).re ≤ 3 + Real.log Q := by
        have hnorm := norm_LFunction_one_le χ₃ hχ₃
        push_cast at hnorm
        exact (Complex.re_le_norm _).trans hnorm
      have hlogQ : Real.log Q ≤ (2 / ε) * Q ^ (ε / 2) := by
        have hQpos : 0 < Q := by linarith
        have hstep := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hQpos (ε / 2))
        rw [Real.log_rpow hQpos] at hstep
        have h2 : (ε / 2) * Real.log Q ≤ Q ^ (ε / 2) := by linarith
        have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 / ε)
        have hcancel : (2 / ε) * ((ε / 2) * Real.log Q) = Real.log Q := by field_simp
        linarith
      have hQpow_ge1 : 1 ≤ Q ^ (ε / 2) := Real.one_le_rpow hQge1 (by positivity)
      nlinarith
    have hpowM : (2 - β) ^ M ≤ Real.exp (2 * η) * (8 * C₁) ^ (4 * η) * Q ^ (ε / 2) := by
      have h2β : 2 - β ≤ Real.exp η := by
        have := Real.add_one_le_exp η
        linarith
      have h1 : (2 - β) ^ M ≤ Real.exp (η * (M : ℝ)) := by
        calc (2 - β) ^ M ≤ (Real.exp η) ^ M := pow_le_pow_left₀ (by linarith) h2β M
          _ = Real.exp ((M : ℝ) * η) := (Real.exp_nat_mul η M).symm
          _ = Real.exp (η * (M : ℝ)) := by ring_nf
      have h2 : η * (M : ℝ) ≤ 2 * η + 4 * η * Real.log (8 * C₁ * Q ^ 2) := by
        have hRle : R ≤ 4 * Real.log (8 * C₁ * Q ^ 2) := by
          dsimp only [R]
          rw [div_le_iff₀ hlog43_pos]
          have hln : 0 ≤ Real.log (8 * C₁ * Q ^ 2) := Real.log_nonneg hA_ge
          nlinarith
        nlinarith
      have h3 : Real.exp (η * (M : ℝ)) ≤ Real.exp (2 * η) * (8 * C₁ * Q ^ 2) ^ (4 * η) := by
        calc Real.exp (η * (M : ℝ))
            ≤ Real.exp (2 * η + 4 * η * Real.log (8 * C₁ * Q ^ 2)) := Real.exp_le_exp.mpr h2
          _ = Real.exp (2 * η) * Real.exp (Real.log (8 * C₁ * Q ^ 2) * (4 * η)) := by
              rw [Real.exp_add]; ring_nf
          _ = Real.exp (2 * η) * (8 * C₁ * Q ^ 2) ^ (4 * η) := by
              rw [Real.rpow_def_of_pos (by linarith)]
      have h4 : (8 * C₁ * Q ^ 2) ^ (4 * η) ≤ (8 * C₁) ^ (4 * η) * Q ^ (ε / 2) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [show Q ^ 2 = Q ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul (by linarith)]
        exact Real.rpow_le_rpow_of_exponent_le hQge1 (by linarith)
      calc (2 - β) ^ M ≤ Real.exp (η * (M : ℝ)) := h1
        _ ≤ Real.exp (2 * η) * (8 * C₁ * Q ^ 2) ^ (4 * η) := h3
        _ ≤ Real.exp (2 * η) * ((8 * C₁) ^ (4 * η) * Q ^ (ε / 2)) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = Real.exp (2 * η) * (8 * C₁) ^ (4 * η) * Q ^ (ε / 2) := by ring
    have hL2pos : 0 < (DirichletCharacter.LFunction χ₂ 1).re := by
      simpa using LFunction_re_pos_of_one_le hχ₂ hχ₂₂ (x := 1) le_rfl
    have hL3pos : 0 < (DirichletCharacter.LFunction χ₃ 1).re := by
      simpa using LFunction_re_pos_of_one_le hχ₃ hχ₃₂ (x := 1) le_rfl
    have hQpow : Q ^ (ε / 2) * Q ^ (ε / 2) = (q₁ : ℝ) ^ ε * (d₂ : ℝ) ^ ε := by
      rw [← Real.rpow_add (by linarith), show ε / 2 + ε / 2 = ε by ring]
      dsimp only [Q]
      exact Real.mul_rpow (by positivity) (by positivity)
    have hprod_le : (DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re *
        (DirichletCharacter.LFunction χ₃ 1).re * (2 - β) ^ M ≤
        (DirichletCharacter.LFunction χ₂ 1).re * K_exp * (d₂ : ℝ) ^ ε := by
      have hmul := mul_le_mul hL3le hpowM (pow_nonneg (by linarith) M) (by positivity)
      have hmul2 := mul_le_mul_of_nonneg_left hmul (mul_pos hL1pos hL2pos).le
      calc (DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re *
            (DirichletCharacter.LFunction χ₃ 1).re * (2 - β) ^ M
          = ((DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re) *
            ((DirichletCharacter.LFunction χ₃ 1).re * (2 - β) ^ M) := by ring
        _ ≤ ((DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re) *
            (((3 + 2 / ε) * Q ^ (ε / 2)) * (Real.exp (2 * η) * (8 * C₁) ^ (4 * η) * Q ^ (ε / 2))) := hmul2
        _ = (DirichletCharacter.LFunction χ₂ 1).re *
            (Real.exp (2 * η) * (8 * C₁) ^ (4 * η) * (3 + 2 / ε) *
              (DirichletCharacter.LFunction χ₁ 1).re) * (Q ^ (ε / 2) * Q ^ (ε / 2)) := by ring
        _ = (DirichletCharacter.LFunction χ₂ 1).re * K_exp * (d₂ : ℝ) ^ ε := by
            rw [hQpow]; dsimp only [K_exp]; ring
    have h1β : 0 < 1 - β := by linarith
    have hhalf' : (1 - β) / 2 ≤ (DirichletCharacter.LFunction χ₂ 1).re * K_exp * (d₂ : ℝ) ^ ε := by
      have hstep : (1 - β) / 2 ≤ (DirichletCharacter.LFunction χ₁ 1).re * (DirichletCharacter.LFunction χ₂ 1).re *
          (DirichletCharacter.LFunction χ₃ 1).re * (2 - β) ^ M := by
        rw [le_div_iff₀ h1β] at hhalf; linarith
      exact hstep.trans hprod_le
    rw [Real.rpow_neg (by positivity)]
    have hd2pow : 0 < (d₂ : ℝ) ^ ε := by positivity
    dsimp only [c_big]
    rw [mul_inv_le_iff₀ hd2pow, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K_exp)]
    linarith
  let smallSet : Finset ℕ := (Finset.Icc 2 q₁).filter (fun d => Squarefree d ∧ d % 8 = 3)
  let vals : Finset ℝ := insert c_big (smallSet.attach.image fun (d : {x // x ∈ smallSet}) =>
    have hd : 1 < d.1 := by have := (Finset.mem_filter.mp d.2).1; rw [Finset.mem_Icc] at this; omega
    letI : NeZero d.1 := ⟨by omega⟩
    (DirichletCharacter.LFunction (jacobiChar d.1 hd) 1).re * (d.1 : ℝ) ^ ε)
  have hvals_ne : vals.Nonempty := Finset.insert_nonempty _ _
  let C : ℝ := vals.min' hvals_ne
  have hCpos : 0 < C := by
    rw [Finset.lt_min'_iff]
    intro v hv
    rw [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact hcbig_pos
    · rw [Finset.mem_image] at hv
      obtain ⟨⟨d, hd_mem⟩, _, rfl⟩ := hv
      obtain ⟨hd_icc, hd_sf, hd_mod⟩ := Finset.mem_filter.mp hd_mem
      have hd1 : 1 < d := by rw [Finset.mem_Icc] at hd_icc; omega
      have : NeZero d := ⟨by omega⟩
      have hpos : 0 < (DirichletCharacter.LFunction (jacobiChar d hd1) 1).re := by
        simpa using LFunction_re_pos_of_one_le (jacobiChar_ne_one hd_sf ⟨d / 2, by omega⟩ hd1)
          (jacobiChar_sq_eq_one d hd1) (x := 1) le_rfl
      have hdpos : (0 : ℝ) < (d : ℝ) ^ ε := by positivity
      exact mul_pos hpos hdpos
  refine ⟨C, hCpos, fun d _ hd hsf hmod => ?_⟩
  by_cases hle : d ≤ q₁
  · have hmem_small : d ∈ smallSet := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hle⟩, hsf, hmod⟩
    have hmem_vals : (DirichletCharacter.LFunction (jacobiChar d hd) 1).re * (d : ℝ) ^ ε ∈ vals := by
      apply Finset.mem_insert_of_mem
      rw [Finset.mem_image]
      exact ⟨⟨d, hmem_small⟩, Finset.mem_attach _ _, rfl⟩
    have hCle : C ≤ (DirichletCharacter.LFunction (jacobiChar d hd) 1).re * (d : ℝ) ^ ε :=
      Finset.min'_le vals _ hmem_vals
    rw [Real.rpow_neg (by positivity), mul_inv_le_iff₀ (by positivity)]
    exact hCle
  · have hCle : C ≤ c_big := Finset.min'_le vals c_big (Finset.mem_insert_self _ _)
    exact (mul_le_mul_of_nonneg_right hCle (by positivity)).trans
      (hbig d hd hsf hmod (by omega))

/-- Dirichlet hyperbola limit: `(1/X) ∑_{n=1}^X (1 * χ)(n) → L(1, χ)`. -/
theorem tendsto_conv_one_char {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hχ2 : χ ^ 2 = 1) :
    Tendsto (fun X : ℕ => (∑ n ∈ Finset.Icc 1 X, ∑ k ∈ n.divisors, (χ k).re) / (X : ℝ))
      atTop (𝓝 (DirichletCharacter.LFunction χ 1).re) := by
  -- Step 1: Partial sums ∑_{k=1}^N (χ k).re / k converge to L(1, χ).re
  have hpart_lim : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (χ k).re / (k : ℝ))
      atTop (𝓝 (DirichletCharacter.LFunction χ 1).re) := by
    have hL1 := LFunction_eq_abel_tsum χ hχ (s := 1) (by simp)
    have hsum : Summable (fun n : ℕ => (∑ k ∈ Finset.Icc 1 (n + 1), χ k) *
        (((n + 1 : ℕ) : ℂ) ^ (-(1 : ℂ)) - ((n + 2 : ℕ) : ℂ) ^ (-(1 : ℂ)))) := by
      have htele : HasSum (fun n : ℕ => ((n + 1 : ℝ)⁻¹ - (n + 2 : ℝ)⁻¹)) 1 := by
        simpa using hasSum_inv_sub_inv_shift 0
      refine Summable.of_norm_bounded (htele.summable.mul_left (q : ℝ)) fun n => ?_
      rw [norm_mul]
      have h1 := norm_char_partialSum_le χ hχ (n + 1)
      have h2 : ‖((n + 1 : ℕ) : ℂ) ^ (-(1 : ℂ)) - ((n + 2 : ℕ) : ℂ) ^ (-(1 : ℂ))‖ =
          ((n + 1 : ℝ)⁻¹) - ((n + 2 : ℝ)⁻¹) := by
        rw [cpow_neg_one, cpow_neg_one, ← ofReal_natCast, ← ofReal_natCast, ← ofReal_inv,
          ← ofReal_inv, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr (inv_anti₀ (by positivity) (by push_cast; linarith)))]
        push_cast; rfl
      rw [h2]
      exact mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr (inv_anti₀ (by positivity) (by linarith)))
    have hlim_abel : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (∑ k ∈ Finset.Icc 1 (n + 1), χ k) *
        (((n + 1 : ℕ) : ℂ) ^ (-(1 : ℂ)) - ((n + 2 : ℕ) : ℂ) ^ (-(1 : ℂ))))
        atTop (𝓝 (DirichletCharacter.LFunction χ 1)) := by
      rw [hL1]; exact hsum.hasSum.tendsto_sum_nat
    have hrem : Tendsto (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, χ k) * (((N + 1 : ℕ) : ℂ) ^ (-(1 : ℂ))))
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (g := fun N : ℕ => (q : ℝ) * (((N + 1 : ℕ) : ℝ)⁻¹))
        (fun _ => norm_nonneg _) (fun N => ?_) ?_
      · rw [norm_mul, cpow_neg_one, norm_inv, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right (norm_char_partialSum_le χ hχ N) (by positivity)
      · have hinv : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
        simpa using hinv.const_mul (q : ℝ)
    have hlimC : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, χ k * ((k : ℂ) ^ (-(1 : ℂ))))
        atTop (𝓝 (DirichletCharacter.LFunction χ 1)) := by
      have hadd := hlim_abel.add hrem
      rw [add_zero] at hadd
      refine hadd.congr fun N => ?_
      rw [abel_partial_sum χ 1 N]; ring
    have hlimR := (Complex.continuous_re.tendsto _).comp hlimC
    refine hlimR.congr fun N => ?_
    dsimp only [Function.comp_apply]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cpow_neg_one, ← ofReal_natCast, ← ofReal_inv, mul_re, ofReal_re, ofReal_im, mul_zero,
      sub_zero, div_eq_mul_inv]
  -- Step 2: Compose with Nat.sqrt
  have hsqrt_lim : Tendsto (fun X : ℕ => ∑ k ∈ Finset.Icc 1 (Nat.sqrt X), (χ k).re / (k : ℝ))
      atTop (𝓝 (DirichletCharacter.LFunction χ 1).re) := by
    refine hpart_lim.comp ?_
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b * b, fun n hn => ?_⟩
    exact Nat.le_sqrt.mpr hn
  -- Step 3: Show difference tends to 0 via Dirichlet hyperbola identity
  suffices hdiff : Tendsto (fun X : ℕ =>
      (∑ n ∈ Finset.Icc 1 X, ∑ k ∈ n.divisors, (χ k).re) / (X : ℝ) -
      ∑ k ∈ Finset.Icc 1 (Nat.sqrt X), (χ k).re / (k : ℝ)) atTop (𝓝 0) by
    have := hsqrt_lim.add hdiff
    rw [add_zero] at this
    exact this.congr fun X => by ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun X : ℕ => ((2 * (q : ℝ) + 1) * (Nat.sqrt X : ℝ)) / (X : ℝ))
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with X hX1
    set D := Nat.sqrt X
    have hDX : D ≤ X := Nat.sqrt_le_self X
    have hswap : (∑ n ∈ Finset.Icc 1 X, ∑ k ∈ n.divisors, (χ k).re) =
        ∑ k ∈ Finset.Icc 1 X, ((X / k : ℕ) : ℝ) * (χ k).re := by
      have h1 : (∑ n ∈ Finset.Icc 1 X, ∑ k ∈ n.divisors, (χ k).re) =
          ∑ p ∈ (Finset.Icc 1 X).sigma (fun n => n.divisors), (χ p.2).re :=
        Finset.sum_sigma' (Finset.Icc 1 X) (fun n => n.divisors) (fun _ k => (χ k).re)
      have h2 : (∑ k ∈ Finset.Icc 1 X, ((X / k : ℕ) : ℝ) * (χ k).re) =
          ∑ q ∈ (Finset.Icc 1 X).sigma (fun k => Finset.Icc 1 (X / k)), (χ q.1).re := by
        rw [← Finset.sum_sigma' (Finset.Icc 1 X) (fun k => Finset.Icc 1 (X / k)) (fun k _ => (χ k).re)]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
      rw [h1, h2]
      refine Finset.sum_bij (fun p _ => ⟨p.2, p.1 / p.2⟩) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp ⊢
        obtain ⟨⟨hn1, hnX⟩, ⟨hdvd, hn0⟩⟩ := hp
        have hkpos : 0 < p.2 := Nat.pos_of_dvd_of_pos hdvd (by omega)
        have hkle : p.2 ≤ p.1 := Nat.le_of_dvd (by omega) hdvd
        exact ⟨⟨hkpos, le_trans hkle hnX⟩,
          ⟨Nat.div_pos hkle hkpos, Nat.div_le_div_right hnX⟩⟩
      · intro p₁ hp₁ p₂ hp₂ heq
        simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp₁ hp₂
        rcases p₁ with ⟨n₁, k₁⟩; rcases p₂ with ⟨n₂, k₂⟩
        dsimp only at hp₁ hp₂
        simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
        obtain ⟨rfl, hdiv⟩ := heq
        have heq_n : n₁ = n₂ := by
          rw [← Nat.mul_div_cancel' hp₁.2.1, ← Nat.mul_div_cancel' hp₂.2.1, hdiv]
        subst heq_n; rfl
      · intro p hp
        simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
        obtain ⟨⟨hk1, hkX⟩, ⟨hm1, hmX⟩⟩ := hp
        have hmul_le : p.1 * p.2 ≤ X := by
          calc p.1 * p.2 ≤ p.1 * (X / p.1) := Nat.mul_le_mul_left p.1 hmX
            _ ≤ X := Nat.mul_div_le X p.1
        refine ⟨⟨p.1 * p.2, p.1⟩, ?_, ?_⟩
        · simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
          exact ⟨⟨by nlinarith, hmul_le⟩, dvd_mul_right _ _, by nlinarith⟩
        · have hdiv : p.1 * p.2 / p.1 = p.2 := Nat.mul_div_cancel_left p.2 hk1
          rcases p with ⟨a, b⟩; dsimp only at hdiv ⊢; rw [hdiv]
      · intro _ _; rfl
    have hsplit_k : Finset.Icc 1 X = Finset.Icc 1 D ∪ Finset.Ioc D X := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 1 D) (Finset.Ioc D X) := by
      rw [Finset.disjoint_left]; intro k h1 h2
      rw [Finset.mem_Icc] at h1; rw [Finset.mem_Ioc] at h2; omega
    rw [hswap, hsplit_k, Finset.sum_union hdisj]
    have hpart1 : |∑ k ∈ Finset.Icc 1 D, (((X / k : ℕ) : ℝ) - (X : ℝ) / (k : ℝ)) * (χ k).re| ≤ (D : ℝ) := by
      calc |∑ k ∈ Finset.Icc 1 D, (((X / k : ℕ) : ℝ) - (X : ℝ) / (k : ℝ)) * (χ k).re|
          ≤ ∑ k ∈ Finset.Icc 1 D, |(((X / k : ℕ) : ℝ) - (X : ℝ) / (k : ℝ)) * (χ k).re| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.Icc 1 D, (1 : ℝ) := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [Finset.mem_Icc] at hk
            rw [abs_mul]
            have hχ1 : |(χ k).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (χ.norm_le_one _)
            have hfrac : |((X / k : ℕ) : ℝ) - (X : ℝ) / (k : ℝ)| ≤ 1 := by
              have hle : ((X / k : ℕ) : ℝ) * (k : ℝ) ≤ (X : ℝ) := by
                exact_mod_cast Nat.div_mul_le_self X k
              have hlt : (X : ℝ) < (((X / k : ℕ) : ℝ) + 1) * (k : ℝ) := by
                have := Nat.lt_mul_div_succ X (by omega : 0 < k)
                have : X < (X / k + 1) * k := by linarith [mul_comm k (X / k + 1)]
                exact_mod_cast this
              have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
              have hdiv_ge : ((X / k : ℕ) : ℝ) ≤ (X : ℝ) / (k : ℝ) := (le_div_iff₀ hkpos).mpr hle
              have hdiv_lt : (X : ℝ) / (k : ℝ) < ((X / k : ℕ) : ℝ) + 1 := (div_lt_iff₀ hkpos).mpr hlt
              rw [abs_le]
              constructor <;> linarith
            exact mul_le_one₀ hfrac (abs_nonneg _) hχ1
        _ = (D : ℝ) := by simp [Nat.card_Icc]
    have hpart2 : |∑ k ∈ Finset.Ioc D X, ((X / k : ℕ) : ℝ) * (χ k).re| ≤ 2 * (q : ℝ) * (D : ℝ) := by
      have hswap2 : (∑ k ∈ Finset.Ioc D X, ((X / k : ℕ) : ℝ) * (χ k).re) =
          ∑ m ∈ Finset.Icc 1 D, ∑ k ∈ Finset.Ioc D (X / m), (χ k).re := by
        have hl : (∑ k ∈ Finset.Ioc D X, ((X / k : ℕ) : ℝ) * (χ k).re) =
            ∑ p ∈ (Finset.Ioc D X).sigma (fun k => Finset.Icc 1 (X / k)), (χ p.1).re := by
          rw [← Finset.sum_sigma' (Finset.Ioc D X) (fun k => Finset.Icc 1 (X / k)) (fun k _ => (χ k).re)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
        have hr : (∑ m ∈ Finset.Icc 1 D, ∑ k ∈ Finset.Ioc D (X / m), (χ k).re) =
            ∑ p ∈ (Finset.Icc 1 D).sigma (fun m => Finset.Ioc D (X / m)), (χ p.2).re :=
          Finset.sum_sigma' (Finset.Icc 1 D) (fun m => Finset.Ioc D (X / m)) (fun _ k => (χ k).re)
        rw [hl, hr]
        refine Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
        · intro p hp
          simp only [Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
          obtain ⟨⟨hkD, hkX⟩, ⟨hm1, hmX⟩⟩ := hp
          have hkm : p.1 * p.2 ≤ X := (Nat.mul_le_mul_left p.1 hmX).trans (Nat.mul_div_le X p.1)
          have hDsq : X < (D + 1) * (D + 1) := Nat.lt_succ_sqrt X
          have hmD : p.2 ≤ D := by nlinarith
          have hkXm : p.1 ≤ X / p.2 := (Nat.le_div_iff_mul_le (by omega)).mpr hkm
          exact ⟨⟨hm1, hmD⟩, ⟨hkD, hkXm⟩⟩
        · intro p₁ _ p₂ _ heq
          rcases p₁ with ⟨k₁, m₁⟩; rcases p₂ with ⟨k₂, m₂⟩
          simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
          obtain ⟨rfl, rfl⟩ := heq; rfl
        · intro p hp
          simp only [Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_Icc] at hp
          obtain ⟨⟨hm1, hmD⟩, ⟨hkD, hkXm⟩⟩ := hp
          have hmk : p.2 * p.1 ≤ X := (Nat.mul_le_mul_right p.1 hkXm).trans (Nat.div_mul_le_self X p.1)
          have hkX : p.2 ≤ X := by nlinarith
          have hmXk : p.1 ≤ X / p.2 := (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
          exact ⟨⟨p.2, p.1⟩, by simp only [Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_Icc]; exact ⟨⟨hkD, hkX⟩, ⟨hm1, hmXk⟩⟩, rfl⟩
        · intro _ _; rfl
      rw [hswap2]
      calc |∑ m ∈ Finset.Icc 1 D, ∑ k ∈ Finset.Ioc D (X / m), (χ k).re|
          ≤ ∑ m ∈ Finset.Icc 1 D, |∑ k ∈ Finset.Ioc D (X / m), (χ k).re| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _m ∈ Finset.Icc 1 D, (2 * (q : ℝ)) := by
            refine Finset.sum_le_sum fun m _ => ?_
            by_cases hle : D ≤ X / m
            · have hdiff_sum : ∑ k ∈ Finset.Ioc D (X / m), (χ k).re =
                  (∑ k ∈ Finset.Icc 1 (X / m), χ k - ∑ k ∈ Finset.Icc 1 D, χ k).re := by
                rw [sub_re, Complex.re_sum, Complex.re_sum]
                have hun : Finset.Icc 1 (X / m) = Finset.Icc 1 D ∪ Finset.Ioc D (X / m) := by
                  ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]; omega
                have hdj : Disjoint (Finset.Icc 1 D) (Finset.Ioc D (X / m)) := by
                  rw [Finset.disjoint_left]; intro k h1 h2
                  rw [Finset.mem_Icc] at h1; rw [Finset.mem_Ioc] at h2; omega
                rw [hun, Finset.sum_union hdj]; ring
              rw [hdiff_sum]
              calc |(∑ k ∈ Finset.Icc 1 (X / m), χ k - ∑ k ∈ Finset.Icc 1 D, χ k).re|
                  ≤ ‖∑ k ∈ Finset.Icc 1 (X / m), χ k - ∑ k ∈ Finset.Icc 1 D, χ k‖ :=
                    Complex.abs_re_le_norm _
                _ ≤ ‖∑ k ∈ Finset.Icc 1 (X / m), χ k‖ + ‖∑ k ∈ Finset.Icc 1 D, χ k‖ :=
                    norm_sub_le _ _
                _ ≤ (q : ℝ) + (q : ℝ) := add_le_add (norm_char_partialSum_le χ hχ _) (norm_char_partialSum_le χ hχ _)
                _ = 2 * (q : ℝ) := by ring
            · have hemp : Finset.Ioc D (X / m) = ∅ := by
                ext k; simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]; omega
              rw [hemp, Finset.sum_empty, abs_zero]; positivity
        _ = 2 * (q : ℝ) * (D : ℝ) := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX1
    have hrew : ((∑ k ∈ Finset.Icc 1 D, ((X / k : ℕ) : ℝ) * (χ k).re) +
        ∑ k ∈ Finset.Ioc D X, ((X / k : ℕ) : ℝ) * (χ k).re) / (X : ℝ) -
        ∑ k ∈ Finset.Icc 1 D, (χ k).re / (k : ℝ) =
        ((∑ k ∈ Finset.Icc 1 D, (((X / k : ℕ) : ℝ) - (X : ℝ) / (k : ℝ)) * (χ k).re) +
          ∑ k ∈ Finset.Ioc D X, ((X / k : ℕ) : ℝ) * (χ k).re) / (X : ℝ) := by
      have hmulX : (X : ℝ) * ∑ k ∈ Finset.Icc 1 D, (χ k).re / (k : ℝ) =
          ∑ k ∈ Finset.Icc 1 D, ((X : ℝ) / (k : ℝ)) * (χ k).re := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      have hsub : ∑ k ∈ Finset.Icc 1 D, (((X / k : ℕ) : ℝ) - (X : ℝ) / (k : ℝ)) * (χ k).re =
          (∑ k ∈ Finset.Icc 1 D, ((X / k : ℕ) : ℝ) * (χ k).re) -
          ∑ k ∈ Finset.Icc 1 D, ((X : ℝ) / (k : ℝ)) * (χ k).re := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hsub, ← hmulX]
      field_simp [hXpos.ne']; ring
    rw [Real.norm_eq_abs, hrew, abs_div, abs_of_pos hXpos]
    refine div_le_div_of_nonneg_right ?_ hXpos.le
    calc |(∑ k ∈ Finset.Icc 1 D, (((X / k : ℕ) : ℝ) - (X : ℝ) / (k : ℝ)) * (χ k).re) +
          ∑ k ∈ Finset.Ioc D X, ((X / k : ℕ) : ℝ) * (χ k).re|
        ≤ |∑ k ∈ Finset.Icc 1 D, (((X / k : ℕ) : ℝ) - (X : ℝ) / (k : ℝ)) * (χ k).re| +
          |∑ k ∈ Finset.Ioc D X, ((X / k : ℕ) : ℝ) * (χ k).re| := abs_add_le _ _
      _ ≤ (D : ℝ) + 2 * (q : ℝ) * (D : ℝ) := add_le_add hpart1 hpart2
      _ = (2 * (q : ℝ) + 1) * (D : ℝ) := by ring
  · have h0 : Tendsto (fun X : ℕ => (2 * (q : ℝ) + 1) * (Real.sqrt (X : ℝ))⁻¹) atTop (𝓝 0) := by
      have hsq : Tendsto (fun X : ℕ => Real.sqrt (X : ℝ)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      simpa using (tendsto_inv_atTop_zero.comp hsq).const_mul (2 * (q : ℝ) + 1)
    refine squeeze_zero (fun X => by positivity) (fun X => ?_) h0
    by_cases hX : X = 0
    · subst hX; simp
    · have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hX
      have hle : (Nat.sqrt X : ℝ) ≤ Real.sqrt (X : ℝ) := by
        rw [Real.le_sqrt (by positivity) hXpos.le, sq]
        exact_mod_cast Nat.sqrt_le X
      have hsqmul : Real.sqrt (X : ℝ) / (X : ℝ) = (Real.sqrt (X : ℝ))⁻¹ := by
        have hsqpos : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hXpos
        rw [div_eq_iff hXpos.ne', inv_mul_eq_div, eq_div_iff hsqpos.ne', Real.mul_self_sqrt hXpos.le]
      calc ((2 * (q : ℝ) + 1) * (Nat.sqrt X : ℝ)) / (X : ℝ)
          ≤ ((2 * (q : ℝ) + 1) * Real.sqrt (X : ℝ)) / (X : ℝ) := by gcongr
        _ = (2 * (q : ℝ) + 1) * (Real.sqrt (X : ℝ) / (X : ℝ)) := by ring
        _ = (2 * (q : ℝ) + 1) * (Real.sqrt (X : ℝ))⁻¹ := by rw [hsqmul]

end E940.Siegel

end ModSiegel

section ModClassNumber

open Finset BigOperators Filter Topology Matrix

namespace E940.ClassNumber

/-!
### Part 1: Positive Definite Binary Quadratic Forms of Discriminant `-d` and Gauss Reduction
-/

/-- Positive definite binary quadratic form `a x² + b x y + c y²` of discriminant `-d`. -/
structure BQF (d : ℕ) where
  a : ℤ
  b : ℤ
  c : ℤ
  ha : 0 < a
  hc : 0 < c
  hdisc : 4 * a * c - b ^ 2 = (d : ℤ)

namespace BQF

lemma ext {d : ℕ} {f g : BQF d} (ha : f.a = g.a) (hb : f.b = g.b) (hc : f.c = g.c) : f = g := by
  cases f; cases g; dsimp at ha hb hc; subst ha hb hc; rfl

instance (d : ℕ) : DecidableEq (BQF d) := fun f g =>
  if h : f.a = g.a ∧ f.b = g.b ∧ f.c = g.c then
    isTrue (BQF.ext h.1 h.2.1 h.2.2)
  else
    isFalse fun heq => h ⟨congrArg BQF.a heq, congrArg BQF.b heq, congrArg BQF.c heq⟩

def eval {d : ℕ} (f : BQF d) (x y : ℤ) : ℤ :=
  f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2

def conj {d : ℕ} (f : BQF d) : BQF d :=
  ⟨f.a, -f.b, f.c, f.ha, f.hc, by linear_combination f.hdisc⟩

lemma eval_nonneg {d : ℕ} (f : BQF d) (x y : ℤ) : 0 ≤ f.eval x y := by
  have h4 : 4 * f.a * f.eval x y = (2 * f.a * x + f.b * y) ^ 2 + (d : ℤ) * y ^ 2 := by
    dsimp only [eval]; linear_combination y ^ 2 * f.hdisc
  have hd : (0 : ℤ) ≤ (d : ℤ) := Nat.cast_nonneg d
  nlinarith [f.ha, sq_nonneg (2 * f.a * x + f.b * y), sq_nonneg y]

lemma eval_pos {d : ℕ} (hd : 0 < d) (f : BQF d) {x y : ℤ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < f.eval x y := by
  have h4 : 4 * f.a * f.eval x y = (2 * f.a * x + f.b * y) ^ 2 + (d : ℤ) * y ^ 2 := by
    dsimp only [eval]; linear_combination y ^ 2 * f.hdisc
  have hdZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  by_cases hy : y = 0
  · subst hy
    have hx : x ≠ 0 := hxy.resolve_right (not_not.mpr rfl)
    have hx2 : 0 < x ^ 2 := by rcases lt_or_gt_of_ne hx with h | h <;> nlinarith
    have hax : 0 < (2 * f.a * x) ^ 2 := by
      have : 2 * f.a * x ≠ 0 := mul_ne_zero (mul_ne_zero (by decide) f.ha.ne') hx
      rcases lt_or_gt_of_ne this with h | h <;> nlinarith
    nlinarith [f.ha]
  · have hy2 : 0 < y ^ 2 := by rcases lt_or_gt_of_ne hy with h | h <;> nlinarith
    nlinarith [f.ha, sq_nonneg (2 * f.a * x + f.b * y)]

def isReduced {d : ℕ} (f : BQF d) : Prop :=
  |f.b| ≤ f.a ∧ f.a ≤ f.c

lemma isReduced_conj {d : ℕ} {f : BQF d} (hf : f.isReduced) : f.conj.isReduced := by
  simpa [isReduced, conj] using hf

/-- Elementary `T_k` action `(a, b, c) ↦ (a, b + 2ka, ak² + bk + c)` corresponding to `[[1, k], [0, 1]]`. -/
def shift {d : ℕ} (f : BQF d) (k : ℤ) (hd : 0 < d) : BQF d :=
  ⟨f.a, f.b + 2 * k * f.a, f.a * k ^ 2 + f.b * k + f.c, f.ha,
    by have := eval_pos hd f (x := k) (y := 1) (Or.inr one_ne_zero); dsimp only [eval] at this; linarith,
    by linear_combination f.hdisc⟩

/-- Elementary `S` action `(a, b, c) ↦ (c, -b, a)` corresponding to `[[0, -1], [1, 0]]`. -/
def swap {d : ℕ} (f : BQF d) : BQF d :=
  ⟨f.c, -f.b, f.a, f.hc, f.ha, by linear_combination f.hdisc⟩

/-- Proper `SL₂(ℤ)` equivalence of binary quadratic forms. -/
def SL2Equiv {d : ℕ} (f g : BQF d) : Prop :=
  ∃ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = 1 ∧
    ∀ x y : ℤ, f.eval (M 0 0 * x + M 0 1 * y) (M 1 0 * x + M 1 1 * y) = g.eval x y

/-- General `GL₂(ℤ)` equivalence of binary quadratic forms. -/
def GL2Equiv {d : ℕ} (f g : BQF d) : Prop :=
  ∃ M : Matrix (Fin 2) (Fin 2) ℤ, (M.det = 1 ∨ M.det = -1) ∧
    ∀ x y : ℤ, f.eval (M 0 0 * x + M 0 1 * y) (M 1 0 * x + M 1 1 * y) = g.eval x y

lemma SL2Equiv.toGL2 {d : ℕ} {f g : BQF d} (h : SL2Equiv f g) : GL2Equiv f g :=
  let ⟨M, hd, he⟩ := h; ⟨M, Or.inl hd, he⟩

lemma SL2Equiv.refl {d : ℕ} (f : BQF d) : SL2Equiv f f :=
  ⟨1, Matrix.det_one, fun x y => by simp⟩

lemma SL2Equiv.trans {d : ℕ} {f g h : BQF d} (h1 : SL2Equiv f g) (h2 : SL2Equiv g h) :
    SL2Equiv f h := by
  obtain ⟨M₁, hd₁, he₁⟩ := h1
  obtain ⟨M₂, hd₂, he₂⟩ := h2
  refine ⟨M₁ * M₂, by rw [Matrix.det_mul, hd₁, hd₂, mul_one], fun x y => ?_⟩
  have hlin : f.eval ((M₁ * M₂) 0 0 * x + (M₁ * M₂) 0 1 * y) ((M₁ * M₂) 1 0 * x + (M₁ * M₂) 1 1 * y) =
      f.eval (M₁ 0 0 * (M₂ 0 0 * x + M₂ 0 1 * y) + M₁ 0 1 * (M₂ 1 0 * x + M₂ 1 1 * y))
        (M₁ 1 0 * (M₂ 0 0 * x + M₂ 0 1 * y) + M₁ 1 1 * (M₂ 1 0 * x + M₂ 1 1 * y)) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]; congr 1 <;> ring
  rw [hlin, he₁, he₂]

lemma GL2Equiv.trans {d : ℕ} {f g h : BQF d} (h1 : GL2Equiv f g) (h2 : GL2Equiv g h) :
    GL2Equiv f h := by
  obtain ⟨M₁, hd₁, he₁⟩ := h1
  obtain ⟨M₂, hd₂, he₂⟩ := h2
  refine ⟨M₁ * M₂, ?_, fun x y => ?_⟩
  · rw [Matrix.det_mul]; rcases hd₁ with h1 | h1 <;> rcases hd₂ with h2 | h2 <;> simp [h1, h2]
  · have hlin : f.eval ((M₁ * M₂) 0 0 * x + (M₁ * M₂) 0 1 * y) ((M₁ * M₂) 1 0 * x + (M₁ * M₂) 1 1 * y) =
        f.eval (M₁ 0 0 * (M₂ 0 0 * x + M₂ 0 1 * y) + M₁ 0 1 * (M₂ 1 0 * x + M₂ 1 1 * y))
          (M₁ 1 0 * (M₂ 0 0 * x + M₂ 0 1 * y) + M₁ 1 1 * (M₂ 1 0 * x + M₂ 1 1 * y)) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two]; congr 1 <;> ring
    rw [hlin, he₁, he₂]

lemma GL2Equiv.symm {d : ℕ} {f g : BQF d} (h : GL2Equiv f g) : GL2Equiv g f := by
  obtain ⟨M, hdet, he⟩ := h
  let N : Matrix (Fin 2) (Fin 2) ℤ := M.det • !![M 1 1, -M 0 1; -M 1 0, M 0 0]
  have hdsq : M.det ^ 2 = 1 := by rcases hdet with h1 | h1 <;> simp [h1]
  have hMN : M * N = 1 := by
    ext i j
    have hdetf : M 0 0 * M 1 1 - M 0 1 * M 1 0 = M.det := (Matrix.det_fin_two M).symm
    fin_cases i <;> fin_cases j <;> simp [N, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination M.det * hdetf + hdsq
    · ring
    · ring
    · linear_combination M.det * hdetf + hdsq
  refine ⟨N, ?_, fun x y => ?_⟩
  · have h1 : M.det * N.det = 1 := by rw [← Matrix.det_mul, hMN, Matrix.det_one]
    rcases hdet with hd1 | hd1 <;> rw [hd1] at h1
    · left; linarith
    · right; linarith
  · have hx : M 0 0 * (N 0 0 * x + N 0 1 * y) + M 0 1 * (N 1 0 * x + N 1 1 * y) = x := by
      have h00 := congrFun (congrFun hMN 0) 0
      have h01 := congrFun (congrFun hMN 0) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)] at h00 h01
      linear_combination x * h00 + y * h01
    have hy : M 1 0 * (N 0 0 * x + N 0 1 * y) + M 1 1 * (N 1 0 * x + N 1 1 * y) = y := by
      have h10 := congrFun (congrFun hMN 1) 0
      have h11 := congrFun (congrFun hMN 1) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h10 h11
      linear_combination x * h10 + y * h11
    have h := he (N 0 0 * x + N 0 1 * y) (N 1 0 * x + N 1 1 * y)
    rw [hx, hy] at h
    exact h.symm

lemma sl2Equiv_shift {d : ℕ} (f : BQF d) (k : ℤ) (hd : 0 < d) :
    SL2Equiv f (f.shift k hd) := by
  refine ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two], fun x y => ?_⟩
  simp [eval, shift]; ring

lemma sl2Equiv_swap {d : ℕ} (f : BQF d) : SL2Equiv f f.swap := by
  refine ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two], fun x y => ?_⟩
  simp [eval, swap]; ring

/-- Inductive relation of Gauss reduction steps (`shift` and `swap`). -/
inductive StepEquiv {d : ℕ} (hd : 0 < d) : BQF d → BQF d → Prop
  | refl (f : BQF d) : StepEquiv hd f f
  | shift (f g : BQF d) (k : ℤ) : StepEquiv hd (f.shift k hd) g → StepEquiv hd f g
  | swap (f g : BQF d) : StepEquiv hd f.swap g → StepEquiv hd f g

lemma StepEquiv.toSL2 {d : ℕ} {hd : 0 < d} {f g : BQF d} (h : StepEquiv hd f g) :
    SL2Equiv f g := by
  induction h with
  | refl f => exact SL2Equiv.refl f
  | shift f g k _ ih => exact (sl2Equiv_shift f k hd).trans ih
  | swap f g _ ih => exact (sl2Equiv_swap f).trans ih

/-- Gauss reduction: every `f : BQF d` reduces via `shift` and `swap` steps to a reduced form. -/
theorem exists_reduced_stepEquiv {d : ℕ} (hd : 0 < d) (f : BQF d) :
    ∃ g : BQF d, g.isReduced ∧ StepEquiv hd f g := by
  suffices h : ∀ n : ℕ, ∀ f : BQF d, f.a.toNat ≤ n → ∃ g : BQF d, g.isReduced ∧ StepEquiv hd f g from
    h f.a.toNat f le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hfn
    -- Choose k such that |f.b + 2*k*f.a| ≤ f.a
    set m := f.a
    have hm : 0 < m := f.ha
    set k := (-(f.b) + m) / (2 * m)
    have hdiv : (2 * m) * k + (-(f.b) + m) % (2 * m) = -(f.b) + m :=
      Int.mul_ediv_add_emod (-(f.b) + m) (2 * m)
    have hrem_nn : 0 ≤ (-(f.b) + m) % (2 * m) := Int.emod_nonneg _ (by omega)
    have hrem_lt : (-(f.b) + m) % (2 * m) < 2 * m := Int.emod_lt_of_pos _ (by omega)
    set f₁ := f.shift k hd
    have hb1 : |f₁.b| ≤ f₁.a := by
      dsimp only [f₁, shift]
      rw [abs_le]
      constructor <;> nlinarith
    by_cases hac : f₁.a ≤ f₁.c
    · exact ⟨f₁, ⟨hb1, hac⟩, StepEquiv.shift f f₁ k (StepEquiv.refl f₁)⟩
    · have hlt : f₁.swap.a.toNat < n := by
        dsimp only [swap, f₁, shift] at hac ⊢
        omega
      obtain ⟨g, hgr, hstep⟩ := ih f₁.swap.a.toNat hlt f₁.swap le_rfl
      exact ⟨g, hgr, StepEquiv.shift f g k (StepEquiv.swap f₁ g hstep)⟩

/-- Finset of all reduced forms of discriminant `-d`. -/
noncomputable def reducedForms (d : ℕ) : Finset (BQF d) :=
  let boxA := Finset.Icc (1 : ℤ) (d : ℤ)
  let boxB := Finset.Icc (-(d : ℤ)) (d : ℤ)
  let boxC := Finset.Icc (1 : ℤ) (d : ℤ)
  let S : Finset (ℤ × ℤ × ℤ) := (boxA ×ˢ (boxB ×ˢ boxC)).filter fun t =>
    4 * t.1 * t.2.2 - t.2.1 ^ 2 = (d : ℤ) ∧ |t.2.1| ≤ t.1 ∧ t.1 ≤ t.2.2
  S.attach.image fun (t : {p // p ∈ S}) =>
    let h1 := (Finset.mem_product.mp (Finset.mem_filter.mp t.2).1)
    let h2 := (Finset.mem_product.mp h1.2)
    let ha : 0 < t.1.1 := by have := (Finset.mem_Icc.mp h1.1).1; omega
    let hc : 0 < t.1.2.2 := by have := (Finset.mem_Icc.mp h2.2).1; omega
    ⟨t.1.1, t.1.2.1, t.1.2.2, ha, hc, (Finset.mem_filter.mp t.2).2.1⟩

lemma mem_reducedForms_iff {d : ℕ} (hd : 0 < d) (f : BQF d) :
    f ∈ reducedForms d ↔ f.isReduced := by
  constructor
  · intro hf
    simp only [reducedForms, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hf
    obtain ⟨t, ht, heq⟩ := hf
    have hfilt := (Finset.mem_filter.mp ht).2
    have ha := congrArg BQF.a heq
    have hb := congrArg BQF.b heq
    have hc := congrArg BQF.c heq
    dsimp only at ha hb hc
    dsimp only [isReduced]
    rw [← ha, ← hb, ← hc]; exact ⟨hfilt.2.1, hfilt.2.2⟩
  · intro ⟨hba, hac⟩
    have ha_le : f.a ≤ (d : ℤ) := by
      have hb2 : f.b ^ 2 ≤ f.a ^ 2 := by nlinarith [(abs_le.mp hba).1, (abs_le.mp hba).2]
      have h3a2 : 3 * f.a ^ 2 ≤ (d : ℤ) := by nlinarith [f.hdisc, f.ha]
      nlinarith [f.ha]
    have hb_le : -(d : ℤ) ≤ f.b ∧ f.b ≤ (d : ℤ) := by
      have := abs_le.mp hba; constructor <;> linarith
    have hc_le : f.c ≤ (d : ℤ) := by
      have hb2 : f.b ^ 2 ≤ f.a * f.c := by nlinarith [(abs_le.mp hba).1, (abs_le.mp hba).2, f.ha]
      have h3c : 3 * f.a * f.c ≤ (d : ℤ) := by linarith [f.hdisc]
      nlinarith [f.ha, f.hc]
    simp only [reducedForms, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
    refine ⟨(f.a, (f.b, f.c)), ?_, BQF.ext rfl rfl rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by linarith [f.ha], ha_le⟩,
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hb_le, Finset.mem_Icc.mpr ⟨by linarith [f.hc], hc_le⟩⟩⟩,
      f.hdisc, hba, hac⟩

/-- Uniqueness of reduced forms under `GL₂(ℤ)` equivalence: if `f, g` are reduced and `GL2Equiv f g`,
then `g = f ∨ g = f.conj`. -/
lemma reduced_gl2Equiv_eq_or_conj {d : ℕ} (hd : 0 < d) {f g : BQF d}
    (hf : f.isReduced) (hg : g.isReduced) (heq : GL2Equiv f g) :
    g = f ∨ g = f.conj := by
  have hmin_ge : ∀ (h : BQF d), h.isReduced → ∀ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) → h.a ≤ h.eval x y := by
    intro h ⟨hba, hac⟩ x y hxy
    have habs : |h.b * x * y| ≤ h.a * |x| * |y| := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hba (abs_nonneg x)) (abs_nonneg y)
    by_cases hx : x = 0
    · subst hx
      have hy : y ≠ 0 := hxy.resolve_left (not_not.mpr rfl)
      have hy2 : 1 ≤ y ^ 2 := by rcases lt_or_gt_of_ne hy with h1 | h1 <;> nlinarith
      dsimp only [eval]; nlinarith [h.hc]
    · by_cases hy : y = 0
      · subst hy
        have hx2 : 1 ≤ x ^ 2 := by rcases lt_or_gt_of_ne hx with h1 | h1 <;> nlinarith
        dsimp only [eval]; nlinarith [h.ha]
      · have hx1 : 1 ≤ |x| := by
          rcases lt_or_gt_of_ne hx with h1 | h1
          · rw [abs_of_neg h1]; omega
          · rw [abs_of_pos h1]; omega
        have hy1 : 1 ≤ |y| := by
          rcases lt_or_gt_of_ne hy with h1 | h1
          · rw [abs_of_neg h1]; omega
          · rw [abs_of_pos h1]; omega
        have hev : h.eval x y ≥ h.a * x ^ 2 - h.a * |x| * |y| + h.c * y ^ 2 := by
          dsimp only [eval]; linarith [(abs_le.mp habs).1]
        have hsq : h.a * x ^ 2 - h.a * |x| * |y| + h.c * y ^ 2 ≥ h.a * (|x| - |y|) ^ 2 + h.a * |x| * |y| := by
          nlinarith [sq_abs x, sq_abs y, h.ha]
        have hmul : h.a ≤ h.a * |x| * |y| := by
          have hxy1 : 1 ≤ |x| * |y| := by nlinarith [hx1, hy1]
          nlinarith [h.ha]
        nlinarith [sq_nonneg (|x| - |y|), h.ha]
  have hy_ge_c : ∀ (h : BQF d), h.isReduced → ∀ x y : ℤ, y ≠ 0 → h.c ≤ h.eval x y := by
    intro h ⟨hba, hac⟩ x y hy
    by_cases hy1 : |y| = 1
    · have hy2 : y ^ 2 = 1 := by nlinarith [sq_abs y]
      have hbx : -(h.a * x ^ 2) ≤ h.b * x * y := by
        have h1 : |h.b * x * y| ≤ h.a * |x| := by
          rw [abs_mul, abs_mul, hy1, mul_one]
          exact mul_le_mul_of_nonneg_right hba (abs_nonneg x)
        have h2 : |x| ≤ x ^ 2 := by
          have : 0 ≤ |x| * (|x| - 1) := by
            rcases eq_or_ne x 0 with rfl | hx
            · simp
            · have : 1 ≤ |x| := by
                rcases lt_or_gt_of_ne hx with h' | h'
                · rw [abs_of_neg h']; omega
                · rw [abs_of_pos h']; omega
              nlinarith
          nlinarith [sq_abs x]
        linarith [(abs_le.mp h1).1, mul_le_mul_of_nonneg_left h2 h.ha.le]
      dsimp only [eval]; rw [hy2]; linarith
    · have hy2 : 2 ≤ |y| := by
        have h1 : 1 ≤ |y| := by
          rcases lt_or_gt_of_ne hy with h' | h'
          · rw [abs_of_neg h']; omega
          · rw [abs_of_pos h']; omega
        omega
      have h4 : 4 * h.a * h.eval x y = (2 * h.a * x + h.b * y) ^ 2 + (d : ℤ) * y ^ 2 := by
        dsimp only [eval]; linear_combination y ^ 2 * h.hdisc
      have hd3 : 3 * h.a * h.c ≤ (d : ℤ) := by
        have hb2 : h.b ^ 2 ≤ h.a * h.c := by nlinarith [(abs_le.mp hba).1, (abs_le.mp hba).2, h.ha]
        linarith [h.hdisc]
      have hysq : 4 ≤ y ^ 2 := by nlinarith [sq_abs y]
      nlinarith [sq_nonneg (2 * h.a * x + h.b * y), h.ha, h.hc]
  -- Extract a_f = a_g and c_f = c_g
  obtain ⟨M, hdet, hMe⟩ := heq
  have hcol1_ne : M 0 0 ≠ 0 ∨ M 1 0 ≠ 0 := by
    by_contra h; push Not at h
    rw [Matrix.det_fin_two, h.1, h.2] at hdet; norm_num at hdet
  have hcol2_ne : M 0 1 ≠ 0 ∨ M 1 1 ≠ 0 := by
    by_contra h; push Not at h
    rw [Matrix.det_fin_two, h.1, h.2] at hdet; norm_num at hdet
  have hag : f.a ≤ g.a := by
    have h1 := hMe 1 0; simp only [eval, mul_one, mul_zero, add_zero, one_pow, zero_pow two_ne_zero] at h1
    rw [← h1]; exact hmin_ge f hf (M 0 0) (M 1 0) hcol1_ne
  obtain ⟨N, hNdet, hNe⟩ := (GL2Equiv.symm ⟨M, hdet, hMe⟩)
  have hga : g.a ≤ f.a := by
    have hNc1 : N 0 0 ≠ 0 ∨ N 1 0 ≠ 0 := by
      by_contra h; push Not at h; rw [Matrix.det_fin_two, h.1, h.2] at hNdet; norm_num at hNdet
    have h1 := hNe 1 0; simp only [eval, mul_one, mul_zero, add_zero, one_pow, zero_pow two_ne_zero] at h1
    rw [← h1]; exact hmin_ge g hg (N 0 0) (N 1 0) hNc1
  have ha_eq : f.a = g.a := le_antisymm hag hga
  have hcg : f.c ≤ g.c := by
    by_cases h10 : M 1 0 = 0
    · have h11 : M 1 1 ≠ 0 := by
        intro h11; rw [Matrix.det_fin_two, h10, h11] at hdet; norm_num at hdet
      have h2 := hMe 0 1; simp only [eval, mul_zero, zero_add, mul_one, zero_pow two_ne_zero, one_pow] at h2
      rw [← h2]; exact hy_ge_c f hf (M 0 1) (M 1 1) h11
    · have h1 := hMe 1 0; simp only [eval, mul_one, mul_zero, add_zero, one_pow, zero_pow two_ne_zero] at h1
      have hfc_le_ga : f.c ≤ g.a := by rw [← h1]; exact hy_ge_c f hf (M 0 0) (M 1 0) h10
      linarith [hg.2]
  have hgc : g.c ≤ f.c := by
    by_cases h10 : N 1 0 = 0
    · have h11 : N 1 1 ≠ 0 := by
        intro h11; rw [Matrix.det_fin_two, h10, h11] at hNdet; norm_num at hNdet
      have h2 := hNe 0 1; simp only [eval, mul_zero, zero_add, mul_one, zero_pow two_ne_zero, one_pow] at h2
      rw [← h2]; exact hy_ge_c g hg (N 0 1) (N 1 1) h11
    · have h1 := hNe 1 0; simp only [eval, mul_one, mul_zero, add_zero, one_pow, zero_pow two_ne_zero] at h1
      have hgc_le_fa : g.c ≤ f.a := by rw [← h1]; exact hy_ge_c g hg (N 0 0) (N 1 0) h10
      linarith [hf.2]
  have hc_eq : f.c = g.c := le_antisymm hcg hgc
  have hb2 : g.b ^ 2 = f.b ^ 2 := by
    have h1 := f.hdisc; have h2 := g.hdisc; rw [ha_eq, hc_eq] at h1; linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hb2 with hb | hb
  · left; exact BQF.ext ha_eq.symm hb hc_eq.symm
  · right; exact BQF.ext ha_eq.symm hb hc_eq.symm

/-!
### Part 2: Elementary Dirichlet Class Number Lower Bound `h_d ≥ (√d / 8) * L(1, χ_d)`
-/

/-- Representations `(x, y) ∈ ℤ²` of `n` by `f : BQF d`. -/
noncomputable def repForm {d : ℕ} (f : BQF d) (n : ℕ) : Finset (ℤ × ℤ) :=
  let B : ℤ := 2 * (n : ℤ) + 1
  (Finset.Icc (-B) B ×ˢ Finset.Icc (-B) B).filter fun p => f.eval p.1 p.2 = (n : ℤ)

lemma mem_repForm_iff {d : ℕ} (hd : 0 < d) {f : BQF d} (hf : f.isReduced) (n : ℕ) (p : ℤ × ℤ) :
    p ∈ repForm f n ↔ f.eval p.1 p.2 = (n : ℤ) := by
  simp only [repForm, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_iff_right_iff_imp]
  intro h
  have h4 : 4 * f.a * (n : ℤ) = (2 * f.a * p.1 + f.b * p.2) ^ 2 + (d : ℤ) * p.2 ^ 2 := by
    rw [← h]; dsimp only [eval]; linear_combination p.2 ^ 2 * f.hdisc
  have hy_sq : p.2 ^ 2 ≤ 4 * f.a * (n : ℤ) := by
    have hd1 : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    nlinarith [sq_nonneg (2 * f.a * p.1 + f.b * p.2), sq_nonneg p.2]
  have hy_sq2 : 3 * p.2 ^ 2 ≤ 4 * (n : ℤ) := by
    have hb2 : f.b ^ 2 ≤ f.a ^ 2 := by nlinarith [(abs_le.mp hf.1).1, (abs_le.mp hf.1).2]
    have h3 : 3 * f.a ^ 2 ≤ (d : ℤ) := by nlinarith [f.hdisc, hf.2, f.ha]
    have h3a : 3 * f.a * p.2 ^ 2 ≤ (d : ℤ) * p.2 ^ 2 := by
      have : 3 * f.a ≤ (d : ℤ) := by nlinarith [f.ha]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg p.2)
    -- Better: 4*a*n = (2ax+by)^2 + d*y^2 ≥ 3*a^2*y^2 -> 4*n ≥ 3*a*y^2 ≥ 3*y^2!
    have h3a2y : 3 * f.a ^ 2 * p.2 ^ 2 ≤ 4 * f.a * (n : ℤ) := by
      nlinarith [sq_nonneg (2 * f.a * p.1 + f.b * p.2), sq_nonneg p.2]
    nlinarith [f.ha, sq_nonneg p.2]
  have hy_le : |p.2| ≤ 2 * (n : ℤ) + 1 := by
    have h1 : p.2 ^ 2 ≤ (2 * (n : ℤ) + 1) ^ 2 := by nlinarith [sq_nonneg p.2]
    rw [abs_le]
    exact ⟨by nlinarith, by nlinarith⟩
  have hx_le : |p.1| ≤ 2 * (n : ℤ) + 1 := by
    have h2ax : (2 * f.a * p.1 + f.b * p.2) ^ 2 ≤ 4 * f.a * (n : ℤ) := by
      have hd0 : (0 : ℤ) ≤ (d : ℤ) := Nat.cast_nonneg d
      nlinarith [sq_nonneg p.2]
    have h2ax_abs : |2 * f.a * p.1 + f.b * p.2| ≤ 2 * f.a * (n : ℤ) + 2 * f.a := by
      have : (2 * f.a * p.1 + f.b * p.2) ^ 2 ≤ (2 * f.a * (n : ℤ) + 2 * f.a) ^ 2 := by
        nlinarith [f.ha, sq_nonneg (n : ℤ)]
      rw [abs_le]; exact ⟨by nlinarith [f.ha], by nlinarith [f.ha]⟩
    have hby_abs : |f.b * p.2| ≤ f.a * (2 * (n : ℤ) + 1) := by
      rw [abs_mul]; exact mul_le_mul hf.1 hy_le (abs_nonneg p.2) f.ha.le
    have h2a_p1 : |2 * f.a * p.1| ≤ |2 * f.a * p.1 + f.b * p.2| + |f.b * p.2| := by
      have := abs_sub (2 * f.a * p.1 + f.b * p.2) (f.b * p.2)
      simpa using this
    have h2a_bound : 2 * f.a * |p.1| ≤ 2 * f.a * (2 * (n : ℤ) + 1) + f.a := by
      have heq : |2 * f.a * p.1| = 2 * f.a * |p.1| := by
        rw [abs_mul, abs_of_pos (by linarith [f.ha])]
      rw [← heq]; linarith
    have h2a_strict : 2 * f.a * |p.1| < 2 * f.a * (2 * (n : ℤ) + 2) := by linarith [f.ha]
    have hp1_lt : |p.1| < 2 * (n : ℤ) + 2 := by nlinarith [f.ha]
    omega
  exact ⟨abs_le.mp hx_le, abs_le.mp hy_le⟩

/-- Number of roots of `b² + d ≡ 0 (mod 4n)` with `0 ≤ b < 2n`. -/
def rootCount (d n : ℕ) : ℕ :=
  ((Finset.range (2 * n)).filter fun b => 4 * n ∣ b ^ 2 + d).card

lemma rootCount_one (d : ℕ) (hd : d % 4 = 3) : rootCount d 1 = 1 := by
  have h : (Finset.range 2).filter (fun b => 4 ∣ b ^ 2 + d) = {1} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · intro ⟨hb, hdvd⟩
      have hb01 : b = 0 ∨ b = 1 := by omega
      rcases hb01 with rfl | rfl
      · exfalso; obtain ⟨k, hk⟩ := hdvd; omega
      · rfl
    · rintro rfl; exact ⟨by omega, ⟨(d + 1) / 4, by omega⟩⟩
  simpa [rootCount] using congrArg Finset.card h

lemma rootCount_even_eq_zero (d n : ℕ) (hd : d % 8 = 3) (hn : 2 ∣ n) (hn0 : 0 < n) :
    rootCount d n = 0 := by
  rw [rootCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b _ h4n
  have h8 : 8 ∣ b ^ 2 + d := dvd_trans (by obtain ⟨k, rfl⟩ := hn; exact ⟨k, by ring⟩) h4n
  obtain ⟨k, hk⟩ := h8
  have hbm : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by omega
  have hsq : (b ^ 2) % 8 = ((b % 8) ^ 2) % 8 := by rw [Nat.pow_mod]
  rcases hbm with h | h | h | h | h | h | h | h <;> rw [h] at hsq <;> omega

/-- For odd `n ≥ 1` and `d ≡ 3 (mod 4)`, `rootCount d n = #{r : ZMod n | r² + d = 0}`. -/
lemma rootCount_odd_eq (d n : ℕ) [NeZero n] (hd : d % 4 = 3) (hn : Odd n) :
    rootCount d n = (Finset.univ.filter fun r : ZMod n => r ^ 2 + (d : ZMod n) = 0).card := by
  have hn0 : 0 < n := NeZero.pos n
  rw [rootCount]
  refine Finset.card_bij (fun b _ => (b : ZMod n)) ?_ ?_ ?_
  · intro b hb
    obtain ⟨_, h4n⟩ := Finset.mem_filter.mp hb
    have hnd : n ∣ b ^ 2 + d := dvd_trans ⟨4, by ring⟩ h4n
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h0 : ((b ^ 2 + d : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ n).mpr hnd
    push_cast at h0; exact h0
  · intro b₁ hb₁ b₂ hb₂ heq
    obtain ⟨hb₁r, h4n₁⟩ := Finset.mem_filter.mp hb₁
    obtain ⟨hb₂r, h4n₂⟩ := Finset.mem_filter.mp hb₂
    rw [Finset.mem_range] at hb₁r hb₂r
    have h41 : 4 ∣ b₁ ^ 2 + d := dvd_trans ⟨n, by ring⟩ h4n₁
    have h42 : 4 ∣ b₂ ^ 2 + d := dvd_trans ⟨n, by ring⟩ h4n₂
    have hb₁odd : b₁ % 2 = 1 := by
      rcases Nat.even_or_odd b₁ with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · obtain ⟨t, ht⟩ := h41
        have : (k + k) ^ 2 = 4 * k ^ 2 := by ring
        omega
      · omega
    have hb₂odd : b₂ % 2 = 1 := by
      rcases Nat.even_or_odd b₂ with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · obtain ⟨t, ht⟩ := h42
        have : (k + k) ^ 2 = 4 * k ^ 2 := by ring
        omega
      · omega
    have hmodn : b₁ % n = b₂ % n := (ZMod.natCast_eq_natCast_iff' b₁ b₂ n).mp heq
    have hcases1 : b₁ = b₁ % n ∨ b₁ = b₁ % n + n := by
      have hdm := Nat.div_add_mod b₁ n
      have hdiv : b₁ / n < 2 := Nat.div_lt_of_lt_mul (by omega)
      interval_cases h : b₁ / n <;> [left; right] <;> omega
    have hcases2 : b₂ = b₂ % n ∨ b₂ = b₂ % n + n := by
      have hdm := Nat.div_add_mod b₂ n
      have hdiv : b₂ / n < 2 := Nat.div_lt_of_lt_mul (by omega)
      interval_cases h : b₂ / n <;> [left; right] <;> omega
    obtain ⟨m, rfl⟩ := hn
    rcases hcases1 with h1 | h1 <;> rcases hcases2 with h2 | h2 <;> omega
  · intro r hr
    have hr0 : r ^ 2 + (d : ZMod n) = 0 := (Finset.mem_filter.mp hr).2
    let b : ℕ := if r.val % 2 = 1 then r.val else r.val + n
    have hbodd : b % 2 = 1 := by
      dsimp only [b]; obtain ⟨m, hm⟩ := hn; split_ifs <;> omega
    have hbrange : b < 2 * n := by
      have := r.val_lt; dsimp only [b]; split_ifs <;> omega
    have hbmod : (b : ZMod n) = r := by
      dsimp only [b]; split_ifs
      · exact ZMod.natCast_zmod_val r
      · push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
    have hndvd : n ∣ b ^ 2 + d := by
      rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [hbmod]; exact hr0
    have h4dvd : 4 ∣ b ^ 2 + d := by
      obtain ⟨k, hk⟩ : ∃ k, b = 2 * k + 1 := ⟨b / 2, by omega⟩
      have : b ^ 2 = 4 * (k ^ 2 + k) + 1 := by rw [hk]; ring
      exact ⟨k ^ 2 + k + (d + 1) / 4, by omega⟩
    have hcop : Nat.Coprime 4 n := by
      have h2 : Nat.Coprime 2 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by obtain ⟨m, rfl⟩ := hn; omega)
      simpa using h2.pow_left 2
    exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hbrange, hcop.mul_dvd_of_dvd_of_dvd h4dvd hndvd⟩, hbmod⟩

/-- Multiplicativity of `rootCount d` on coprime `m, n`. -/
lemma rootCount_mul (d m n : ℕ) (hd : d % 8 = 3) (hcop : Nat.Coprime m n) (hm : 0 < m) (hn : 0 < n) :
    rootCount d (m * n) = rootCount d m * rootCount d n := by
  by_cases hm2 : 2 ∣ m
  · rw [rootCount_even_eq_zero d m hd hm2 hm, rootCount_even_eq_zero d (m * n) hd (dvd_mul_of_dvd_left hm2 n) (Nat.mul_pos hm hn), zero_mul]
  · by_cases hn2 : 2 ∣ n
    · rw [rootCount_even_eq_zero d n hd hn2 hn, rootCount_even_eq_zero d (m * n) hd (dvd_mul_of_dvd_right hn2 m) (Nat.mul_pos hm hn), mul_zero]
    · have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
      have hnodd : Odd n := Nat.odd_iff.mpr (by omega)
      have hmnodd : Odd (m * n) := hmodd.mul hnodd
      have : NeZero m := ⟨hm.ne'⟩
      have : NeZero n := ⟨hn.ne'⟩
      have : NeZero (m * n) := ⟨(Nat.mul_pos hm hn).ne'⟩
      rw [rootCount_odd_eq d (m * n) (by omega) hmnodd,
        rootCount_odd_eq d m (by omega) hmodd,
        rootCount_odd_eq d n (by omega) hnodd, ← Finset.card_product]
      let e := ZMod.chineseRemainder hcop
      refine Finset.card_bij (fun r _ => e r) ?_ ?_ ?_
      · intro r hr
        have hr0 : r ^ 2 + (d : ZMod (m * n)) = 0 := (Finset.mem_filter.mp hr).2
        have he := congrArg e hr0
        rw [map_add, map_pow, map_natCast, map_zero] at he
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
        exact ⟨⟨Finset.mem_univ _, by simpa using congrArg Prod.fst he⟩,
          ⟨Finset.mem_univ _, by simpa using congrArg Prod.snd he⟩⟩
      · intro r₁ _ r₂ _ heq; exact e.injective heq
      · intro p hp
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
        refine ⟨e.symm p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply p⟩
        apply e.injective
        rw [map_add, map_pow, map_natCast, map_zero, e.apply_symm_apply]
        exact Prod.ext (by simpa using hp.1.2) (by simpa using hp.2.2)

/-- Hensel lifting: for odd prime `p ∤ d` and `k ≥ 1`, `rootCount d (p^k) = if jacobiSym p d = 1 then 2 else 0`. -/
lemma rootCount_prime_pow_not_dvd {d p : ℕ} (hd : d % 8 = 3) (hp : p.Prime) (hp2 : p ≠ 2)
    (hnpd : ¬ p ∣ d) (k : ℕ) (hk : 1 ≤ k) :
    rootCount d (p ^ k) = if jacobiSym (p : ℤ) d = 1 then 2 else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd_p : Odd p := hp.odd_of_ne_two hp2
  have hodd_d : Odd d := ⟨d / 2, by omega⟩
  have hrec : legendreSym p (-(d : ℤ)) = jacobiSym (p : ℤ) d := by
    rw [jacobiSym.legendreSym.to_jacobiSym, show -(d : ℤ) = (-1 : ℤ) * (d : ℤ) by ring,
      jacobiSym.mul_left, jacobiSym.at_neg_one hodd_p]
    have hpm : p % 4 = 1 ∨ p % 4 = 3 := by obtain ⟨m, rfl⟩ := hodd_p; omega
    rcases hpm with hp1 | hp3
    · have h1 : ZMod.χ₄ (p : ZMod 4) = 1 := by
        rw [ZMod.χ₄_nat_eq_if_mod_four]; simp [show p % 2 = 1 by omega, hp1]
      rw [h1, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four hp1 hodd_d]
    · have h1 : ZMod.χ₄ (p : ZMod 4) = -1 := by
        rw [ZMod.χ₄_nat_eq_if_mod_four]; simp [show p % 2 = 1 by omega, hp3]
      rw [h1, jacobiSym.quadratic_reciprocity_three_mod_four (show d % 4 = 3 by omega) hp3]
      ring
  -- Count roots of r² + d = 0 in ZMod (p^k) by induction on k ≥ 1
  have hcount : ∀ m : ℕ, 1 ≤ m →
      have : NeZero (p ^ m) := ⟨pow_ne_zero m hp.ne_zero⟩
      (Finset.univ.filter fun r : ZMod (p ^ m) => r ^ 2 + (d : ZMod (p ^ m)) = 0).card =
        if legendreSym p (-(d : ℤ)) = 1 then 2 else 0 := by
    intro m hm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hm
    induction j with
    | zero =>
      dsimp only
      have hrew : ∀ (q : ℕ) [NeZero q], q = p →
          (Finset.univ.filter fun r : ZMod q => r ^ 2 + (d : ZMod q) = 0).card =
          (Finset.univ.filter fun r : ZMod p => r ^ 2 + (d : ZMod p) = 0).card := by
        rintro q _ rfl; rfl
      have : NeZero (p ^ (0 + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      rw [hrew (p ^ (0 + 1)) (by simp)]
      have hdne : ((-(d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
        intro h; apply hnpd
        push_cast at h
        have h0 : ((d : ℕ) : ZMod p) = 0 := by linear_combination -h
        exact (ZMod.natCast_eq_zero_iff d p).mp h0
      by_cases hleg : legendreSym p (-(d : ℤ)) = 1
      · rw [if_pos hleg]
        have hsq : IsSquare ((-(d : ℤ) : ℤ) : ZMod p) := (legendreSym.eq_one_iff p hdne).mp hleg
        obtain ⟨u, hu⟩ := hsq
        have hune : u ≠ 0 := by intro h; subst h; rw [mul_zero] at hu; exact hdne hu
        have hune_neg : u ≠ -u := by
          intro h
          have h2u : (2 : ZMod p) * u = 0 := by linear_combination h
          have h2ne : (2 : ZMod p) ≠ 0 := by
            intro h2; exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp h2))
          exact hune ((mul_eq_zero.mp h2u).resolve_left h2ne)
        have hset : (Finset.univ.filter fun r : ZMod p => r ^ 2 + (d : ZMod p) = 0) = {u, -u} := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
          have hu2 : u ^ 2 = -(d : ZMod p) := by
            push_cast at hu; linear_combination -hu
          constructor
          · intro hr
            have hsq_eq : r ^ 2 = u ^ 2 := by linear_combination hr - hu2
            exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq_eq
          · rintro (rfl | rfl) <;> linear_combination hu2
        rw [hset, Finset.card_pair hune_neg]
      · rw [if_neg hleg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro r _ hr
        apply hleg
        rw [legendreSym.eq_one_iff p hdne]
        refine ⟨r, ?_⟩
        push_cast; linear_combination -hr
    | succ j ih =>
      have : NeZero (p ^ (j + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      have : NeZero (p ^ (j + 2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      rw [← ih (by omega)]
      -- Hensel lifting bijection between roots mod p^(j+2) and roots mod p^(j+1)
      let proj : ZMod (p ^ (j + 2)) →+* ZMod (p ^ (j + 1)) :=
        ZMod.castHom (pow_dvd_pow p (by omega)) (ZMod (p ^ (j + 1)))
      have h2p : Nat.Coprime (2 : ℕ) p := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by
        intro h; exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm)
      refine Finset.card_bij (fun r _ => proj r) ?_ ?_ ?_
      · intro r hr
        have hr0 : r ^ 2 + (d : ZMod (p ^ (j + 2))) = 0 := (Finset.mem_filter.mp hr).2
        have hp0 := congrArg proj hr0
        rw [map_add, map_pow, map_natCast, map_zero] at hp0
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp0⟩
      · intro r₁ hr₁ r₂ hr₂ hproj
        have h1 : r₁ ^ 2 + (d : ZMod (p ^ (j + 2))) = 0 := (Finset.mem_filter.mp hr₁).2
        have h2 : r₂ ^ 2 + (d : ZMod (p ^ (j + 2))) = 0 := (Finset.mem_filter.mp hr₂).2
        -- Write r₁.val and r₂.val: since proj r₁ = proj r₂, p^(j+1) ∣ (r₁.val - r₂.val) in ℤ
        have hdvd_diff : (p ^ (j + 1) : ℤ) ∣ (r₁.val : ℤ) - (r₂.val : ℤ) := by
          rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
          push_cast
          have h1' : (r₁.val : ZMod (p ^ (j + 1))) = proj r₁ := by
            rw [← map_natCast proj, ZMod.natCast_zmod_val]
          have h2' : (r₂.val : ZMod (p ^ (j + 1))) = proj r₂ := by
            rw [← map_natCast proj, ZMod.natCast_zmod_val]
          rw [h1', h2', hproj, sub_self]
        obtain ⟨t, ht⟩ := hdvd_diff
        have hdiff_sq : (p ^ (j + 2) : ℤ) ∣ (r₁.val : ℤ) ^ 2 - (r₂.val : ℤ) ^ 2 := by
          rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
          push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
          linear_combination h1 - h2
        have hfac : (r₁.val : ℤ) ^ 2 - (r₂.val : ℤ) ^ 2 =
            (p ^ (j + 1) : ℤ) * t * ((r₁.val : ℤ) + (r₂.val : ℤ)) := by
          linear_combination ((r₁.val : ℤ) + (r₂.val : ℤ)) * ht
        rw [hfac, pow_succ] at hdiff_sq
        have hp_dvd_prod : (p : ℤ) ∣ t * ((r₁.val : ℤ) + (r₂.val : ℤ)) := by
          obtain ⟨w, hw⟩ := hdiff_sq
          have hpne : ((p : ℤ) ^ (j + 1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
          refine ⟨w, mul_left_cancel₀ hpne ?_⟩
          linear_combination hw
        have hnp_sum : ¬ (p : ℤ) ∣ (r₁.val : ℤ) + (r₂.val : ℤ) := by
          intro hsum
          have hp_r2 : (p : ℤ) ∣ 2 * (r₂.val : ℤ) := by
            have hd2 : (p : ℤ) ∣ (r₁.val : ℤ) - (r₂.val : ℤ) :=
              dvd_trans (dvd_pow_self (p : ℤ) (by omega)) ⟨t, ht⟩
            have : 2 * (r₂.val : ℤ) = ((r₁.val : ℤ) + (r₂.val : ℤ)) - ((r₁.val : ℤ) - (r₂.val : ℤ)) := by ring
            rw [this]; exact dvd_sub hsum hd2
          have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
          have hp_r2' : (p : ℤ) ∣ (r₂.val : ℤ) := by
            rcases hpZ.dvd_mul.mp hp_r2 with h2 | hr2
            · exfalso; exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by exact_mod_cast h2))
            · exact hr2
          have hp_d : (p : ℤ) ∣ (r₂.val : ℤ) ^ 2 + (d : ℤ) := by
            have h2' : (p ^ (j + 2) : ℤ) ∣ (r₂.val : ℤ) ^ 2 + (d : ℤ) := by
              rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ZMod.natCast_zmod_val]; exact h2
            exact dvd_trans (dvd_pow_self (p : ℤ) (by omega)) h2'
          have hpd : (p : ℤ) ∣ (d : ℤ) := by
            have := dvd_sub hp_d (dvd_pow hp_r2' two_ne_zero)
            simpa using this
          exact hnpd (Int.natCast_dvd_natCast.mp hpd)
        have hpt : (p : ℤ) ∣ t :=
          ((Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hp_dvd_prod).resolve_right hnp_sum
        have hdvd_full : ((p ^ (j + 2) : ℕ) : ℤ) ∣ (r₁.val : ℤ) - (r₂.val : ℤ) := by
          obtain ⟨t', rfl⟩ := hpt
          exact ⟨t', by push_cast; rw [ht, pow_succ]; ring⟩
        have h0 : (((r₁.val : ℤ) - (r₂.val : ℤ) : ℤ) : ZMod (p ^ (j + 2))) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd_full
        push_cast at h0; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h0
        exact sub_eq_zero.mp h0
      · intro s hs
        have hs0 : s ^ 2 + (d : ZMod (p ^ (j + 1))) = 0 := (Finset.mem_filter.mp hs).2
        have hdvd_s : (p ^ (j + 1) : ℤ) ∣ (s.val : ℤ) ^ 2 + (d : ℤ) := by
          rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ZMod.natCast_zmod_val]; exact hs0
        obtain ⟨q, hq⟩ := hdvd_s
        -- Solve 2 * s.val * t + q ≡ 0 (mod p)
        have hs_ne : (2 * (s.val : ZMod p)) ≠ 0 := by
          intro h0
          have h2ne : (2 : ZMod p) ≠ 0 := by
            intro h2; exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp h2))
          have hs_p : (s.val : ZMod p) = 0 := (mul_eq_zero.mp h0).resolve_left h2ne
          have hp_s : (p : ℤ) ∣ (s.val : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (by simpa using hs_p)
          have hp_sd : (p : ℤ) ∣ (s.val : ℤ) ^ 2 + (d : ℤ) :=
            dvd_trans (dvd_pow_self (p : ℤ) (by omega)) ⟨q, hq⟩
          have hp_d : (p : ℤ) ∣ (d : ℤ) := by
            have := dvd_sub hp_sd (dvd_pow hp_s two_ne_zero); simpa using this
          exact hnpd (Int.natCast_dvd_natCast.mp hp_d)
        let tZ : ZMod p := -((q : ZMod p)) * (2 * (s.val : ZMod p))⁻¹
        let rInt : ℤ := (s.val : ℤ) + (tZ.val : ℤ) * (p ^ (j + 1) : ℤ)
        refine ⟨(rInt : ZMod (p ^ (j + 2))), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · have hr_sq : ((p ^ (j + 2) : ℕ) : ℤ) ∣ rInt ^ 2 + (d : ℤ) := by
            have hlin : (p : ℤ) ∣ q + 2 * (s.val : ℤ) * (tZ.val : ℤ) := by
              rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
              push_cast; rw [ZMod.natCast_zmod_val]
              dsimp only [tZ]
              have : 2 * (s.val : ZMod p) * (-(q : ZMod p) * (2 * (s.val : ZMod p))⁻¹) = -(q : ZMod p) := by
                rw [mul_comm (-(q : ZMod p)), ← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul]
              linear_combination this
            obtain ⟨u, hu⟩ := hlin
            refine ⟨u + (tZ.val : ℤ) ^ 2 * (p ^ j : ℤ), ?_⟩
            dsimp only [rInt]
            have hp2eq : (p ^ (j + 2) : ℤ) = (p ^ (j + 1) : ℤ) * (p : ℤ) := by rw [pow_succ]
            have hp2eq2 : (p ^ (j + 1) : ℤ) ^ 2 = (p ^ (j + 2) : ℤ) * (p ^ j : ℤ) := by
              rw [← pow_mul, ← pow_add]; congr 1; omega
            push_cast
            linear_combination hq + (p ^ (j + 1) : ℤ) * hu + (tZ.val : ℤ) ^ 2 * hp2eq2 - u * hp2eq
          have h0 : ((rInt ^ 2 + (d : ℤ) : ℤ) : ZMod (p ^ (j + 2))) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hr_sq
          push_cast at h0; exact h0
        · rw [map_intCast]
          dsimp only [rInt]
          push_cast
          rw [ZMod.natCast_zmod_val, ← Nat.cast_pow, ZMod.natCast_self, mul_zero, add_zero]
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  rw [rootCount_odd_eq d (p ^ k) (by omega) (Odd.pow hodd_p), hcount k hk, hrec]

lemma rootCount_prime_pow_dvd {d p : ℕ} (hd : d % 8 = 3) (hd_sf : Squarefree d)
    (hp : p.Prime) (hpd : p ∣ d) (k : ℕ) (hk : 1 ≤ k) :
    rootCount d (p ^ k) = if k = 1 then 1 else 0 := by
  have hp2 : p ≠ 2 := by intro h; subst h; obtain ⟨m, hm⟩ := hpd; omega
  have hodd_p : Odd p := hp.odd_of_ne_two hp2
  by_cases hk1 : k = 1
  · subst hk1
    have : NeZero p := ⟨hp.ne_zero⟩
    rw [pow_one, rootCount_odd_eq d p (by omega) hodd_p]
    simp only [↓reduceIte]
    haveI : Fact p.Prime := ⟨hp⟩
    have hset : (Finset.univ.filter fun r : ZMod p => r ^ 2 + (d : ZMod p) = 0) = {0} := by
      ext r
      have hd0 : (d : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).mpr hpd
      simp [hd0]
    rw [hset, Finset.card_singleton]
  · have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
    rw [rootCount_odd_eq d (p ^ k) (by omega) (Odd.pow hodd_p)]
    rw [if_neg hk1, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro r _ hr
    have hpk : p ^ k ∣ r.val ^ 2 + d := by
      rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [ZMod.natCast_zmod_val]; exact hr
    have hp2_dvd : p ^ 2 ∣ r.val ^ 2 + d := dvd_trans (pow_dvd_pow p (by omega)) hpk
    have hp_dvd : p ∣ r.val ^ 2 := by
      have h1 : p ∣ r.val ^ 2 + d := dvd_trans (dvd_pow_self p two_ne_zero) hp2_dvd
      have h2 := Nat.dvd_sub h1 hpd
      simpa using h2
    have hpr : p ∣ r.val := hp.dvd_of_dvd_pow hp_dvd
    have hp2_r2 : p ^ 2 ∣ r.val ^ 2 := pow_dvd_pow_of_dvd hpr 2
    have hp2_d : p ^ 2 ∣ d := by
      have h2 := Nat.dvd_sub hp2_dvd hp2_r2
      simpa using h2
    exact hp.not_isUnit (hd_sf p (by simpa [sq] using hp2_d))

/-- For all `n ≥ 1`, `(1 * χ_d)(n) = ∑_{m² ∣ n} rootCount d (n / m²)`. -/
lemma conv_eq_sum_sq_div_rootCount {d : ℕ} (hd_sf : Squarefree d) (hd : d % 8 = 3)
    (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ n.divisors, (jacobiSym (k : ℤ) d : ℝ)) =
      ∑ m ∈ n.divisors.filter (fun m => m ^ 2 ∣ n), (rootCount d (n / m ^ 2) : ℝ) := by
  -- Define both sides as ArithmeticFunctions and verify multiplicativity + prime power equality!
  let f : ArithmeticFunction ℝ := ⟨fun k => if k = 0 then 0 else
    ∑ j ∈ k.divisors, (jacobiSym (j : ℤ) d : ℝ), by simp⟩
  let g : ArithmeticFunction ℝ := ⟨fun k => if k = 0 then 0 else
    ∑ m ∈ k.divisors.filter (fun m => m ^ 2 ∣ k), (rootCount d (k / m ^ 2) : ℝ), by simp⟩
  have h1 : f n = ∑ k ∈ n.divisors, (jacobiSym (k : ℤ) d : ℝ) := by simp [f, show n ≠ 0 by omega]
  have h2 : g n = ∑ m ∈ n.divisors.filter (fun m => m ^ 2 ∣ n), (rootCount d (n / m ^ 2) : ℝ) := by
    simp [g, show n ≠ 0 by omega]
  rw [← h1, ← h2]
  have hf_mult : f.IsMultiplicative := by
    refine ⟨by simp [f, jacobiSym.one_left], fun {a b} hcop => ?_⟩
    by_cases ha : a = 0
    · subst ha; simp [f]
    · by_cases hb : b = 0
      · subst hb; simp [f]
      · simp only [f, ArithmeticFunction.coe_mk, mul_ne_zero ha hb, ha, hb, ↓reduceIte]
        have hdiv_eq : (a * b).divisors = (a.divisors ×ˢ b.divisors).image fun p => p.1 * p.2 := by
          ext m
          simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_product, Prod.exists]
          constructor
          · intro ⟨hm, _⟩
            refine ⟨Nat.gcd m a, Nat.gcd m b, ⟨⟨Nat.gcd_dvd_right m a, ha⟩, ⟨Nat.gcd_dvd_right m b, hb⟩⟩, ?_⟩
            have hmul : Nat.gcd m a * Nat.gcd m b = Nat.gcd m (a * b) := (hcop.gcd_mul m).symm
            rw [hmul, Nat.gcd_eq_left hm]
          · rintro ⟨m₁, m₂, ⟨⟨h1, _⟩, ⟨h2, _⟩⟩, rfl⟩
            exact ⟨mul_dvd_mul h1 h2, mul_ne_zero ha hb⟩
        have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2)
            ((a.divisors ×ˢ b.divisors : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
          intro p₁ hp₁ p₂ hp₂ heq
          rw [Finset.mem_coe, Finset.mem_product] at hp₁ hp₂
          have h1a := (Nat.mem_divisors.mp hp₁.1).1
          have h1b := (Nat.mem_divisors.mp hp₁.2).1
          have h2a := (Nat.mem_divisors.mp hp₂.1).1
          have h2b := (Nat.mem_divisors.mp hp₂.2).1
          have hd1 : p₁.1 ∣ p₂.1 := ((hcop.coprime_dvd_left h1a).coprime_dvd_right h2b).dvd_of_dvd_mul_right ⟨p₁.2, heq.symm⟩
          have hd2 : p₂.1 ∣ p₁.1 := ((hcop.coprime_dvd_left h2a).coprime_dvd_right h1b).dvd_of_dvd_mul_right ⟨p₂.2, heq⟩
          have heq1 : p₁.1 = p₂.1 := Nat.dvd_antisymm hd1 hd2
          have hp1pos : 0 < p₁.1 := Nat.pos_of_dvd_of_pos h1a (Nat.pos_of_ne_zero ha)
          have heq2 : p₁.2 = p₂.2 := mul_left_cancel₀ hp1pos.ne' (by dsimp only at heq; rw [← heq1] at heq; exact heq)
          exact Prod.ext heq1 heq2
        rw [hdiv_eq, Finset.sum_image hinj, Finset.sum_product]
        have : ∑ x ∈ a.divisors, ∑ y ∈ b.divisors, (jacobiSym ((x * y : ℕ) : ℤ) d : ℝ) =
            ∑ x ∈ a.divisors, (jacobiSym (x : ℤ) d : ℝ) * ∑ y ∈ b.divisors, (jacobiSym (y : ℤ) d : ℝ) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => by rw [Nat.cast_mul, jacobiSym.mul_left]; push_cast; rfl
        rw [this, ← Finset.sum_mul]
  have hg_mult : g.IsMultiplicative := by
    refine ⟨?_, fun {a b} hcop => ?_⟩
    · simp only [g, ArithmeticFunction.coe_mk, one_ne_zero, ↓reduceIte, Nat.divisors_one]
      rw [show (({1} : Finset ℕ).filter fun m => m ^ 2 ∣ 1) = {1} by decide,
        Finset.sum_singleton, one_pow, Nat.div_one, rootCount_one d (by omega), Nat.cast_one]
    by_cases ha : a = 0
    · subst ha; simp [g]
    · by_cases hb : b = 0
      · subst hb; simp [g]
      · simp only [g, ArithmeticFunction.coe_mk, mul_ne_zero ha hb, ha, hb, ↓reduceIte]
        have hbij : ((a * b).divisors.filter fun m => m ^ 2 ∣ a * b) =
            ((a.divisors.filter fun m₁ => m₁ ^ 2 ∣ a) ×ˢ (b.divisors.filter fun m₂ => m₂ ^ 2 ∣ b)).image
              fun p => p.1 * p.2 := by
          ext m
          simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image, Finset.mem_product, Prod.exists]
          constructor
          · intro ⟨⟨hmd, _⟩, hm2⟩
            set m₁ := Nat.gcd m a
            set m₂ := Nat.gcd m b
            have hm12 : m₁ * m₂ = m := by rw [← hcop.gcd_mul m, Nat.gcd_eq_left hmd]
            have hm₁a : m₁ ∣ a := Nat.gcd_dvd_right m a
            have hm₂b : m₂ ∣ b := Nat.gcd_dvd_right m b
            rw [← hm12] at hm2
            have hm₁2 : m₁ ^ 2 ∣ a := (hcop.coprime_dvd_left hm₁a |>.pow_left 2).dvd_of_dvd_mul_right
              (dvd_trans ⟨m₂ ^ 2, by ring⟩ hm2)
            have hm₂2 : m₂ ^ 2 ∣ b := (hcop.symm.coprime_dvd_left hm₂b |>.pow_left 2).dvd_of_dvd_mul_left
              (dvd_trans ⟨m₁ ^ 2, by ring⟩ hm2)
            exact ⟨m₁, m₂, ⟨⟨⟨hm₁a, ha⟩, hm₁2⟩, ⟨⟨hm₂b, hb⟩, hm₂2⟩⟩, hm12⟩
          · rintro ⟨m₁, m₂, ⟨⟨⟨hm₁a, _⟩, hm₁2⟩, ⟨⟨hm₂b, _⟩, hm₂2⟩⟩, rfl⟩
            exact ⟨⟨mul_dvd_mul hm₁a hm₂b, mul_ne_zero ha hb⟩,
              by rw [mul_pow]; exact mul_dvd_mul hm₁2 hm₂2⟩
        have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2)
            (((a.divisors.filter fun m₁ => m₁ ^ 2 ∣ a) ×ˢ (b.divisors.filter fun m₂ => m₂ ^ 2 ∣ b) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
          intro p₁ hp₁ p₂ hp₂ heq
          rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp₁ hp₂
          have h1a := (Nat.mem_divisors.mp hp₁.1.1).1
          have h1b := (Nat.mem_divisors.mp hp₁.2.1).1
          have h2a := (Nat.mem_divisors.mp hp₂.1.1).1
          have h2b := (Nat.mem_divisors.mp hp₂.2.1).1
          have hcop12 : Nat.Coprime p₁.1 p₂.2 := (hcop.coprime_dvd_left h1a).coprime_dvd_right h2b
          have hcop21 : Nat.Coprime p₂.1 p₁.2 := (hcop.coprime_dvd_left h2a).coprime_dvd_right h1b
          have hd1 : p₁.1 ∣ p₂.1 := hcop12.dvd_of_dvd_mul_right ⟨p₁.2, heq.symm⟩
          have hd2 : p₂.1 ∣ p₁.1 := hcop21.dvd_of_dvd_mul_right ⟨p₂.2, heq⟩
          have heq1 : p₁.1 = p₂.1 := Nat.dvd_antisymm hd1 hd2
          have hp1pos : 0 < p₁.1 := Nat.pos_of_dvd_of_pos h1a (Nat.pos_of_ne_zero ha)
          have heq2 : p₁.2 = p₂.2 := mul_left_cancel₀ hp1pos.ne' (by dsimp only at heq; rw [← heq1] at heq; exact heq)
          exact Prod.ext heq1 heq2
        rw [hbij, Finset.sum_image hinj, Finset.sum_product]
        have hterm : ∀ m₁ ∈ a.divisors.filter (fun m => m ^ 2 ∣ a),
            ∀ m₂ ∈ b.divisors.filter (fun m => m ^ 2 ∣ b),
              (rootCount d (a * b / (m₁ * m₂) ^ 2) : ℝ) =
                (rootCount d (a / m₁ ^ 2) : ℝ) * (rootCount d (b / m₂ ^ 2) : ℝ) := by
          intro m₁ hm₁ m₂ hm₂
          obtain ⟨h1d, h12⟩ := Finset.mem_filter.mp hm₁
          obtain ⟨h2d, h22⟩ := Finset.mem_filter.mp hm₂
          obtain ⟨a', ha'⟩ := h12
          obtain ⟨b', hb'⟩ := h22
          have hm1pos : 0 < m₁ ^ 2 := pow_pos (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp h1d).1 (Nat.pos_of_ne_zero ha)) 2
          have hm2pos : 0 < m₂ ^ 2 := pow_pos (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp h2d).1 (Nat.pos_of_ne_zero hb)) 2
          have ha'pos : 0 < a' := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at ha'; exact ha ha'
          have hb'pos : 0 < b' := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hb'; exact hb hb'
          have hdiv1 : a / m₁ ^ 2 = a' := by rw [ha', Nat.mul_div_cancel_left _ hm1pos]
          have hdiv2 : b / m₂ ^ 2 = b' := by rw [hb', Nat.mul_div_cancel_left _ hm2pos]
          have hdiv12 : a * b / (m₁ * m₂) ^ 2 = a' * b' := by
            rw [ha', hb', mul_pow, show m₁ ^ 2 * a' * (m₂ ^ 2 * b') = (m₁ ^ 2 * m₂ ^ 2) * (a' * b') by ring,
              Nat.mul_div_cancel_left _ (Nat.mul_pos hm1pos hm2pos)]
          have hcop' : Nat.Coprime a' b' :=
            (hcop.coprime_dvd_left ⟨m₁ ^ 2, by rw [ha', mul_comm]⟩).coprime_dvd_right ⟨m₂ ^ 2, by rw [hb', mul_comm]⟩
          rw [hdiv1, hdiv2, hdiv12, rootCount_mul d a' b' hd hcop' ha'pos hb'pos, Nat.cast_mul]
        rw [Finset.sum_congr rfl fun m₁ hm₁ => Finset.sum_congr rfl fun m₂ hm₂ => hterm m₁ hm₁ m₂ hm₂]
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  -- Compare multiplicative functions f and g on prime powers p^k!
  have hpp : ∀ p k : ℕ, p.Prime → f (p ^ k) = g (p ^ k) := by
    intro p k hp
    have hpk0 : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
    simp only [f, g, ArithmeticFunction.coe_mk, hpk0, ↓reduceIte]
    have hdiv_pk : (p ^ k).divisors = (Finset.range (k + 1)).image (p ^ ·) := by
      rw [Nat.divisors_prime_pow hp, Finset.map_eq_image]; rfl
    have hflhs : ∑ j ∈ (p ^ k).divisors, (jacobiSym (j : ℤ) d : ℝ) =
        ∑ i ∈ Finset.range (k + 1), (jacobiSym (p : ℤ) d : ℝ) ^ i := by
      rw [hdiv_pk, Finset.sum_image (fun a _ b _ h => Nat.pow_right_injective hp.two_le h)]
      refine Finset.sum_congr rfl fun i _ => by rw [Nat.cast_pow, jacobiSym.pow_left]; push_cast; rfl
    have hgrhs : ∑ m ∈ (p ^ k).divisors.filter (fun m => m ^ 2 ∣ p ^ k), (rootCount d (p ^ k / m ^ 2) : ℝ) =
        ∑ j ∈ Finset.range (k / 2 + 1), (rootCount d (p ^ (k - 2 * j)) : ℝ) := by
      have hfilt : (p ^ k).divisors.filter (fun m => m ^ 2 ∣ p ^ k) =
          (Finset.range (k / 2 + 1)).image (p ^ ·) := by
        ext m
        simp only [Finset.mem_filter, hdiv_pk, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨⟨j, hj, rfl⟩, h2⟩
          rw [← pow_mul, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h2
          exact ⟨j, by omega, rfl⟩
        · rintro ⟨j, hj, rfl⟩
          exact ⟨⟨j, by omega, rfl⟩, by rw [← pow_mul]; exact pow_dvd_pow p (by omega)⟩
      rw [hfilt, Finset.sum_image (fun a _ b _ h => Nat.pow_right_injective hp.two_le h)]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [← pow_mul, Nat.pow_div (by omega) hp.pos, mul_comm j 2]
    rw [hflhs, hgrhs]
    by_cases hp2 : p = 2
    · subst hp2
      have hj2 : jacobiSym (2 : ℤ) d = -1 := by
        rw [jacobiSym.at_two (Nat.odd_iff.mpr (by omega)), ZMod.χ₈_nat_eq_if_mod_eight]
        simp [show d % 2 = 1 by omega, hd]
      simp only [Nat.cast_ofNat, hj2]
      have hlhs_val : ∑ i ∈ Finset.range (k + 1), ((-1 : ℤ) : ℝ) ^ i = if Even k then 1 else 0 := by
        clear hdiv_pk hflhs hgrhs hpk0
        induction k with
        | zero => simp
        | succ k ih =>
          rw [Finset.sum_range_succ, ih]
          rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
          · have hev : Even (r + r) := ⟨r, rfl⟩
            have hnev : ¬ Even (r + r + 1) := by intro ⟨t, ht⟩; omega
            have hpow : (-1 : ℝ) ^ (r + r + 1) = -1 := by rw [pow_succ, show r + r = 2 * r by omega, pow_mul]; norm_num
            simp [hev, hnev, hpow]
          · have hnev : ¬ Even (2 * r + 1) := by intro ⟨t, ht⟩; omega
            have hev : Even (2 * r + 1 + 1) := ⟨r + 1, by omega⟩
            have hpow : (-1 : ℝ) ^ (2 * r + 1 + 1) = 1 := by rw [show 2 * r + 1 + 1 = 2 * (r + 1) by omega, pow_mul]; norm_num
            simp [hev, hnev, hpow]
      rw [hlhs_val]
      rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · have hev : Even (r + r) := ⟨r, rfl⟩
        rw [if_pos hev, show (r + r) / 2 = r by omega, Finset.sum_eq_single r]
        · rw [show r + r - 2 * r = 0 by omega, pow_zero, rootCount_one d (by omega)]; simp
        · intro j hj hne
          rw [Finset.mem_range] at hj
          have hpos : 0 < r + r - 2 * j := by omega
          have h2dvd : 2 ∣ 2 ^ (r + r - 2 * j) := dvd_pow_self 2 (by omega)
          rw [rootCount_even_eq_zero d _ hd h2dvd (pow_pos (by omega) _)]; simp
        · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
      · have hnev : ¬ Even (2 * r + 1) := by intro ⟨t, ht⟩; omega
        rw [if_neg hnev]
        refine (Finset.sum_eq_zero fun j hj => ?_).symm
        rw [Finset.mem_range] at hj
        have hpos : 0 < 2 * r + 1 - 2 * j := by omega
        have h2dvd : 2 ∣ 2 ^ (2 * r + 1 - 2 * j) := dvd_pow_self 2 (by omega)
        rw [rootCount_even_eq_zero d _ hd h2dvd (pow_pos (by omega) _)]; simp
    · by_cases hpd : p ∣ d
      · have hj0 : jacobiSym (p : ℤ) d = 0 := by
          have : NeZero d := ⟨by omega⟩
          rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
          intro hcop
          have := Nat.dvd_gcd (dvd_refl p) hpd
          rw [hcop] at this; exact hp.not_dvd_one this
        rw [hj0, Int.cast_zero]
        have hlhs1 : ∑ i ∈ Finset.range (k + 1), (0 : ℝ) ^ i = 1 := by
          rw [Finset.sum_eq_single 0] <;> simp (config := { contextual := true }) [zero_pow]
        rw [hlhs1]
        rw [Finset.sum_eq_single (k / 2)]
        · rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
          · rw [show (r + r) / 2 = r by omega, show r + r - 2 * r = 0 by omega, pow_zero,
              rootCount_one d (by omega)]; simp
          · rw [show (2 * r + 1) / 2 = r by omega, show 2 * r + 1 - 2 * r = 1 by omega,
              rootCount_prime_pow_dvd hd hd_sf hp hpd 1 le_rfl]; simp
        · intro j hj hne
          rw [Finset.mem_range] at hj
          have hge2 : 2 ≤ k - 2 * j := by omega
          rw [rootCount_prime_pow_dvd hd hd_sf hp hpd _ (by omega), if_neg (by omega)]; simp
        · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
      · have hne0 : jacobiSym (p : ℤ) d ≠ 0 := by
          apply jacobiSym.ne_zero
          rw [Int.gcd_natCast_natCast]; exact hp.coprime_iff_not_dvd.mpr hpd
        rcases jacobiSym.trichotomy (p : ℤ) d with h0 | h1 | hm1
        · exact absurd h0 hne0
        · rw [h1, Int.cast_one]
          simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
          · rw [show (r + r) / 2 = r by omega, Finset.sum_range_succ, show r + r - 2 * r = 0 by omega,
              pow_zero, rootCount_one d (by omega)]
            have hrest : ∑ j ∈ Finset.range r, (rootCount d (p ^ (r + r - 2 * j)) : ℝ) = 2 * (r : ℝ) := by
              have : ∀ j ∈ Finset.range r, (rootCount d (p ^ (r + r - 2 * j)) : ℝ) = 2 := by
                intro j hj; rw [Finset.mem_range] at hj
                rw [rootCount_prime_pow_not_dvd hd hp hp2 hpd _ (by omega), if_pos h1]; simp
              rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
            rw [hrest]; push_cast; ring
          · rw [show (2 * r + 1) / 2 = r by omega]
            have hall : ∀ j ∈ Finset.range (r + 1), (rootCount d (p ^ (2 * r + 1 - 2 * j)) : ℝ) = 2 := by
              intro j hj; rw [Finset.mem_range] at hj
              rw [rootCount_prime_pow_not_dvd hd hp hp2 hpd _ (by omega), if_pos h1]; simp
            rw [Finset.sum_congr rfl hall, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        · rw [hm1]
          have hlhs_val : ∑ i ∈ Finset.range (k + 1), ((-1 : ℤ) : ℝ) ^ i = if Even k then 1 else 0 := by
            clear hdiv_pk hflhs hgrhs hpk0
            induction k with
            | zero => simp
            | succ k ih =>
              rw [Finset.sum_range_succ, ih]
              rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
              · have hev : Even (r + r) := ⟨r, rfl⟩
                have hnev : ¬ Even (r + r + 1) := by intro ⟨t, ht⟩; omega
                have hpow : (-1 : ℝ) ^ (r + r + 1) = -1 := by rw [pow_succ, show r + r = 2 * r by omega, pow_mul]; norm_num
                simp [hev, hnev, hpow]
              · have hnev : ¬ Even (2 * r + 1) := by intro ⟨t, ht⟩; omega
                have hev : Even (2 * r + 1 + 1) := ⟨r + 1, by omega⟩
                have hpow : (-1 : ℝ) ^ (2 * r + 1 + 1) = 1 := by rw [show 2 * r + 1 + 1 = 2 * (r + 1) by omega, pow_mul]; norm_num
                simp [hev, hnev, hpow]
          rw [hlhs_val]
          rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
          · have hev : Even (r + r) := ⟨r, rfl⟩
            rw [if_pos hev, show (r + r) / 2 = r by omega, Finset.sum_eq_single r]
            · rw [show r + r - 2 * r = 0 by omega, pow_zero, rootCount_one d (by omega)]; simp
            · intro j hj hne
              rw [Finset.mem_range] at hj
              rw [rootCount_prime_pow_not_dvd hd hp hp2 hpd _ (by omega), if_neg (by omega)]; simp
            · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
          · have hnev : ¬ Even (2 * r + 1) := by intro ⟨t, ht⟩; omega
            rw [if_neg hnev]
            refine (Finset.sum_eq_zero fun j hj => ?_).symm
            rw [Finset.mem_range] at hj
            rw [rootCount_prime_pow_not_dvd hd hp hp2 hpd _ (by omega), if_neg (by omega)]; simp
  rw [hf_mult.multiplicative_factorization f (by omega), hg_mult.multiplicative_factorization g (by omega)]
  exact Finset.prod_congr rfl fun p hp => hpp p (n.factorization p) (Nat.prime_of_mem_primeFactors (by simpa using hp))

/-- Every root `b ∈ [0, 2n)` of `4n ∣ b² + d` injects into primitive representations of `n` by reduced forms,
hence `∑_{m² ∣ n} rootCount d (n / m²) ≤ ∑_{g ∈ reducedForms d} (repForm g n).card`. -/
lemma sum_sq_div_rootCount_le_repForm {d : ℕ} (hd : 0 < d) (n : ℕ) (hn : 1 ≤ n) :
    (∑ m ∈ n.divisors.filter (fun m => m ^ 2 ∣ n), rootCount d (n / m ^ 2)) ≤
      ∑ g ∈ reducedForms d, (repForm g n).card := by
  classical
  -- Step 1: For any n' ≥ 1, rootCount d n' ≤ ∑ g ∈ reducedForms d, #(primitive reps of n' by g)
  have hprim : ∀ n' : ℕ, 1 ≤ n' →
      rootCount d n' ≤ ∑ g ∈ reducedForms d,
        ((repForm g n').filter fun p => Int.gcd p.1 p.2 = 1).card := by
    intro n' hn'
    let roots := (Finset.range (2 * n')).filter fun b => 4 * n' ∣ b ^ 2 + d
    -- For each b ∈ roots, form f_b = ⟨n', b, (b² + d)/(4n')⟩ and reduce to g_b ∈ reducedForms d via M_b ∈ SL₂(ℤ)
    have hred : ∀ b (hb : b ∈ roots), ∃ (g : BQF d) (M : Matrix (Fin 2) (Fin 2) ℤ),
        g ∈ reducedForms d ∧ M.det = 1 ∧
        ∀ x y : ℤ, (⟨(n' : ℤ), (b : ℤ), (((b ^ 2 + d) / (4 * n') : ℕ) : ℤ),
          by exact_mod_cast hn',
          by
            have h4n := (Finset.mem_filter.mp hb).2
            have hpos : 0 < (b ^ 2 + d) / (4 * n') := Nat.div_pos (Nat.le_of_dvd (by omega) h4n) (by omega)
            exact_mod_cast hpos,
          by
            have h4n := (Finset.mem_filter.mp hb).2
            have hmul : 4 * n' * ((b ^ 2 + d) / (4 * n')) = b ^ 2 + d := Nat.mul_div_cancel' h4n
            have hZ : (4 * (n' : ℤ)) * (((b ^ 2 + d) / (4 * n') : ℕ) : ℤ) = (b : ℤ) ^ 2 + (d : ℤ) := by
              exact_mod_cast hmul
            linarith⟩ : BQF d).eval (M 0 0 * x + M 0 1 * y) (M 1 0 * x + M 1 1 * y) = g.eval x y := by
      intro b hb
      have h4n := (Finset.mem_filter.mp hb).2
      let fb : BQF d := ⟨(n' : ℤ), (b : ℤ), (((b ^ 2 + d) / (4 * n') : ℕ) : ℤ),
        by exact_mod_cast hn',
        by
          have hpos : 0 < (b ^ 2 + d) / (4 * n') := Nat.div_pos (Nat.le_of_dvd (by omega) h4n) (by omega)
          exact_mod_cast hpos,
        by
          have hmul : 4 * n' * ((b ^ 2 + d) / (4 * n')) = b ^ 2 + d := Nat.mul_div_cancel' h4n
          have hZ : (4 * (n' : ℤ)) * (((b ^ 2 + d) / (4 * n') : ℕ) : ℤ) = (b : ℤ) ^ 2 + (d : ℤ) := by
            exact_mod_cast hmul
          linarith⟩
      obtain ⟨g, hgr, hstep⟩ := exists_reduced_stepEquiv hd fb
      obtain ⟨M, hMdet, hMe⟩ := hstep.toSL2
      exact ⟨g, M, (mem_reducedForms_iff hd g).mpr hgr, hMdet, hMe⟩
    choose g_b M_b hg_mem hM_det hM_eq using hred
    -- Map b ∈ roots to ⟨g_b b, (M_b⁻¹) * (1, 0)⟩ = ⟨g_b b, (M 1 1, -M 1 0)⟩
    let Φ : (b : {x // x ∈ roots}) → (g : BQF d) × (ℤ × ℤ) := fun b =>
      ⟨g_b b.1 b.2, (M_b b.1 b.2 1 1, -(M_b b.1 b.2 1 0))⟩
    let Target := (reducedForms d).sigma fun g => (repForm g n').filter fun p => Int.gcd p.1 p.2 = 1
    have hTarget_card : Target.card = ∑ g ∈ reducedForms d, ((repForm g n').filter fun p => Int.gcd p.1 p.2 = 1).card :=
      Finset.card_sigma _ _
    rw [← hTarget_card, rootCount]
    calc roots.card = roots.attach.card := (Finset.card_attach).symm
      _ ≤ Target.card := by
        refine Finset.card_le_card_of_injOn Φ ?_ ?_
        · intro b _
          rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter]
          refine ⟨hg_mem b.1 b.2, ?_, ?_⟩
          · rw [mem_repForm_iff hd ((mem_reducedForms_iff hd _).mp (hg_mem b.1 b.2))]
            have h1 := hM_eq b.1 b.2 (M_b b.1 b.2 1 1) (-(M_b b.1 b.2 1 0))
            have hdet := hM_det b.1 b.2
            rw [Matrix.det_fin_two] at hdet
            have hx : M_b b.1 b.2 0 0 * M_b b.1 b.2 1 1 + M_b b.1 b.2 0 1 * -(M_b b.1 b.2 1 0) = 1 := by linarith
            have hy : M_b b.1 b.2 1 0 * M_b b.1 b.2 1 1 + M_b b.1 b.2 1 1 * -(M_b b.1 b.2 1 0) = 0 := by ring
            rw [hx, hy] at h1
            simp only [eval, mul_one, mul_zero, add_zero, one_pow, zero_pow two_ne_zero] at h1
            exact h1.symm
          · have hdet := hM_det b.1 b.2
            rw [Matrix.det_fin_two] at hdet
            have hcop : IsCoprime (M_b b.1 b.2 1 1) (-(M_b b.1 b.2 1 0)) :=
              ⟨M_b b.1 b.2 0 0, M_b b.1 b.2 0 1, by linarith⟩
            exact Int.isCoprime_iff_gcd_eq_one.mp hcop
        · intro b₁ _ b₂ _ heq
          dsimp only [Φ] at heq
          have hg_eq : g_b b₁.1 b₁.2 = g_b b₂.1 b₂.2 := congrArg Sigma.fst heq
          have hp_eq : (M_b b₁.1 b₁.2 1 1, -(M_b b₁.1 b₁.2 1 0)) = (M_b b₂.1 b₂.2 1 1, -(M_b b₂.1 b₂.2 1 0)) :=
            congrArg Sigma.snd heq
          have h11 : M_b b₁.1 b₁.2 1 1 = M_b b₂.1 b₂.2 1 1 := congrArg Prod.fst hp_eq
          have h10 : M_b b₁.1 b₁.2 1 0 = M_b b₂.1 b₂.2 1 0 := by
            have := congrArg Prod.snd hp_eq; dsimp only at this; omega
          -- Compute K = M₁ * M₂⁻¹: row 1 of K is (0, 1) and det K = 1, so K = [[1, k], [0, 1]]!
          set M₁ := M_b b₁.1 b₁.2
          set M₂ := M_b b₂.1 b₂.2
          have hd₁ := hM_det b₁.1 b₁.2
          have hd₂ := hM_det b₂.1 b₂.2
          rw [Matrix.det_fin_two] at hd₁ hd₂
          set k : ℤ := -(M₁ 0 0 * M₂ 0 1) + M₁ 0 1 * M₂ 0 0
          -- For all u, v: fb₁(u + k*v, v) = fb₂(u, v) via (x, y) = M₂⁻¹ (u, v)
          have hfb_eq : ∀ u v : ℤ,
              ((n' : ℤ) * (u + k * v) ^ 2 + (b₁.1 : ℤ) * (u + k * v) * v + (((b₁.1 ^ 2 + d) / (4 * n') : ℕ) : ℤ) * v ^ 2) =
              ((n' : ℤ) * u ^ 2 + (b₂.1 : ℤ) * u * v + (((b₂.1 ^ 2 + d) / (4 * n') : ℕ) : ℤ) * v ^ 2) := by
            intro u v
            set x : ℤ := M₂ 1 1 * u - M₂ 0 1 * v
            set y : ℤ := -(M₂ 1 0) * u + M₂ 0 0 * v
            have h1 := hM_eq b₁.1 b₁.2 x y
            have h2 := hM_eq b₂.1 b₂.2 x y
            rw [hg_eq] at h1
            have h12 : _ = _ := h1.trans h2.symm
            have hx2 : M₂ 0 0 * x + M₂ 0 1 * y = u := by dsimp only [x, y]; linear_combination u * hd₂
            have hy2 : M₂ 1 0 * x + M₂ 1 1 * y = v := by dsimp only [x, y]; linear_combination v * hd₂
            have hx1 : M₁ 0 0 * x + M₁ 0 1 * y = u + k * v := by
              dsimp only [x, y, k]; rw [← h11, ← h10]; linear_combination u * hd₁
            have hy1 : M₁ 1 0 * x + M₁ 1 1 * y = v := by
              dsimp only [x, y]; rw [h10, h11]; linear_combination v * hd₂
            dsimp only [eval] at h12
            rw [hx1, hy1, hx2, hy2] at h12
            exact h12
          -- Compare coefficient of u*v using (u, v) = (1, 1) and (-1, 1)
          have h11' := hfb_eq 1 1
          have hm11' := hfb_eq (-1) 1
          have hb_diff : (b₂.1 : ℤ) = (b₁.1 : ℤ) + 2 * (n' : ℤ) * k := by linarith
          have hr₁ := Finset.mem_range.mp (Finset.mem_filter.mp b₁.2).1
          have hr₂ := Finset.mem_range.mp (Finset.mem_filter.mp b₂.2).1
          have hk0 : k = 0 := by nlinarith
          have hb_eq : b₁.1 = b₂.1 := by
            rw [hk0] at hb_diff; omega
          exact Subtype.ext hb_eq
  -- Step 2: Sum over square divisors m² ∣ n; scaling primitive reps of n/m² by m gives disjoint reps of n!
  have hdisj_sum : ∀ g ∈ reducedForms d,
      ∑ m ∈ n.divisors.filter (fun m => m ^ 2 ∣ n),
        ((repForm g (n / m ^ 2)).filter fun p => Int.gcd p.1 p.2 = 1).card ≤ (repForm g n).card := by
    intro g hg
    let Dom := (n.divisors.filter fun m => m ^ 2 ∣ n).sigma fun m =>
      (repForm g (n / m ^ 2)).filter fun p => Int.gcd p.1 p.2 = 1
    rw [← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn (fun t => ((t.1 : ℤ) * t.2.1, (t.1 : ℤ) * t.2.2)) ?_ ?_
    · intro t ht
      rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter] at ht
      obtain ⟨⟨hmd, hm2⟩, hrep, _⟩ := ht
      rw [Finset.mem_coe, mem_repForm_iff hd ((mem_reducedForms_iff hd g).mp hg)]
      have hev := (mem_repForm_iff hd ((mem_reducedForms_iff hd g).mp hg) _ _).mp hrep
      have hmul : (t.1 : ℤ) ^ 2 * ((n / t.1 ^ 2 : ℕ) : ℤ) = (n : ℤ) := by
        exact_mod_cast Nat.mul_div_cancel' hm2
      dsimp only [eval] at hev ⊢
      linear_combination (t.1 : ℤ) ^ 2 * hev + hmul
    · intro t₁ ht₁ t₂ ht₂ heq
      rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Finset.mem_filter] at ht₁ ht₂
      have hm1pos : 0 < t₁.1 := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ht₁.1.1).1 (by omega)
      have hm2pos : 0 < t₂.1 := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ht₂.1.1).1 (by omega)
      have hx : (t₁.1 : ℤ) * t₁.2.1 = (t₂.1 : ℤ) * t₂.2.1 := congrArg Prod.fst heq
      have hy : (t₁.1 : ℤ) * t₁.2.2 = (t₂.1 : ℤ) * t₂.2.2 := congrArg Prod.snd heq
      have hgcd1 : Int.gcd ((t₁.1 : ℤ) * t₁.2.1) ((t₁.1 : ℤ) * t₁.2.2) = t₁.1 := by
        rw [Int.gcd_mul_left, ht₁.2.2, mul_one]; exact Int.natAbs_natCast t₁.1
      have hgcd2 : Int.gcd ((t₂.1 : ℤ) * t₂.2.1) ((t₂.1 : ℤ) * t₂.2.2) = t₂.1 := by
        rw [Int.gcd_mul_left, ht₂.2.2, mul_one]; exact Int.natAbs_natCast t₂.1
      have hm_eq : t₁.1 = t₂.1 := by rw [← hgcd1, hx, hy, hgcd2]
      rcases t₁ with ⟨m₁, x₁, y₁⟩; rcases t₂ with ⟨m₂, x₂, y₂⟩
      dsimp only at hm_eq hx hy hm1pos; subst hm_eq
      have hmne : (m₁ : ℤ) ≠ 0 := by exact_mod_cast hm1pos.ne'
      have hx' : x₁ = x₂ := mul_left_cancel₀ hmne hx
      have hy' : y₁ = y₂ := mul_left_cancel₀ hmne hy
      subst hx' hy'; rfl
  calc ∑ m ∈ n.divisors.filter (fun m => m ^ 2 ∣ n), rootCount d (n / m ^ 2)
      ≤ ∑ m ∈ n.divisors.filter (fun m => m ^ 2 ∣ n),
          ∑ g ∈ reducedForms d, ((repForm g (n / m ^ 2)).filter fun p => Int.gcd p.1 p.2 = 1).card := by
        refine Finset.sum_le_sum fun m hm => hprim (n / m ^ 2) ?_
        have ⟨hmd, hm2⟩ := Finset.mem_filter.mp hm
        have hmpos : 0 < m ^ 2 := pow_pos (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hmd).1 (by omega)) 2
        exact Nat.div_pos (Nat.le_of_dvd (by omega) hm2) hmpos
    _ = ∑ g ∈ reducedForms d, ∑ m ∈ n.divisors.filter (fun m => m ^ 2 ∣ n),
          ((repForm g (n / m ^ 2)).filter fun p => Int.gcd p.1 p.2 = 1).card := Finset.sum_comm
    _ ≤ ∑ g ∈ reducedForms d, (repForm g n).card := Finset.sum_le_sum hdisj_sum

/-- Elementary upper bound on lattice points in an ellipse `a x² + b x y + c y² ≤ X`. -/
lemma sum_repForm_le_ellipse {d : ℕ} (hd : 0 < d) {f : BQF d} (hf : f.isReduced) (X : ℕ) (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Icc 1 X, ((repForm f n).card : ℝ)) ≤
      (8 / Real.sqrt (d : ℝ)) * (X : ℝ) +
      (2 * Real.sqrt (4 * (f.a : ℝ) / (d : ℝ)) + 2 / Real.sqrt (f.a : ℝ)) * Real.sqrt (X : ℝ) + 1 := by
  have hfa_pos : (0 : ℝ) < (f.a : ℝ) := by exact_mod_cast f.ha
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  set Y : ℕ := Nat.floor (Real.sqrt (4 * (f.a : ℝ) * (X : ℝ) / (d : ℝ)))
  set S_y : Finset ℤ := Finset.Icc (-(Y : ℤ)) (Y : ℤ)
  -- For each y ∈ S_y, x lies in an interval of length ≤ 2 * √(X / a)
  let xLo (y : ℤ) : ℤ := Int.ceil ((-(f.b : ℝ) * (y : ℝ) - Real.sqrt (4 * (f.a : ℝ) * (X : ℝ))) / (2 * (f.a : ℝ)))
  let xHi (y : ℤ) : ℤ := Int.floor ((-(f.b : ℝ) * (y : ℝ) + Real.sqrt (4 * (f.a : ℝ) * (X : ℝ))) / (2 * (f.a : ℝ)))
  let Box : Finset (ℤ × ℤ) := S_y.biUnion fun y => (Finset.Icc (xLo y) (xHi y)).image fun x => (x, y)
  have hcard_le : (∑ n ∈ Finset.Icc 1 X, (repForm f n).card) ≤ Box.card := by
    let All := (Finset.Icc 1 X).biUnion fun n => repForm f n
    have hdisj : Set.PairwiseDisjoint (Finset.Icc 1 X : Set ℕ) (fun n => repForm f n) := by
      intro n₁ _ n₂ _ hne
      change Disjoint (repForm f n₁) (repForm f n₂)
      rw [Finset.disjoint_left]
      intro p hp₁ hp₂
      have h1 := (mem_repForm_iff hd hf n₁ p).mp hp₁
      have h2 := (mem_repForm_iff hd hf n₂ p).mp hp₂
      exact hne (by exact_mod_cast h1.symm.trans h2)
    rw [← Finset.card_biUnion hdisj]
    refine Finset.card_le_card fun p hp => ?_
    rw [Finset.mem_biUnion] at hp
    obtain ⟨n, hn, hp_rep⟩ := hp
    have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
    have hev : f.eval p.1 p.2 = (n : ℤ) := (mem_repForm_iff hd hf n p).mp hp_rep
    have h4R : (2 * (f.a : ℝ) * (p.1 : ℝ) + (f.b : ℝ) * (p.2 : ℝ)) ^ 2 + (d : ℝ) * (p.2 : ℝ) ^ 2 ≤
        4 * (f.a : ℝ) * (X : ℝ) := by
      have h4Z : (2 * f.a * p.1 + f.b * p.2) ^ 2 + (d : ℤ) * p.2 ^ 2 = 4 * f.a * (n : ℤ) := by
        rw [← hev]; dsimp only [eval]; linear_combination -(p.2 ^ 2 * f.hdisc)
      have h4R' : (2 * (f.a : ℝ) * (p.1 : ℝ) + (f.b : ℝ) * (p.2 : ℝ)) ^ 2 + (d : ℝ) * (p.2 : ℝ) ^ 2 =
          4 * (f.a : ℝ) * (n : ℝ) := by exact_mod_cast h4Z
      have hnXR : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast hnX
      nlinarith
    have hy_mem : p.2 ∈ S_y := by
      have hysq : (p.2 : ℝ) ^ 2 ≤ 4 * (f.a : ℝ) * (X : ℝ) / (d : ℝ) := by
        rw [le_div_iff₀ hd_pos]; nlinarith [sq_nonneg (2 * (f.a : ℝ) * (p.1 : ℝ) + (f.b : ℝ) * (p.2 : ℝ))]
      have hyabs : |(p.2 : ℝ)| ≤ Real.sqrt (4 * (f.a : ℝ) * (X : ℝ) / (d : ℝ)) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hysq
      have hyNat : p.2.natAbs ≤ Y := by
        refine Nat.le_floor ?_
        have : (p.2.natAbs : ℝ) = |(p.2 : ℝ)| := by rw [← Int.cast_abs, Int.abs_eq_natAbs]; rfl
        rwa [this]
      rw [Finset.mem_Icc]; omega
    have hx_mem : p.1 ∈ Finset.Icc (xLo p.2) (xHi p.2) := by
      have hsq : (2 * (f.a : ℝ) * (p.1 : ℝ) + (f.b : ℝ) * (p.2 : ℝ)) ^ 2 ≤ 4 * (f.a : ℝ) * (X : ℝ) := by
        nlinarith [sq_nonneg (p.2 : ℝ)]
      have habs : |2 * (f.a : ℝ) * (p.1 : ℝ) + (f.b : ℝ) * (p.2 : ℝ)| ≤ Real.sqrt (4 * (f.a : ℝ) * (X : ℝ)) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hsq
      have ⟨hl, hu⟩ := abs_le.mp habs
      rw [Finset.mem_Icc]
      refine ⟨Int.ceil_le.mpr ?_, Int.le_floor.mpr ?_⟩
      · rw [div_le_iff₀ (by positivity)]; linarith
      · rw [le_div_iff₀ (by positivity)]; linarith
    rw [Finset.mem_biUnion]
    exact ⟨p.2, hy_mem, Finset.mem_image.mpr ⟨p.1, hx_mem, by cases p; rfl⟩⟩
  have hBox_card : (Box.card : ℝ) ≤
      (2 * Real.sqrt (4 * (f.a : ℝ) * (X : ℝ) / (d : ℝ)) + 1) *
      (2 * Real.sqrt ((X : ℝ) / (f.a : ℝ)) + 1) := by
    have hstep1 : Box.card ≤ ∑ y ∈ S_y, (Finset.Icc (xLo y) (xHi y)).card := by
      calc Box.card ≤ ∑ y ∈ S_y, ((Finset.Icc (xLo y) (xHi y)).image fun x => (x, y)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ y ∈ S_y, (Finset.Icc (xLo y) (xHi y)).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
    have hrow : ∀ y : ℤ, ((Finset.Icc (xLo y) (xHi y)).card : ℝ) ≤ 2 * Real.sqrt ((X : ℝ) / (f.a : ℝ)) + 1 := by
      intro y
      by_cases hle : xLo y ≤ xHi y
      · have hcard : ((Finset.Icc (xLo y) (xHi y)).card : ℝ) = (xHi y : ℝ) - (xLo y : ℝ) + 1 := by
          rw [Int.card_Icc]; have : 0 ≤ xHi y + 1 - xLo y := by omega
          have h1 : ((xHi y + 1 - xLo y).toNat : ℤ) = xHi y + 1 - xLo y := Int.toNat_of_nonneg this
          have h2 : (((xHi y + 1 - xLo y).toNat : ℕ) : ℝ) = (xHi y : ℝ) + 1 - (xLo y : ℝ) := by
            exact_mod_cast h1
          linarith
        rw [hcard]
        have hlo : (-(f.b : ℝ) * (y : ℝ) - Real.sqrt (4 * (f.a : ℝ) * (X : ℝ))) / (2 * (f.a : ℝ)) ≤ (xLo y : ℝ) :=
          Int.le_ceil _
        have hhi : (xHi y : ℝ) ≤ (-(f.b : ℝ) * (y : ℝ) + Real.sqrt (4 * (f.a : ℝ) * (X : ℝ))) / (2 * (f.a : ℝ)) :=
          Int.floor_le _
        have hdiff : (xHi y : ℝ) - (xLo y : ℝ) ≤ Real.sqrt (4 * (f.a : ℝ) * (X : ℝ)) / (f.a : ℝ) := by
          have : (-(f.b : ℝ) * (y : ℝ) + Real.sqrt (4 * (f.a : ℝ) * (X : ℝ))) / (2 * (f.a : ℝ)) -
              (-(f.b : ℝ) * (y : ℝ) - Real.sqrt (4 * (f.a : ℝ) * (X : ℝ))) / (2 * (f.a : ℝ)) =
              Real.sqrt (4 * (f.a : ℝ) * (X : ℝ)) / (f.a : ℝ) := by field_simp; ring
          linarith
        have hsq : Real.sqrt (4 * (f.a : ℝ) * (X : ℝ)) / (f.a : ℝ) = 2 * Real.sqrt ((X : ℝ) / (f.a : ℝ)) := by
          have h1 : Real.sqrt (4 * (f.a : ℝ) * (X : ℝ)) = 2 * Real.sqrt (f.a : ℝ) * Real.sqrt (X : ℝ) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num]
          rw [h1, Real.sqrt_div hX_pos.le]
          have hsqa : Real.sqrt (f.a : ℝ) * Real.sqrt (f.a : ℝ) = (f.a : ℝ) := Real.mul_self_sqrt hfa_pos.le
          have hsqapos : 0 < Real.sqrt (f.a : ℝ) := Real.sqrt_pos.mpr hfa_pos
          rw [← hsqa]; field_simp; rw [Real.sq_sqrt (sq_nonneg _)]
        linarith
      · have hemp : Finset.Icc (xLo y) (xHi y) = ∅ := by
          ext x; simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
        rw [hemp, Finset.card_empty, Nat.cast_zero]; positivity
    have hSy_card : (S_y.card : ℝ) ≤ 2 * Real.sqrt (4 * (f.a : ℝ) * (X : ℝ) / (d : ℝ)) + 1 := by
      have hc : S_y.card = 2 * Y + 1 := by
        dsimp only [S_y]; rw [Int.card_Icc]; omega
      rw [hc]; push_cast
      have hYle : (Y : ℝ) ≤ Real.sqrt (4 * (f.a : ℝ) * (X : ℝ) / (d : ℝ)) := Nat.floor_le (by positivity)
      linarith
    calc (Box.card : ℝ) ≤ ∑ y ∈ S_y, ((Finset.Icc (xLo y) (xHi y)).card : ℝ) := by exact_mod_cast hstep1
      _ ≤ ∑ _y ∈ S_y, (2 * Real.sqrt ((X : ℝ) / (f.a : ℝ)) + 1) := Finset.sum_le_sum fun y _ => hrow y
      _ = (S_y.card : ℝ) * (2 * Real.sqrt ((X : ℝ) / (f.a : ℝ)) + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * Real.sqrt (4 * (f.a : ℝ) * (X : ℝ) / (d : ℝ)) + 1) * (2 * Real.sqrt ((X : ℝ) / (f.a : ℝ)) + 1) :=
          mul_le_mul_of_nonneg_right hSy_card (by positivity)
  have hprod_eq : (2 * Real.sqrt (4 * (f.a : ℝ) * (X : ℝ) / (d : ℝ)) + 1) *
      (2 * Real.sqrt ((X : ℝ) / (f.a : ℝ)) + 1) =
      (8 / Real.sqrt (d : ℝ)) * (X : ℝ) +
      (2 * Real.sqrt (4 * (f.a : ℝ) / (d : ℝ)) + 2 / Real.sqrt (f.a : ℝ)) * Real.sqrt (X : ℝ) + 1 := by
    have h1 : Real.sqrt (4 * (f.a : ℝ) * (X : ℝ) / (d : ℝ)) =
        Real.sqrt (4 * (f.a : ℝ) / (d : ℝ)) * Real.sqrt (X : ℝ) := by
      rw [show 4 * (f.a : ℝ) * (X : ℝ) / (d : ℝ) = (4 * (f.a : ℝ) / (d : ℝ)) * (X : ℝ) by ring,
        Real.sqrt_mul (by positivity)]
    have h2 : Real.sqrt ((X : ℝ) / (f.a : ℝ)) = Real.sqrt (X : ℝ) / Real.sqrt (f.a : ℝ) :=
      Real.sqrt_div hX_pos.le _
    have h3 : Real.sqrt (4 * (f.a : ℝ) / (d : ℝ)) / Real.sqrt (f.a : ℝ) = 2 / Real.sqrt (d : ℝ) := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num]
      have hsqa : Real.sqrt (f.a : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hfa_pos).ne'
      field_simp
    have h4 : Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) = (X : ℝ) := Real.mul_self_sqrt hX_pos.le
    rw [h1, h2]
    have hcross : 2 * (Real.sqrt (4 * (f.a : ℝ) / (d : ℝ)) * Real.sqrt (X : ℝ)) *
        (2 * (Real.sqrt (X : ℝ) / Real.sqrt (f.a : ℝ))) = (8 / Real.sqrt (d : ℝ)) * (X : ℝ) := by
      calc _ = 4 * (Real.sqrt (4 * (f.a : ℝ) / (d : ℝ)) / Real.sqrt (f.a : ℝ)) * (Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ)) := by ring
        _ = 4 * (2 / Real.sqrt (d : ℝ)) * (X : ℝ) := by rw [h3, h4]
        _ = (8 / Real.sqrt (d : ℝ)) * (X : ℝ) := by ring
    linarith [show (2 * (Real.sqrt (4 * (f.a : ℝ) / (d : ℝ)) * Real.sqrt (X : ℝ)) + 1) *
        (2 * (Real.sqrt (X : ℝ) / Real.sqrt (f.a : ℝ)) + 1) =
        2 * (Real.sqrt (4 * (f.a : ℝ) / (d : ℝ)) * Real.sqrt (X : ℝ)) * (2 * (Real.sqrt (X : ℝ) / Real.sqrt (f.a : ℝ))) +
        (2 * Real.sqrt (4 * (f.a : ℝ) / (d : ℝ)) + 2 / Real.sqrt (f.a : ℝ)) * Real.sqrt (X : ℝ) + 1 by ring]
  have hcast : (∑ n ∈ Finset.Icc 1 X, ((repForm f n).card : ℝ)) ≤ (Box.card : ℝ) := by
    exact_mod_cast hcard_le
  linarith

/-- Elementary Dirichlet Class Number Lower Bound:
`(√d / 8) * L(1, jacobiChar d) ≤ (reducedForms d).card` for squarefree `d ≡ 3 (mod 8)`. -/
theorem class_number_lower_bound {d : ℕ} [NeZero d] (hd_gt : 1 < d)
    (hd_sf : Squarefree d) (hd_mod : d % 8 = 3) :
    (Real.sqrt (d : ℝ) / 8) * (DirichletCharacter.LFunction (E940.Siegel.jacobiChar d hd_gt) 1).re ≤
      ((reducedForms d).card : ℝ) := by
  have hd_pos : 0 < d := by omega
  have hd_odd : Odd d := ⟨d / 2, by omega⟩
  let χ := E940.Siegel.jacobiChar d hd_gt
  have hχne : χ ≠ 1 := E940.Siegel.jacobiChar_ne_one hd_sf hd_odd hd_gt
  have hχ2 : χ ^ 2 = 1 := E940.Siegel.jacobiChar_sq_eq_one d hd_gt
  have hlim := E940.Siegel.tendsto_conv_one_char χ hχne hχ2
  -- Define C_err = ∑_{f ∈ reducedForms d} (2*√(4a/d) + 2/√a)
  let C_err : ℝ := ∑ f ∈ reducedForms d, (2 * Real.sqrt (4 * (f.a : ℝ) / (d : ℝ)) + 2 / Real.sqrt (f.a : ℝ))
  let R : ℝ := ((reducedForms d).card : ℝ)
  have hupper : ∀ X : ℕ, 1 ≤ X →
      (∑ n ∈ Finset.Icc 1 X, ∑ k ∈ n.divisors, (χ k).re) / (X : ℝ) ≤
        (8 / Real.sqrt (d : ℝ)) * R + C_err / Real.sqrt (X : ℝ) + R / (X : ℝ) := by
    intro X hX
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    have hnum : (∑ n ∈ Finset.Icc 1 X, ∑ k ∈ n.divisors, (χ k).re) ≤
        (8 / Real.sqrt (d : ℝ)) * R * (X : ℝ) + C_err * Real.sqrt (X : ℝ) + R := by
      have h1 : (∑ n ∈ Finset.Icc 1 X, ∑ k ∈ n.divisors, (χ k).re) =
          ∑ n ∈ Finset.Icc 1 X, ∑ m ∈ n.divisors.filter (fun m => m ^ 2 ∣ n), (rootCount d (n / m ^ 2) : ℝ) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        rw [← conv_eq_sum_sq_div_rootCount hd_sf hd_mod n hn1]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [χ, E940.Siegel.jacobiChar_apply_nat]
      have h2 : (∑ n ∈ Finset.Icc 1 X, ∑ m ∈ n.divisors.filter (fun m => m ^ 2 ∣ n), (rootCount d (n / m ^ 2) : ℝ)) ≤
          ∑ f ∈ reducedForms d, ∑ n ∈ Finset.Icc 1 X, ((repForm f n).card : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun n hn => ?_
        exact_mod_cast sum_sq_div_rootCount_le_repForm hd_pos n (Finset.mem_Icc.mp hn).1
      have h3 : (∑ f ∈ reducedForms d, ∑ n ∈ Finset.Icc 1 X, ((repForm f n).card : ℝ)) ≤
          ∑ f ∈ reducedForms d, ((8 / Real.sqrt (d : ℝ)) * (X : ℝ) +
            (2 * Real.sqrt (4 * (f.a : ℝ) / (d : ℝ)) + 2 / Real.sqrt (f.a : ℝ)) * Real.sqrt (X : ℝ) + 1) :=
        Finset.sum_le_sum fun f hf => sum_repForm_le_ellipse hd_pos ((mem_reducedForms_iff hd_pos f).mp hf) X hX
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.sum_mul] at h3
      dsimp only [R, C_err]
      linarith
    have hmul_sq : C_err / Real.sqrt (X : ℝ) * (X : ℝ) = C_err * Real.sqrt (X : ℝ) := by
      have hsqpos : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hXpos
      rw [div_mul_eq_mul_div, div_eq_iff hsqpos.ne', mul_assoc, Real.mul_self_sqrt hXpos.le]
    rw [div_le_iff₀ hXpos]
    calc _ ≤ (8 / Real.sqrt (d : ℝ)) * R * (X : ℝ) + C_err * Real.sqrt (X : ℝ) + R := hnum
      _ = ((8 / Real.sqrt (d : ℝ)) * R + C_err / Real.sqrt (X : ℝ) + R / (X : ℝ)) * (X : ℝ) := by
        rw [add_mul, add_mul, div_mul_cancel₀ _ hXpos.ne', hmul_sq]
  -- Pass to limit as X → ∞
  have hlim_rhs : Tendsto (fun X : ℕ => (8 / Real.sqrt (d : ℝ)) * R + C_err / Real.sqrt (X : ℝ) + R / (X : ℝ))
      atTop (𝓝 ((8 / Real.sqrt (d : ℝ)) * R + 0 + 0)) := by
    refine (tendsto_const_nhds.add ?_).add ?_
    · simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul C_err
    · simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul R
  rw [add_zero, add_zero] at hlim_rhs
  have hle : (DirichletCharacter.LFunction χ 1).re ≤ (8 / Real.sqrt (d : ℝ)) * R :=
    le_of_tendsto_of_tendsto hlim hlim_rhs (by filter_upwards [Filter.eventually_ge_atTop 1] with X hX; exact hupper X hX)
  have hsqd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd_pos)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 8)]
  have h1 := mul_le_mul_of_nonneg_left hle hsqd.le
  have hcancel : Real.sqrt (d : ℝ) * (8 / Real.sqrt (d : ℝ) * R) = 8 * R := by field_simp
  linarith

end BQF

end E940.ClassNumber

end ModClassNumber

section ModGenus

open Finset BigOperators Matrix Module
open scoped nonZeroDivisors
open E940.ClassNumber E940.ClassNumber.BQF E940.QuaternionLift
open E940.QuaternionLift.HQ (rep3Z mem_rep3Z_iff)

namespace E940.Genus

/-!
### Section 1: Imaginary Quadratic Field `K d = ℚ(√(-d))` and Ring of Integers `𝓞 (K d)`
-/

abbrev QuadK (d : ℕ) : Type := QuadraticAlgebra ℚ (-(d : ℚ)) 0

lemma quadK_fact {d : ℕ} (hd : 0 < d) : Fact (∀ r : ℚ, r ^ 2 ≠ -(d : ℚ) + 0 * r) := by
  refine ⟨fun r hr => ?_⟩
  have h1 : (0 : ℚ) ≤ r ^ 2 := sq_nonneg r
  have h2 : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  linarith

noncomputable def quadKBasis (d : ℕ) : Basis (Fin 2) ℚ (QuadK d) :=
  Basis.mk (v := ![(1 : QuadK d), ⟨0, 1⟩])
    (by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      have hre : a * 1 + b * 0 = 0 := congrArg QuadraticAlgebra.re hab
      have him : a * 0 + b * 1 = 0 := congrArg QuadraticAlgebra.im hab
      exact ⟨by linarith, by linarith⟩)
    (by
      rintro z -
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨![z.re, z.im], ?_⟩
      rw [Fin.sum_univ_two]
      ext
      · change z.re * 1 + z.im * 0 = z.re; ring
      · change z.re * 0 + z.im * 1 = z.im; ring)

lemma quadK_finrank (d : ℕ) : Module.finrank ℚ (QuadK d) = 2 := by
  rw [Module.finrank_eq_card_basis (quadKBasis d), Fintype.card_fin]

lemma quadK_numberField {d : ℕ} [Fact (∀ r : ℚ, r ^ 2 ≠ -(d : ℚ) + 0 * r)] :
    NumberField (QuadK d) := by
  haveI : FiniteDimensional ℚ (QuadK d) := Module.Finite.of_basis (quadKBasis d)
  haveI : CharZero (QuadK d) := ⟨fun m n h => by
    have hre := congrArg QuadraticAlgebra.re h
    simp only [QuadraticAlgebra.re_natCast] at hre
    exact_mod_cast hre⟩
  exact ⟨⟩

noncomputable def alphaK (d : ℕ) : QuadK d := ⟨0, 1⟩

lemma alphaK_sq (d : ℕ) : alphaK d ^ 2 = -(d : QuadK d) := by
  ext <;> simp [alphaK, sq]

noncomputable def omegaK (d : ℕ) : QuadK d := ⟨1 / 2, 1 / 2⟩

lemma omegaK_sq {d : ℕ} (hd_mod : d % 8 = 3) :
    omegaK d ^ 2 = omegaK d - (((d + 1) / 4 : ℕ) : QuadK d) := by
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have h4q : (4 : ℚ) * (((d + 1) / 4 : ℕ) : ℚ) = (d : ℚ) + 1 := by exact_mod_cast h4
  ext
  · simp only [omegaK, sq, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_sub,
      QuadraticAlgebra.re_natCast]
    linarith
  · simp only [omegaK, sq, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_sub,
      QuadraticAlgebra.im_natCast]
    ring

lemma omegaK_isIntegral {d : ℕ} (hd_mod : d % 8 = 3) : IsIntegral ℤ (omegaK d) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((d + 1) / 4 : ℕ) : ℤ), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C]
  rw [omegaK_sq hd_mod]
  simp only [eq_intCast, Int.cast_natCast]
  ring

lemma leftMulMatrix_quadK (d : ℕ) [Fact (∀ r : ℚ, r ^ 2 ≠ -(d : ℚ) + 0 * r)] (a b : ℚ) :
    Algebra.leftMulMatrix (quadKBasis d) (⟨a, b⟩ : QuadK d) = !![a, -(d : ℚ) * b; b, a] := by
  have hb0 : quadKBasis d 0 = 1 := by simp [quadKBasis]
  have hb1 : quadKBasis d 1 = ⟨0, 1⟩ := by simp [quadKBasis]
  have hrepr : ∀ z : QuadK d, (quadKBasis d).repr z 0 = z.re ∧ (quadKBasis d).repr z 1 = z.im := by
    intro z
    have hsum := (quadKBasis d).sum_repr z
    rw [Fin.sum_univ_two, hb0, hb1] at hsum
    have hre : (quadKBasis d).repr z 0 * 1 + (quadKBasis d).repr z 1 * 0 = z.re :=
      congrArg QuadraticAlgebra.re hsum
    have him : (quadKBasis d).repr z 0 * 0 + (quadKBasis d).repr z 1 * 1 = z.im :=
      congrArg QuadraticAlgebra.im hsum
    exact ⟨by linarith, by linarith⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, (hrepr _).1, (hrepr _).2]

lemma norm_quadK (d : ℕ) [Fact (∀ r : ℚ, r ^ 2 ≠ -(d : ℚ) + 0 * r)] (z : QuadK d) :
    Algebra.norm ℚ z = z.re ^ 2 + (d : ℚ) * z.im ^ 2 := by
  have hz : z = ⟨z.re, z.im⟩ := by ext <;> rfl
  rw [hz, Algebra.norm_eq_matrix_det (quadKBasis d), leftMulMatrix_quadK,
    Matrix.det_fin_two_of]
  ring

lemma exists_int_add_int_mul_omegaK_of_isIntegral {d : ℕ} (hd_sf : Squarefree d)
    (hd_mod : d % 8 = 3) {z : QuadK d} (hz : IsIntegral ℤ z) :
    ∃ u v : ℤ, z = (u : QuadK d) + (v : QuadK d) * omegaK d := by
  have hd_pos : 0 < d := by omega
  haveI := quadK_fact hd_pos
  haveI := quadK_numberField (d := d)
  have hd0 : d ≠ 0 := hd_sf.ne_zero
  have hdq0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (L := ℚ) hz)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm (K := ℚ) hz)
  have ht_eq := Algebra.trace_eq_matrix_trace (quadKBasis d) z
  have hz' : z = ⟨z.re, z.im⟩ := by ext <;> rfl
  conv_rhs at ht_eq => rw [hz', leftMulMatrix_quadK, Matrix.trace_fin_two_of]
  rw [ht_eq] at ht
  rw [norm_quadK] at hn
  simp only [algebraMap_int_eq, Int.coe_castRingHom] at ht hn
  replace ht : (t : ℚ) = 2 * z.re := by linarith
  have hdv : (d : ℚ) * (2 * z.im) ^ 2 = 4 * (n : ℚ) - (t : ℚ) ^ 2 := by
    rw [hn, ht]; ring
  have hint_dv : IsIntegral ℤ ((d : ℚ) * (2 * z.im)) := by
    refine IsIntegral.of_pow two_pos ?_
    have hsq : ((d : ℚ) * (2 * z.im)) ^ 2 = ((d * (4 * n - t ^ 2) : ℤ) : ℚ) := by
      push_cast; linear_combination (d : ℚ) * hdv
    rw [hsq]; exact isIntegral_intCast _
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint_dv
  simp only [algebraMap_int_eq, Int.coe_castRingHom] at hw
  have hw2 : w ^ 2 = (d : ℤ) * (4 * n - t ^ 2) := by
    have : ((w ^ 2 : ℤ) : ℚ) = (((d : ℤ) * (4 * n - t ^ 2) : ℤ) : ℚ) := by
      push_cast; rw [hw]; linear_combination (d : ℚ) * hdv
    exact_mod_cast this
  have hdw : (d : ℤ) ∣ w :=
    ((Int.squarefree_natCast.mpr hd_sf).dvd_pow_iff_dvd two_ne_zero).mp ⟨4 * n - t ^ 2, hw2⟩
  obtain ⟨v, hv⟩ := hdw
  have hvq : (v : ℚ) = 2 * z.im := by
    refine mul_left_cancel₀ hdq0 ?_
    rw [← hw, hv]; push_cast; ring
  have h4 : (4 : ℤ) ∣ t ^ 2 + (d : ℤ) * v ^ 2 := by
    refine ⟨n, ?_⟩
    have : ((t ^ 2 + (d : ℤ) * v ^ 2 : ℤ) : ℚ) = ((4 * n : ℤ) : ℚ) := by
      push_cast; rw [hvq, ht, hn]; ring
    exact_mod_cast this
  have h2 : (2 : ℤ) ∣ t - v := by
    obtain ⟨m, hm⟩ := h4
    obtain ⟨q, hq⟩ : ∃ q : ℤ, (d : ℤ) = 4 * q + 3 := ⟨(d : ℤ) / 4, by omega⟩
    have : (t ^ 2 + 3 * v ^ 2) % 4 = 0 := by
      have : t ^ 2 + 3 * v ^ 2 = 4 * (m - q * v ^ 2) := by linear_combination hm - v ^ 2 * hq
      omega
    have ht2 : t % 2 = 0 ∨ t % 2 = 1 := Int.emod_two_eq_zero_or_one t
    have hv2 : v % 2 = 0 ∨ v % 2 = 1 := Int.emod_two_eq_zero_or_one v
    have hsqmod : ∀ x : ℤ, (x % 2 = 0 → x ^ 2 % 4 = 0) ∧ (x % 2 = 1 → x ^ 2 % 4 = 1) := fun x =>
      ⟨fun h => by obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k := ⟨x / 2, by omega⟩; ring_nf; omega,
       fun h => by obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩; ring_nf; omega⟩
    rcases ht2 with ht0 | ht1 <;> rcases hv2 with hv0 | hv1
    · omega
    · have := (hsqmod t).1 ht0; have := (hsqmod v).2 hv1; omega
    · have := (hsqmod t).2 ht1; have := (hsqmod v).1 hv0; omega
    · omega
  obtain ⟨u, hu⟩ := h2
  refine ⟨u, v, ?_⟩
  ext
  · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
      QuadraticAlgebra.im_intCast, omegaK]
    have huq : (t : ℚ) - (v : ℚ) = 2 * (u : ℚ) := by exact_mod_cast hu
    linarith
  · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_intCast,
      QuadraticAlgebra.re_intCast, omegaK]
    linarith

lemma int_add_int_mul_omegaK_inj {d : ℕ} {u v u' v' : ℤ}
    (h : (u : QuadK d) + (v : QuadK d) * omegaK d = (u' : QuadK d) + (v' : QuadK d) * omegaK d) :
    u = u' ∧ v = v' := by
  have hre := congrArg QuadraticAlgebra.re h
  have him := congrArg QuadraticAlgebra.im h
  simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
    QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_intCast, omegaK] at hre him
  have hv : v = v' := by
    have : (v : ℚ) = (v' : ℚ) := by linarith
    exact_mod_cast this
  refine ⟨?_, hv⟩
  have : (u : ℚ) = (u' : ℚ) := by subst hv; linarith
  exact_mod_cast this

lemma hd_pos_of_mod8 {d : ℕ} (h : d % 8 = 3) : 0 < d := by omega

section RingOfIntegers

variable {d : ℕ} [Fact (∀ r : ℚ, r ^ 2 ≠ -(d : ℚ) + 0 * r)]

private lemma castO_mul (m n : ℤ) :
    ((m * n : ℤ) : NumberField.RingOfIntegers (QuadK d)) =
      (m : NumberField.RingOfIntegers (QuadK d)) * (n : NumberField.RingOfIntegers (QuadK d)) :=
  Int.cast_mul m n

private lemma castO_add (m n : ℤ) :
    ((m + n : ℤ) : NumberField.RingOfIntegers (QuadK d)) =
      (m : NumberField.RingOfIntegers (QuadK d)) + (n : NumberField.RingOfIntegers (QuadK d)) :=
  Int.cast_add m n

private lemma castO_sub (m n : ℤ) :
    ((m - n : ℤ) : NumberField.RingOfIntegers (QuadK d)) =
      (m : NumberField.RingOfIntegers (QuadK d)) - (n : NumberField.RingOfIntegers (QuadK d)) :=
  Int.cast_sub m n

private lemma castO_neg (m : ℤ) :
    ((-m : ℤ) : NumberField.RingOfIntegers (QuadK d)) =
      -(m : NumberField.RingOfIntegers (QuadK d)) :=
  Int.cast_neg m

private lemma castO_pow (m : ℤ) (k : ℕ) :
    ((m ^ k : ℤ) : NumberField.RingOfIntegers (QuadK d)) =
      (m : NumberField.RingOfIntegers (QuadK d)) ^ k :=
  Int.cast_pow m k

private lemma castO_nat (n : ℕ) :
    ((n : ℤ) : NumberField.RingOfIntegers (QuadK d)) =
      (n : NumberField.RingOfIntegers (QuadK d)) :=
  Int.cast_natCast n

private lemma castO_one :
    ((1 : ℤ) : NumberField.RingOfIntegers (QuadK d)) = 1 := Int.cast_one

private lemma castO_zero :
    ((0 : ℤ) : NumberField.RingOfIntegers (QuadK d)) = 0 := Int.cast_zero

private lemma castO_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((OfNat.ofNat n : ℤ) : NumberField.RingOfIntegers (QuadK d)) = OfNat.ofNat n :=
  Int.cast_ofNat n

noncomputable def omegaO (hd_mod : d % 8 = 3) : NumberField.RingOfIntegers (QuadK d) :=
  ⟨omegaK d, omegaK_isIntegral hd_mod⟩

lemma coe_omegaO (hd_mod : d % 8 = 3) :
    ((omegaO hd_mod : NumberField.RingOfIntegers (QuadK d)) : QuadK d) = omegaK d := rfl

lemma coe_int_add_int_mul_omegaO (hd_mod : d % 8 = 3) (u v : ℤ) :
    ((((u : NumberField.RingOfIntegers (QuadK d)) +
      (v : NumberField.RingOfIntegers (QuadK d)) * omegaO hd_mod) :
      NumberField.RingOfIntegers (QuadK d)) : QuadK d) =
      (u : QuadK d) + (v : QuadK d) * omegaK d := by
  rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast, map_intCast,
    ← NumberField.RingOfIntegers.coe_eq_algebraMap, coe_omegaO]

lemma omegaO_sq (hd_mod : d % 8 = 3) :
    omegaO hd_mod ^ 2 = omegaO hd_mod - (((d + 1) / 4 : ℕ) : NumberField.RingOfIntegers (QuadK d)) := by
  apply NumberField.RingOfIntegers.ext
  rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap,
    map_pow, map_sub, map_natCast, ← NumberField.RingOfIntegers.coe_eq_algebraMap, coe_omegaO]
  exact omegaK_sq hd_mod

lemma exists_int_add_int_mul_omegaO (hd_sf : Squarefree d) (hd_mod : d % 8 = 3)
    (z : NumberField.RingOfIntegers (QuadK d)) :
    ∃ u v : ℤ, z = (u : NumberField.RingOfIntegers (QuadK d)) +
      (v : NumberField.RingOfIntegers (QuadK d)) * omegaO hd_mod := by
  obtain ⟨u, v, huv⟩ := exists_int_add_int_mul_omegaK_of_isIntegral hd_sf hd_mod z.2
  refine ⟨u, v, NumberField.RingOfIntegers.ext ?_⟩
  rw [coe_int_add_int_mul_omegaO hd_mod u v]
  exact huv

lemma int_add_int_mul_omegaO_inj (hd_mod : d % 8 = 3) {u v u' v' : ℤ}
    (h : (u : NumberField.RingOfIntegers (QuadK d)) +
        (v : NumberField.RingOfIntegers (QuadK d)) * omegaO hd_mod =
      (u' : NumberField.RingOfIntegers (QuadK d)) +
        (v' : NumberField.RingOfIntegers (QuadK d)) * omegaO hd_mod) :
    u = u' ∧ v = v' := by
  apply int_add_int_mul_omegaK_inj (d := d)
  have h' := congrArg (fun z : NumberField.RingOfIntegers (QuadK d) => (z : QuadK d)) h
  rw [coe_int_add_int_mul_omegaO, coe_int_add_int_mul_omegaO] at h'
  exact h'

lemma four_mul_norm_omegaO (hd_mod : d % 8 = 3) (u v : ℤ) :
    4 * Algebra.norm ℤ ((u : NumberField.RingOfIntegers (QuadK d)) +
      (v : NumberField.RingOfIntegers (QuadK d)) * omegaO hd_mod) =
      (2 * u + v) ^ 2 + (d : ℤ) * v ^ 2 := by
  haveI := quadK_numberField (d := d)
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [Algebra.coe_norm_int, coe_int_add_int_mul_omegaO hd_mod, norm_quadK]
  simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
    QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_intCast, omegaK]
  ring

lemma norm_omegaO_nonneg (hd_sf : Squarefree d) (hd_mod : d % 8 = 3)
    (z : NumberField.RingOfIntegers (QuadK d)) : 0 ≤ Algebra.norm ℤ z := by
  obtain ⟨u, v, rfl⟩ := exists_int_add_int_mul_omegaO hd_sf hd_mod z
  have h4 := four_mul_norm_omegaO hd_mod u v
  have hd0 : (0 : ℤ) ≤ (d : ℤ) := Nat.cast_nonneg d
  nlinarith [sq_nonneg (2 * u + v), sq_nonneg v]

lemma norm_omegaO_pos (hd_sf : Squarefree d) (hd_mod : d % 8 = 3)
    {z : NumberField.RingOfIntegers (QuadK d)} (hz : z ≠ 0) : 0 < Algebra.norm ℤ z := by
  obtain ⟨u, v, rfl⟩ := exists_int_add_int_mul_omegaO hd_sf hd_mod z
  have h4 := four_mul_norm_omegaO hd_mod u v
  have hne : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (by rw [h.1, h.2]; simp)
  have hdpos : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd_pos_of_mod8 hd_mod
  by_cases hv : v = 0
  · subst hv
    have hu : u ≠ 0 := hne.resolve_right (not_not.mpr rfl)
    have hu2 : 0 < (2 * u) ^ 2 := by rcases lt_or_gt_of_ne hu with h | h <;> nlinarith
    nlinarith
  · have hv2 : 0 < v ^ 2 := by rcases lt_or_gt_of_ne hv with h | h <;> nlinarith
    nlinarith [sq_nonneg (2 * u + v)]

/-!
### Section 2: Ideals Associated to Binary Quadratic Forms `idealOfBQF`
-/

lemma bqf_b_odd {f : BQF d} (hd_mod : d % 8 = 3) : f.b % 2 = 1 := by
  have h := f.hdisc
  rcases Int.emod_two_eq_zero_or_one f.b with hb0 | hb1
  · obtain ⟨k, hk⟩ : ∃ k, f.b = 2 * k := ⟨f.b / 2, by omega⟩
    rw [hk] at h; ring_nf at h; omega
  · exact hb1

lemma bqf_k_spec {f : BQF d} (hd_mod : d % 8 = 3) :
    2 * ((f.b - 1) / 2) + 1 = f.b := by
  have := bqf_b_odd (f := f) hd_mod
  omega

noncomputable def gammaOfBQF (hd_mod : d % 8 = 3) (f : BQF d) :
    NumberField.RingOfIntegers (QuadK d) :=
  (((f.b - 1) / 2 : ℤ) : NumberField.RingOfIntegers (QuadK d)) + omegaO hd_mod

noncomputable def idealOfBQF (hd_mod : d % 8 = 3) (f : BQF d) :
    Ideal (NumberField.RingOfIntegers (QuadK d)) :=
  Ideal.span {((f.a : ℤ) : NumberField.RingOfIntegers (QuadK d)), gammaOfBQF hd_mod f}

lemma gammaOfBQF_mul_omegaO (hd_mod : d % 8 = 3) (f : BQF d) :
    (gammaOfBQF hd_mod f) * omegaO hd_mod =
      ((-f.c : ℤ) : NumberField.RingOfIntegers (QuadK d)) *
        ((f.a : ℤ) : NumberField.RingOfIntegers (QuadK d)) +
      (((f.b - 1) / 2 + 1 : ℤ) : NumberField.RingOfIntegers (QuadK d)) * (gammaOfBQF hd_mod f) := by
  set O := NumberField.RingOfIntegers (QuadK d)
  set k : ℤ := (f.b - 1) / 2
  have hk : 2 * k + 1 = f.b := bqf_k_spec hd_mod
  have h4ac : k ^ 2 + k + (((d + 1) / 4 : ℕ) : ℤ) = f.a * f.c := by
    have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
    have hd := f.hdisc
    have : 4 * (k ^ 2 + k + (((d + 1) / 4 : ℕ) : ℤ)) = (2 * k + 1) ^ 2 + (d : ℤ) := by
      have h4z : 4 * (((d + 1) / 4 : ℕ) : ℤ) = (d : ℤ) + 1 := by exact_mod_cast h4
      linear_combination h4z
    linarith [show (2 * k + 1) ^ 2 = f.b ^ 2 by rw [hk]]
  have hsq := omegaO_sq hd_mod
  have hcast := congrArg (Int.cast : ℤ → O) h4ac
  dsimp only [gammaOfBQF, O, k] at hcast ⊢
  simp only [castO_add, castO_mul, castO_neg, castO_pow, castO_nat, castO_one] at hcast ⊢
  linear_combination hsq - hcast

lemma mem_idealOfBQF_iff (hd_sf : Squarefree d) (hd_mod : d % 8 = 3) (f : BQF d)
    (z : NumberField.RingOfIntegers (QuadK d)) :
    z ∈ idealOfBQF hd_mod f ↔
      ∃ x y : ℤ, z = (x : NumberField.RingOfIntegers (QuadK d)) *
          ((f.a : ℤ) : NumberField.RingOfIntegers (QuadK d)) +
        (y : NumberField.RingOfIntegers (QuadK d)) * gammaOfBQF hd_mod f := by
  constructor
  · intro hz
    set O := NumberField.RingOfIntegers (QuadK d)
    set k : ℤ := (f.b - 1) / 2
    let I_sub : Ideal O :=
      { carrier := {w : O | ∃ x y : ℤ, w = (x : O) * (f.a : O) + (y : O) * gammaOfBQF hd_mod f}
        add_mem' := by
          rintro w₁ w₂ ⟨x₁, y₁, rfl⟩ ⟨x₂, y₂, rfl⟩
          exact ⟨x₁ + x₂, y₁ + y₂, by dsimp only [O]; simp only [castO_add]; ring⟩
        zero_mem' := ⟨0, 0, by simp⟩
        smul_mem' := by
          rintro r w ⟨x, y, rfl⟩
          obtain ⟨u, v, rfl⟩ := exists_int_add_int_mul_omegaO hd_sf hd_mod r
          have h1 : (f.a : O) * omegaO hd_mod =
              ((-k : ℤ) : O) * (f.a : O) + (f.a : O) * gammaOfBQF hd_mod f := by
            dsimp only [gammaOfBQF, O, k]; simp only [castO_neg]; ring
          have h2 := gammaOfBQF_mul_omegaO hd_mod f
          refine ⟨u * x - v * x * k - v * y * f.c, u * y + v * x * f.a + v * y * (k + 1), ?_⟩
          change ((u : O) + (v : O) * omegaO hd_mod) * ((x : O) * (f.a : O) + (y : O) * gammaOfBQF hd_mod f) = _
          dsimp only [O, k] at h1 h2 ⊢
          simp only [castO_add, castO_sub, castO_mul, castO_neg, castO_one] at h1 h2 ⊢
          linear_combination ((v : NumberField.RingOfIntegers (QuadK d)) * (x : NumberField.RingOfIntegers (QuadK d))) * h1 +
            ((v : NumberField.RingOfIntegers (QuadK d)) * (y : NumberField.RingOfIntegers (QuadK d))) * h2 }
    have hle : idealOfBQF hd_mod f ≤ I_sub := by
      rw [idealOfBQF, Ideal.span_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    exact hle hz
  · rintro ⟨x, y, rfl⟩
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

lemma idealOfBQF_ne_bot (hd_mod : d % 8 = 3) (f : BQF d) :
    idealOfBQF hd_mod f ≠ ⊥ := by
  intro hbot
  have hmem : ((f.a : ℤ) : NumberField.RingOfIntegers (QuadK d)) ∈ idealOfBQF hd_mod f :=
    Ideal.subset_span (Set.mem_insert _ _)
  rw [hbot, Ideal.mem_bot] at hmem
  have h0 : f.a = 0 := by
    have := congrArg (fun z : NumberField.RingOfIntegers (QuadK d) => (z : QuadK d).re) hmem
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap,
      map_intCast, map_zero] at this
    simp at this
    exact_mod_cast this
  linarith [f.ha]

lemma norm_idealOfBQF_elem (hd_mod : d % 8 = 3) (f : BQF d) (x y : ℤ) :
    Algebra.norm ℤ ((x : NumberField.RingOfIntegers (QuadK d)) *
        ((f.a : ℤ) : NumberField.RingOfIntegers (QuadK d)) +
      (y : NumberField.RingOfIntegers (QuadK d)) * gammaOfBQF hd_mod f) =
      f.a * f.eval x y := by
  set k : ℤ := (f.b - 1) / 2
  have hk : 2 * k + 1 = f.b := bqf_k_spec hd_mod
  have heq : (x : NumberField.RingOfIntegers (QuadK d)) *
      ((f.a : ℤ) : NumberField.RingOfIntegers (QuadK d)) +
      (y : NumberField.RingOfIntegers (QuadK d)) * gammaOfBQF hd_mod f =
      ((x * f.a + y * k : ℤ) : NumberField.RingOfIntegers (QuadK d)) +
      (y : NumberField.RingOfIntegers (QuadK d)) * omegaO hd_mod := by
    dsimp only [gammaOfBQF, k]; simp only [Int.cast_add, Int.cast_mul]; ring
  rw [heq]
  have h4 := four_mul_norm_omegaO hd_mod (x * f.a + y * k) y
  have h2 : 2 * (x * f.a + y * k) + y = 2 * f.a * x + f.b * y := by linear_combination y * hk
  rw [h2] at h4
  have h4f : (2 * f.a * x + f.b * y) ^ 2 + (d : ℤ) * y ^ 2 = 4 * f.a * f.eval x y := by
    dsimp only [eval]; linear_combination -y ^ 2 * f.hdisc
  linarith

lemma absNorm_idealOfBQF (hd_sf : Squarefree d) (hd_mod : d % 8 = 3) (f : BQF d) :
    haveI := quadK_numberField (d := d)
    Ideal.absNorm (idealOfBQF hd_mod f) = f.a.toNat := by
  haveI := quadK_numberField (d := d)
  set O := NumberField.RingOfIntegers (QuadK d)
  set I := idealOfBQF hd_mod f
  set k : ℤ := (f.b - 1) / 2
  have hapos : 0 < f.a.toNat := by have := f.ha; omega
  have haeq : (f.a.toNat : ℤ) = f.a := Int.toNat_of_nonneg f.ha.le
  haveI : NeZero f.a.toNat := ⟨hapos.ne'⟩
  let φ : ZMod f.a.toNat → (O ⧸ I) := fun r => Ideal.Quotient.mk I (r.val : O)
  have hbij : Function.Bijective φ := by
    constructor
    · intro r₁ r₂ heq
      dsimp only [φ] at heq
      rw [Ideal.Quotient.eq] at heq
      obtain ⟨x, y, hxy⟩ := (mem_idealOfBQF_iff hd_sf hd_mod f _).mp heq
      have h1 : (((r₁.val : ℤ) - (r₂.val : ℤ) : ℤ) : O) + ((0 : ℤ) : O) * omegaO hd_mod =
          ((x * f.a + y * k : ℤ) : O) + (y : O) * omegaO hd_mod := by
        dsimp only [gammaOfBQF, O, k] at hxy ⊢
        simp only [castO_add, castO_sub, castO_mul, castO_nat, castO_zero]
        linear_combination hxy
      obtain ⟨hu, hv⟩ := int_add_int_mul_omegaO_inj hd_mod h1
      subst hv
      have hdvd : (f.a.toNat : ℤ) ∣ ((r₁.val : ℤ) - (r₂.val : ℤ)) := ⟨x, by rw [haeq]; linarith⟩
      have hmod : (r₁.val : ZMod f.a.toNat) = (r₂.val : ZMod f.a.toNat) := by
        rw [← sub_eq_zero]
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ f.a.toNat).mpr hdvd
        simpa using this
      simpa [ZMod.natCast_zmod_val] using hmod
    · intro q
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
      obtain ⟨u, v, rfl⟩ := exists_int_add_int_mul_omegaO hd_sf hd_mod z
      set r_int : ℤ := u - v * k
      let r : ZMod f.a.toNat := (r_int : ZMod f.a.toNat)
      refine ⟨r, ?_⟩
      dsimp only [φ]
      rw [Ideal.Quotient.eq]
      have hdvd : (f.a.toNat : ℤ) ∣ ((r.val : ℤ) - r_int) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        simp [r]
      obtain ⟨x, hx⟩ := hdvd
      rw [mem_idealOfBQF_iff hd_sf hd_mod f]
      refine ⟨x, -v, ?_⟩
      have hx' : (r.val : ℤ) - (u - v * k) = x * f.a := by
        rw [haeq] at hx; dsimp only [r_int] at hx; linarith
      have hxO := congrArg (Int.cast : ℤ → O) hx'
      dsimp only [gammaOfBQF, O, k] at hxO ⊢
      simp only [castO_add, castO_sub, castO_mul, castO_neg, castO_nat] at hxO ⊢
      linear_combination hxO
  have hcard : Nat.card (O ⧸ I) = f.a.toNat := by
    rw [← Nat.card_congr (Equiv.ofBijective φ hbij), Nat.card_zmod]
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact hcard

lemma idealOfBQF_mul_conj (hd_sf : Squarefree d) (hd_mod : d % 8 = 3) (f : BQF d) :
    idealOfBQF hd_mod f * idealOfBQF hd_mod f.conj =
      Ideal.span {((f.a : ℤ) : NumberField.RingOfIntegers (QuadK d))} := by
  set O := NumberField.RingOfIntegers (QuadK d)
  set k : ℤ := (f.b - 1) / 2
  have hk : 2 * k + 1 = f.b := bqf_k_spec hd_mod
  have hk' : (f.conj.b - 1) / 2 = -k - 1 := by
    dsimp only [BQF.conj]; omega
  have hγprod : gammaOfBQF hd_mod f * gammaOfBQF hd_mod f.conj =
      ((-(f.a * f.c) : ℤ) : O) := by
    have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
    have h4z : 4 * (((d + 1) / 4 : ℕ) : ℤ) = (d : ℤ) + 1 := by exact_mod_cast h4
    have h4ac : k ^ 2 + k + (((d + 1) / 4 : ℕ) : ℤ) = f.a * f.c := by
      have hd := f.hdisc
      have : (2 * k + 1) ^ 2 = f.b ^ 2 := by rw [hk]
      linarith
    have hcast := congrArg (Int.cast : ℤ → O) h4ac
    dsimp only [gammaOfBQF]
    rw [hk']
    have hsq := omegaO_sq hd_mod
    dsimp only [O, k] at hcast ⊢
    simp only [castO_add, castO_sub, castO_mul, castO_neg, castO_pow, castO_nat, castO_one] at hcast ⊢
    linear_combination hsq - hcast
  have hγsub : gammaOfBQF hd_mod f - gammaOfBQF hd_mod f.conj = ((f.b : ℤ) : O) := by
    dsimp only [gammaOfBQF]; rw [hk']
    have hcast := congrArg (Int.cast : ℤ → O) hk
    dsimp only [O, k] at hcast ⊢
    simp only [castO_add, castO_sub, castO_mul, castO_neg, castO_one, castO_ofNat] at hcast ⊢
    linear_combination hcast
  apply le_antisymm
  · rw [idealOfBQF, idealOfBQF, Ideal.span_mul_span', Ideal.span_le]
    intro w hw
    rcases Set.mem_mul.mp hw with ⟨x, hx, y, hy, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · rw [hγprod]; dsimp only [O]; rw [castO_neg, castO_mul]
      exact Submodule.neg_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  · rw [Ideal.span_singleton_le_iff_mem]
    have hfa_f : ((f.a : ℤ) : O) ∈ idealOfBQF hd_mod f := Ideal.subset_span (Set.mem_insert _ _)
    have hfa_fc : ((f.a : ℤ) : O) ∈ idealOfBQF hd_mod f.conj := Ideal.subset_span (Set.mem_insert _ _)
    have hγ_f : gammaOfBQF hd_mod f ∈ idealOfBQF hd_mod f := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have hγ_fc : gammaOfBQF hd_mod f.conj ∈ idealOfBQF hd_mod f.conj := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have hmem_aa : ((f.a : ℤ) : O) * ((f.a : ℤ) : O) ∈ idealOfBQF hd_mod f * idealOfBQF hd_mod f.conj :=
      Ideal.mul_mem_mul hfa_f hfa_fc
    have hmem_ab : ((f.a : ℤ) : O) * ((f.b : ℤ) : O) ∈ idealOfBQF hd_mod f * idealOfBQF hd_mod f.conj := by
      rw [← hγsub, mul_sub]
      refine Ideal.sub_mem _ ?_ (Ideal.mul_mem_mul hfa_f hγ_fc)
      rw [mul_comm ((f.a : ℤ) : O) (gammaOfBQF hd_mod f)]
      exact Ideal.mul_mem_mul hγ_f hfa_fc
    have hmem_ac : ((f.a : ℤ) : O) * ((f.c : ℤ) : O) ∈ idealOfBQF hd_mod f * idealOfBQF hd_mod f.conj := by
      have := Submodule.neg_mem _ (Ideal.mul_mem_mul hγ_f hγ_fc)
      dsimp only [O] at hγprod this ⊢
      rwa [hγprod, castO_neg, castO_mul, neg_neg] at this
    -- Since d is squarefree, gcd(f.a, f.b, f.c) = 1
    set g1 : ℕ := Int.gcd f.a f.b
    set g : ℕ := Int.gcd (g1 : ℤ) f.c
    have hg1 : g = 1 := by
      have hg_a : (g : ℤ) ∣ f.a := dvd_trans (Int.gcd_dvd_left _ _) (Int.gcd_dvd_left _ _)
      have hg_b : (g : ℤ) ∣ f.b := dvd_trans (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
      have hg_c : (g : ℤ) ∣ f.c := Int.gcd_dvd_right _ _
      have hg2_d : (g : ℤ) ^ 2 ∣ (d : ℤ) := by
        rw [← f.hdisc]
        obtain ⟨a', ha'⟩ := hg_a; obtain ⟨b', hb'⟩ := hg_b; obtain ⟨c', hc'⟩ := hg_c
        exact ⟨4 * a' * c' - b' ^ 2, by rw [ha', hb', hc']; ring⟩
      have hg2N : g * g ∣ d := by
        have : ((g * g : ℕ) : ℤ) ∣ (d : ℤ) := by simpa [sq] using hg2_d
        exact_mod_cast this
      exact Nat.isUnit_iff.mp (hd_sf g hg2N)
    have hbez1 : (g1 : ℤ) = f.a * Int.gcdA f.a f.b + f.b * Int.gcdB f.a f.b := Int.gcd_eq_gcd_ab f.a f.b
    have hbez2 : (1 : ℤ) = (g1 : ℤ) * Int.gcdA (g1 : ℤ) f.c + f.c * Int.gcdB (g1 : ℤ) f.c := by
      have h := Int.gcd_eq_gcd_ab (g1 : ℤ) f.c
      change (g : ℤ) = _ at h
      rwa [hg1, Nat.cast_one] at h
    set r : ℤ := Int.gcdA f.a f.b * Int.gcdA (g1 : ℤ) f.c
    set s : ℤ := Int.gcdB f.a f.b * Int.gcdA (g1 : ℤ) f.c
    set t : ℤ := Int.gcdB (g1 : ℤ) f.c
    have hcomb : r * f.a + s * f.b + t * f.c = 1 := by
      dsimp only [r, s, t]; linear_combination -hbez2 - Int.gcdA (g1 : ℤ) f.c * hbez1
    have hcombO : (r : O) * ((f.a : O) * (f.a : O)) + (s : O) * ((f.a : O) * (f.b : O)) +
        (t : O) * ((f.a : O) * (f.c : O)) = (f.a : O) := by
      have hcast := congrArg (Int.cast : ℤ → O) hcomb
      dsimp only [O] at hcast ⊢
      simp only [castO_add, castO_mul, castO_one] at hcast
      linear_combination (f.a : NumberField.RingOfIntegers (QuadK d)) * hcast
    rw [← hcombO]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem_aa)
      (Ideal.mul_mem_left _ _ hmem_ab)) (Ideal.mul_mem_left _ _ hmem_ac)

lemma sl2Equiv_imp_classGroup_eq (hd_sf : Squarefree d) (hd_mod : d % 8 = 3)
    {f g : BQF d} (hfg : SL2Equiv f g) :
    haveI := quadK_numberField (d := d)
    ClassGroup.mk0 ⟨idealOfBQF hd_mod f, mem_nonZeroDivisors_of_ne_zero (idealOfBQF_ne_bot hd_mod f)⟩ =
    ClassGroup.mk0 ⟨idealOfBQF hd_mod g, mem_nonZeroDivisors_of_ne_zero (idealOfBQF_ne_bot hd_mod g)⟩ := by
  haveI := quadK_numberField (d := d)
  set O := NumberField.RingOfIntegers (QuadK d)
  obtain ⟨M, hdet, heval⟩ := hfg
  set p := M 0 0; set q := M 0 1; set r := M 1 0; set s := M 1 1
  have hdet' : p * s - q * r = 1 := by
    have := hdet; rw [Matrix.det_fin_two] at this; exact this
  have hga : g.a = f.eval p r := by
    have := heval 1 0
    simp only [mul_one, mul_zero, add_zero, eval, one_pow, zero_pow two_ne_zero] at this
    dsimp only [eval]; linarith
  have hgb : g.b = 2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s := by
    have h11 := heval 1 1
    have h10 := heval 1 0
    have h01 := heval 0 1
    simp only [mul_one, mul_zero, add_zero, zero_add, eval, one_pow, zero_pow two_ne_zero] at h11 h10 h01
    linarith
  set kf : ℤ := (f.b - 1) / 2
  set kg : ℤ := (g.b - 1) / 2
  have hkf : 2 * kf + 1 = f.b := bqf_k_spec hd_mod
  have hkg : 2 * kg + 1 = g.b := bqf_k_spec hd_mod
  -- αbar = (p*f.a + r*(kf + 1)) - r*omegaO
  let αbar : O := ((p * f.a + r * (kf + 1) : ℤ) : O) - (r : O) * omegaO hd_mod
  have hαbar_ne : αbar ≠ 0 := by
    intro h0
    have h1 : ((p * f.a + r * (kf + 1) : ℤ) : O) + ((-r : ℤ) : O) * omegaO hd_mod =
        ((0 : ℤ) : O) + ((0 : ℤ) : O) * omegaO hd_mod := by
      dsimp only [αbar] at h0; simp only [Int.cast_neg, Int.cast_zero]; linear_combination h0
    obtain ⟨hu, hv⟩ := int_add_int_mul_omegaO_inj hd_mod h1
    have hr0 : r = 0 := by omega
    have hp0 : p = 0 := by
      have : p * f.a = 0 := by rw [hr0] at hu; linarith
      exact (mul_eq_zero.mp this).resolve_right f.ha.ne'
    rw [hp0, hr0] at hdet'; norm_num at hdet'
  have hfa_ne : ((f.a : ℤ) : O) ≠ 0 := by
    intro h0
    have := congrArg (fun z : O => (z : QuadK d).re) h0
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap,
      map_intCast, map_zero] at this
    simp at this
    have : f.a = 0 := by exact_mod_cast this
    linarith [f.ha]
  have hid1 : αbar * ((p : O) * (f.a : O) + (r : O) * gammaOfBQF hd_mod f) =
      ((f.a : ℤ) : O) * ((g.a : ℤ) : O) := by
    apply NumberField.RingOfIntegers.ext
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap]
    dsimp only [αbar, gammaOfBQF]
    simp only [map_mul, map_add, map_sub, map_intCast, ← NumberField.RingOfIntegers.coe_eq_algebraMap, coe_omegaO]
    have hga_q : (g.a : ℚ) = (f.a : ℚ) * (p : ℚ) ^ 2 + (f.b : ℚ) * (p : ℚ) * (r : ℚ) + (f.c : ℚ) * (r : ℚ) ^ 2 := by
      exact_mod_cast hga
    have hkf_q : 2 * (kf : ℚ) + 1 = (f.b : ℚ) := by exact_mod_cast hkf
    have hdisc_q : 4 * (f.a : ℚ) * (f.c : ℚ) - (f.b : ℚ) ^ 2 = (d : ℚ) := by exact_mod_cast f.hdisc
    ext
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_sub, QuadraticAlgebra.re_add,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_sub,
        QuadraticAlgebra.im_add, QuadraticAlgebra.im_intCast, omegaK, kf]
      dsimp only [kf] at hkf_q
      simp only [Int.cast_add, Int.cast_mul, Int.cast_one] at hkf_q ⊢
      linear_combination -(f.a : ℚ) * hga_q - ((r : ℚ) ^ 2 / 4) * hdisc_q +
        ((f.a : ℚ) * (p : ℚ) * (r : ℚ) + ((r : ℚ) ^ 2 * (2 * (((f.b - 1) / 2 : ℤ) : ℚ) + 1 + (f.b : ℚ))) / 4) * hkf_q
    · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_sub, QuadraticAlgebra.im_add,
        QuadraticAlgebra.im_intCast, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_sub,
        QuadraticAlgebra.re_add, QuadraticAlgebra.re_intCast, omegaK, kf]
      simp only [Int.cast_add, Int.cast_mul, Int.cast_one]; ring
  have hid2 : αbar * ((q : O) * (f.a : O) + (s : O) * gammaOfBQF hd_mod f) =
      ((f.a : ℤ) : O) * gammaOfBQF hd_mod g := by
    apply NumberField.RingOfIntegers.ext
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap]
    dsimp only [αbar, gammaOfBQF]
    simp only [map_mul, map_add, map_sub, map_intCast, ← NumberField.RingOfIntegers.coe_eq_algebraMap, coe_omegaO]
    have hgb_q : (g.b : ℚ) = 2 * (f.a : ℚ) * (p : ℚ) * (q : ℚ) +
        (f.b : ℚ) * ((p : ℚ) * (s : ℚ) + (q : ℚ) * (r : ℚ)) + 2 * (f.c : ℚ) * (r : ℚ) * (s : ℚ) := by
      exact_mod_cast hgb
    have hkf_q : 2 * (kf : ℚ) + 1 = (f.b : ℚ) := by exact_mod_cast hkf
    have hkg_q : 2 * (kg : ℚ) + 1 = (g.b : ℚ) := by exact_mod_cast hkg
    have hdet_q : (p : ℚ) * (s : ℚ) - (q : ℚ) * (r : ℚ) = 1 := by exact_mod_cast hdet'
    have hdisc_q : 4 * (f.a : ℚ) * (f.c : ℚ) - (f.b : ℚ) ^ 2 = (d : ℚ) := by exact_mod_cast f.hdisc
    ext
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_sub, QuadraticAlgebra.re_add,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_sub,
        QuadraticAlgebra.im_add, QuadraticAlgebra.im_intCast, omegaK, kf, kg]
      dsimp only [kf, kg] at hkf_q hkg_q
      simp only [Int.cast_add, Int.cast_mul, Int.cast_one] at hkf_q hkg_q ⊢
      linear_combination -((f.a : ℚ) / 2) * hkg_q - ((f.a : ℚ) / 2) * hgb_q -
        ((r : ℚ) * (s : ℚ) / 4) * hdisc_q +
        (((f.a : ℚ) * ((p : ℚ) * (s : ℚ) + (q : ℚ) * (r : ℚ))) / 2 +
          ((r : ℚ) * (s : ℚ) * (2 * (((f.b - 1) / 2 : ℤ) : ℚ) + 1 + (f.b : ℚ))) / 4) * hkf_q
    · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_sub, QuadraticAlgebra.im_add,
        QuadraticAlgebra.im_intCast, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_sub,
        QuadraticAlgebra.re_add, QuadraticAlgebra.re_intCast, omegaK, kf, kg]
      simp only [Int.cast_add, Int.cast_mul, Int.cast_one]
      linear_combination ((f.a : ℚ) / 2) * hdet_q
  -- Prove Ideal.span {αbar} * idealOfBQF f = Ideal.span {f.a} * idealOfBQF g
  have hIdeq : Ideal.span {αbar} * idealOfBQF hd_mod f =
      Ideal.span {((f.a : ℤ) : O)} * idealOfBQF hd_mod g := by
    apply le_antisymm
    · rw [Ideal.mul_le]
      intro a ha z hz
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨x, y, rfl⟩ := (mem_idealOfBQF_iff hd_sf hd_mod f z).mp hz
      set x' : ℤ := s * x - q * y
      set y' : ℤ := -r * x + p * y
      have hdecomp : (x : O) * (f.a : O) + (y : O) * gammaOfBQF hd_mod f =
          (x' : O) * ((p : O) * (f.a : O) + (r : O) * gammaOfBQF hd_mod f) +
          (y' : O) * ((q : O) * (f.a : O) + (s : O) * gammaOfBQF hd_mod f) := by
        have hdetO := congrArg (Int.cast : ℤ → O) hdet'
        dsimp only [O, x', y'] at hdetO ⊢
        simp only [castO_add, castO_sub, castO_mul, castO_neg, castO_one] at hdetO ⊢
        linear_combination -(x : NumberField.RingOfIntegers (QuadK d)) * (f.a : NumberField.RingOfIntegers (QuadK d)) * hdetO -
          (y : NumberField.RingOfIntegers (QuadK d)) * gammaOfBQF hd_mod f * hdetO
      have hmul : αbar * c * ((x : O) * (f.a : O) + (y : O) * gammaOfBQF hd_mod f) =
          (((f.a : ℤ) : O) * c) * ((x' : O) * (g.a : O) + (y' : O) * gammaOfBQF hd_mod g) := by
        rw [hdecomp]
        linear_combination c * (x' : O) * hid1 + c * (y' : O) * hid2
      rw [hmul]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton.mpr ⟨c, rfl⟩)
        ((mem_idealOfBQF_iff hd_sf hd_mod g _).mpr ⟨x', y', rfl⟩)
    · rw [Ideal.mul_le]
      intro a ha z hz
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨x, y, rfl⟩ := (mem_idealOfBQF_iff hd_sf hd_mod g z).mp hz
      have hmul : ((f.a : ℤ) : O) * c * ((x : O) * (g.a : O) + (y : O) * gammaOfBQF hd_mod g) =
          (αbar * c) * (((p * x + q * y : ℤ) : O) * (f.a : O) +
            ((r * x + s * y : ℤ) : O) * gammaOfBQF hd_mod f) := by
        dsimp only [O]
        simp only [castO_add, castO_mul]
        linear_combination -c * (x : NumberField.RingOfIntegers (QuadK d)) * hid1 -
          c * (y : NumberField.RingOfIntegers (QuadK d)) * hid2
      rw [hmul]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton.mpr ⟨c, rfl⟩)
        ((mem_idealOfBQF_iff hd_sf hd_mod f _).mpr ⟨p * x + q * y, r * x + s * y, rfl⟩)
  rw [ClassGroup.mk0_eq_mk0_iff]
  exact ⟨αbar, ((f.a : ℤ) : O), hαbar_ne, hfa_ne, hIdeq⟩

lemma classGroup_eq_imp_gl2Equiv (hd_sf : Squarefree d) (hd_mod : d % 8 = 3)
    {f g : BQF d}
    (heq : haveI := quadK_numberField (d := d)
      ClassGroup.mk0 ⟨idealOfBQF hd_mod f, mem_nonZeroDivisors_of_ne_zero (idealOfBQF_ne_bot hd_mod f)⟩ =
      ClassGroup.mk0 ⟨idealOfBQF hd_mod g, mem_nonZeroDivisors_of_ne_zero (idealOfBQF_ne_bot hd_mod g)⟩) :
    GL2Equiv f g := by
  haveI := quadK_numberField (d := d)
  set O := NumberField.RingOfIntegers (QuadK d)
  rw [ClassGroup.mk0_eq_mk0_iff] at heq
  obtain ⟨u, v, hu0, hv0, huv⟩ := heq
  have hnorm_eq : Algebra.norm ℤ u * f.a = Algebra.norm ℤ v * g.a := by
    have h1 := congrArg Ideal.absNorm huv
    rw [map_mul, map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton,
      absNorm_idealOfBQF hd_sf hd_mod f, absNorm_idealOfBQF hd_sf hd_mod g] at h1
    have hnu : 0 ≤ Algebra.norm ℤ u := norm_omegaO_nonneg hd_sf hd_mod u
    have hnv : 0 ≤ Algebra.norm ℤ v := norm_omegaO_nonneg hd_sf hd_mod v
    have h1z : (((Algebra.norm ℤ u).natAbs * f.a.toNat : ℕ) : ℤ) =
        (((Algebra.norm ℤ v).natAbs * g.a.toNat : ℕ) : ℤ) := by exact_mod_cast h1
    push_cast at h1z
    rw [abs_of_nonneg hnu, abs_of_nonneg hnv,
      Int.toNat_of_nonneg f.ha.le, Int.toNat_of_nonneg g.ha.le] at h1z
    exact h1z
  have hm1 : u * (f.a : O) ∈ Ideal.span {v} * idealOfBQF hd_mod g := by
    rw [← huv]; exact Ideal.mul_mem_mul (Ideal.subset_span rfl) (Ideal.subset_span (by simp))
  have hm2 : u * gammaOfBQF hd_mod f ∈ Ideal.span {v} * idealOfBQF hd_mod g := by
    rw [← huv]; exact Ideal.mul_mem_mul (Ideal.subset_span rfl) (Ideal.subset_span (by simp))
  rw [Ideal.mem_span_singleton_mul] at hm1 hm2
  obtain ⟨w₁, hw₁, heq₁⟩ := hm1
  obtain ⟨w₂, hw₂, heq₂⟩ := hm2
  obtain ⟨m00, m10, rfl⟩ := (mem_idealOfBQF_iff hd_sf hd_mod g w₁).mp hw₁
  obtain ⟨m01, m11, rfl⟩ := (mem_idealOfBQF_iff hd_sf hd_mod g w₂).mp hw₂
  have hn1 : v * (g.a : O) ∈ Ideal.span {u} * idealOfBQF hd_mod f := by
    rw [huv]; exact Ideal.mul_mem_mul (Ideal.subset_span rfl) (Ideal.subset_span (by simp))
  have hn2 : v * gammaOfBQF hd_mod g ∈ Ideal.span {u} * idealOfBQF hd_mod f := by
    rw [huv]; exact Ideal.mul_mem_mul (Ideal.subset_span rfl) (Ideal.subset_span (by simp))
  rw [Ideal.mem_span_singleton_mul] at hn1 hn2
  obtain ⟨z₁, hz₁, hzeq₁⟩ := hn1
  obtain ⟨z₂, hz₂, hzeq₂⟩ := hn2
  obtain ⟨n00, n10, rfl⟩ := (mem_idealOfBQF_iff hd_sf hd_mod f z₁).mp hz₁
  obtain ⟨n01, n11, rfl⟩ := (mem_idealOfBQF_iff hd_sf hd_mod f z₂).mp hz₂
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![m00, m01; m10, m11]
  let N : Matrix (Fin 2) (Fin 2) ℤ := !![n00, n01; n10, n11]
  have hNM : N * M = 1 := by
    have hcomp1 : u * (f.a : O) =
        u * (((n00 * m00 + n01 * m10 : ℤ) : O) * (f.a : O) +
          ((n10 * m00 + n11 * m10 : ℤ) : O) * gammaOfBQF hd_mod f) := by
      dsimp only [O]
      simp only [castO_add, castO_mul]
      linear_combination heq₁.symm + (m00 : NumberField.RingOfIntegers (QuadK d)) * hzeq₁.symm +
        (m10 : NumberField.RingOfIntegers (QuadK d)) * hzeq₂.symm
    have hcomp2 : u * gammaOfBQF hd_mod f =
        u * (((n00 * m01 + n01 * m11 : ℤ) : O) * (f.a : O) +
          ((n10 * m01 + n11 * m11 : ℤ) : O) * gammaOfBQF hd_mod f) := by
      dsimp only [O]
      simp only [castO_add, castO_mul]
      linear_combination heq₂.symm + (m01 : NumberField.RingOfIntegers (QuadK d)) * hzeq₁.symm +
        (m11 : NumberField.RingOfIntegers (QuadK d)) * hzeq₂.symm
    have hc1 := mul_left_cancel₀ hu0 hcomp1
    have hc2 := mul_left_cancel₀ hu0 hcomp2
    set kf : ℤ := (f.b - 1) / 2
    have h1' : (f.a : O) + ((0 : ℤ) : O) * omegaO hd_mod =
        (((n00 * m00 + n01 * m10) * f.a + (n10 * m00 + n11 * m10) * kf : ℤ) : O) +
        ((n10 * m00 + n11 * m10 : ℤ) : O) * omegaO hd_mod := by
      dsimp only [gammaOfBQF, O, kf] at hc1 ⊢
      simp only [castO_add, castO_mul, castO_zero] at hc1 ⊢
      linear_combination hc1
    have h2' : (kf : O) + ((1 : ℤ) : O) * omegaO hd_mod =
        (((n00 * m01 + n01 * m11) * f.a + (n10 * m01 + n11 * m11) * kf : ℤ) : O) +
        ((n10 * m01 + n11 * m11 : ℤ) : O) * omegaO hd_mod := by
      dsimp only [gammaOfBQF, O, kf] at hc2 ⊢
      simp only [castO_add, castO_mul, castO_one] at hc2 ⊢
      linear_combination hc2
    obtain ⟨ha1, hb1⟩ := int_add_int_mul_omegaO_inj hd_mod h1'
    obtain ⟨ha2, hb2⟩ := int_add_int_mul_omegaO_inj hd_mod h2'
    have he00 : n00 * m00 + n01 * m10 = 1 := by
      have : f.a = (n00 * m00 + n01 * m10) * f.a := by rw [← hb1, zero_mul, add_zero] at ha1; exact ha1
      nlinarith [f.ha]
    have he01 : n00 * m01 + n01 * m11 = 0 := by
      have : 0 = (n00 * m01 + n01 * m11) * f.a := by rw [← hb2, one_mul] at ha2; linarith
      nlinarith [f.ha]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, N, Matrix.mul_apply, Fin.sum_univ_two, he00, he01, hb1.symm, hb2.symm]
  have hdetM : M.det = 1 ∨ M.det = -1 := by
    have h1 : N.det * M.det = 1 := by rw [← Matrix.det_mul, hNM, Matrix.det_one]
    exact (Int.eq_one_or_neg_one_of_mul_eq_one' h1).imp And.right And.right
  refine GL2Equiv.symm ⟨M, hdetM, fun x y => ?_⟩
  have hlin : u * ((x : O) * (f.a : O) + (y : O) * gammaOfBQF hd_mod f) =
      v * (((M 0 0 * x + M 0 1 * y : ℤ) : O) * (g.a : O) +
        ((M 1 0 * x + M 1 1 * y : ℤ) : O) * gammaOfBQF hd_mod g) := by
    dsimp only [O]
    simp only [M, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, Fin.isValue, castO_add, castO_mul]
    linear_combination (x : NumberField.RingOfIntegers (QuadK d)) * heq₁.symm +
      (y : NumberField.RingOfIntegers (QuadK d)) * heq₂.symm
  have hN := congrArg (Algebra.norm ℤ) hlin
  rw [map_mul, map_mul, norm_idealOfBQF_elem hd_mod f, norm_idealOfBQF_elem hd_mod g] at hN
  have hpos : 0 < Algebra.norm ℤ u * f.a := mul_pos (norm_omegaO_pos hd_sf hd_mod hu0) f.ha
  rw [← mul_assoc, ← mul_assoc, hnorm_eq] at hN
  exact (mul_left_cancel₀ (by linarith : Algebra.norm ℤ v * g.a ≠ 0) hN).symm

/-- Every nonzero ideal `I` of `𝓞 (QuadK d)` is `(g) * idealOfBQF f` for some `g > 0` and `f : BQF d`. -/
lemma exists_bqf_of_ideal (hd_sf : Squarefree d) (hd_mod : d % 8 = 3)
    (I : Ideal (NumberField.RingOfIntegers (QuadK d))) (hI : I ≠ ⊥) :
    ∃ (g : ℤ) (f : BQF d), 0 < g ∧
      I = Ideal.span {(g : NumberField.RingOfIntegers (QuadK d))} * idealOfBQF hd_mod f := by
  set O := NumberField.RingOfIntegers (QuadK d)
  -- 1. Find smallest positive v-coordinate of an element in I
  have hex_v : ∃ v : ℕ, 0 < v ∧ ∃ u : ℤ, (u : O) + ((v : ℤ) : O) * omegaO hd_mod ∈ I := by
    obtain ⟨z, hzI, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨u, v, rfl⟩ := exists_int_add_int_mul_omegaO hd_sf hd_mod z
    by_cases hv : v = 0
    · subst hv
      have hu0 : u ≠ 0 := by intro h; exact hz0 (by rw [h]; simp)
      have hmul : ((u : O) + ((0 : ℤ) : O) * omegaO hd_mod) * omegaO hd_mod ∈ I :=
        Ideal.mul_mem_right _ I hzI
      by_cases hup : 0 < u
      · refine ⟨u.toNat, by omega, 0, ?_⟩
        simpa [Int.toNat_of_nonneg hup.le] using hmul
      · have hneg : -(((u : O) + ((0 : ℤ) : O) * omegaO hd_mod) * omegaO hd_mod) ∈ I :=
          I.neg_mem hmul
        refine ⟨(-u).toNat, by omega, 0, ?_⟩
        have hcast : ((((-u).toNat : ℕ) : ℤ) : O) = -(u : O) := by
          rw [Int.toNat_of_nonneg (by omega), Int.cast_neg]
        convert hneg using 1
        rw [hcast]; ring
    · by_cases hvp : 0 < v
      · exact ⟨v.toNat, by omega, u, by simpa [Int.toNat_of_nonneg hvp.le] using hzI⟩
      · have hneg := I.neg_mem hzI
        refine ⟨(-v).toNat, by omega, -u, ?_⟩
        have hcast : ((((-v).toNat : ℕ) : ℤ) : O) = -(v : O) := by
          rw [Int.toNat_of_nonneg (by omega), Int.cast_neg]
        convert hneg using 1
        rw [hcast, Int.cast_neg]; ring
  classical
  set gN : ℕ := Nat.find hex_v
  have hgN_spec := Nat.find_spec hex_v
  have hgpos : (0 : ℤ) < (gN : ℤ) := by exact_mod_cast hgN_spec.1
  obtain ⟨u₁, hu₁I⟩ := hgN_spec.2
  have hg_dvd_v : ∀ u v : ℤ, (u : O) + (v : O) * omegaO hd_mod ∈ I → (gN : ℤ) ∣ v := by
    intro u v huvI
    set r : ℤ := v % (gN : ℤ)
    set q : ℤ := v / (gN : ℤ)
    have hr_nonneg : 0 ≤ r := Int.emod_nonneg v hgpos.ne'
    have hr_lt : r < (gN : ℤ) := Int.emod_lt_of_pos v hgpos
    have hdiff : ((u - q * u₁ : ℤ) : O) + (r : O) * omegaO hd_mod ∈ I := by
      have := Ideal.sub_mem I huvI (Ideal.mul_mem_left I (q : O) hu₁I)
      have heq : (u : O) + (v : O) * omegaO hd_mod - (q : O) * ((u₁ : O) + ((gN : ℤ) : O) * omegaO hd_mod) =
          ((u - q * u₁ : ℤ) : O) + (r : O) * omegaO hd_mod := by
        have hv : v = (gN : ℤ) * q + r := (Int.mul_ediv_add_emod v (gN : ℤ)).symm
        have hvO := congrArg (Int.cast : ℤ → O) hv
        dsimp only [O] at hvO ⊢
        simp only [castO_add, castO_sub, castO_mul] at hvO ⊢
        linear_combination hvO * omegaO hd_mod
      rwa [heq] at this
    by_contra hndvd
    have hr_pos : 0 < r.toNat := by
      have : r ≠ 0 := fun h => hndvd (Int.dvd_of_emod_eq_zero h)
      omega
    have hlt_min : r.toNat < gN := by omega
    exact Nat.find_min hex_v hlt_min ⟨hr_pos, u - q * u₁, by simpa [Int.toNat_of_nonneg hr_nonneg] using hdiff⟩
  -- 2. Find smallest positive integer in I
  have hex_m : ∃ m : ℕ, 0 < m ∧ ((m : ℤ) : O) ∈ I := by
    set c_d : ℕ := (d + 1) / 4
    have hprod : ((u₁ : O) + ((gN : ℤ) : O) * omegaO hd_mod) *
        (((u₁ + gN : ℤ) : O) - ((gN : ℤ) : O) * omegaO hd_mod) ∈ I :=
      Ideal.mul_mem_right _ I hu₁I
    have hval : ((u₁ : O) + ((gN : ℤ) : O) * omegaO hd_mod) *
        (((u₁ + gN : ℤ) : O) - ((gN : ℤ) : O) * omegaO hd_mod) =
        ((u₁ ^ 2 + u₁ * (gN : ℤ) + (c_d : ℤ) * (gN : ℤ) ^ 2 : ℤ) : O) := by
      have hsq := omegaO_sq hd_mod
      dsimp only [O, c_d]
      simp only [castO_add, castO_mul, castO_pow, castO_nat]
      linear_combination -((gN : NumberField.RingOfIntegers (QuadK d)) ^ 2) * hsq
    rw [hval] at hprod
    have hpos : 0 < u₁ ^ 2 + u₁ * (gN : ℤ) + (c_d : ℤ) * (gN : ℤ) ^ 2 := by
      have h4 : 4 * (c_d : ℤ) = (d : ℤ) + 1 := by exact_mod_cast (show 4 * c_d = d + 1 by omega)
      have hdpos : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd_pos_of_mod8 hd_mod
      have : 4 * (u₁ ^ 2 + u₁ * (gN : ℤ) + (c_d : ℤ) * (gN : ℤ) ^ 2) =
          (2 * u₁ + (gN : ℤ)) ^ 2 + (d : ℤ) * (gN : ℤ) ^ 2 := by linear_combination ((gN : ℤ) ^ 2) * h4
      have hg2 : 0 < (gN : ℤ) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (2 * u₁ + (gN : ℤ))]
    refine ⟨(u₁ ^ 2 + u₁ * (gN : ℤ) + (c_d : ℤ) * (gN : ℤ) ^ 2).toNat, by omega, ?_⟩
    simpa [Int.toNat_of_nonneg hpos.le] using hprod
  set mN : ℕ := Nat.find hex_m
  have hmN_spec := Nat.find_spec hex_m
  have hmpos : (0 : ℤ) < (mN : ℤ) := by exact_mod_cast hmN_spec.1
  have hmI : ((mN : ℤ) : O) ∈ I := hmN_spec.2
  have hm_dvd_u : ∀ u : ℤ, (u : O) ∈ I → (mN : ℤ) ∣ u := by
    intro u huI
    set r : ℤ := u % (mN : ℤ)
    set q : ℤ := u / (mN : ℤ)
    have hr_nonneg : 0 ≤ r := Int.emod_nonneg u hmpos.ne'
    have hr_lt : r < (mN : ℤ) := Int.emod_lt_of_pos u hmpos
    have hdiff : (r : O) ∈ I := by
      have := Ideal.sub_mem I huI (Ideal.mul_mem_left I (q : O) hmI)
      have hu : u = (mN : ℤ) * q + r := (Int.mul_ediv_add_emod u (mN : ℤ)).symm
      have huO := congrArg (Int.cast : ℤ → O) hu
      dsimp only [O] at huO ⊢
      simp only [castO_add, castO_mul] at huO
      have heq : (u : NumberField.RingOfIntegers (QuadK d)) -
          (q : NumberField.RingOfIntegers (QuadK d)) * ((mN : ℤ) : NumberField.RingOfIntegers (QuadK d)) =
          (r : NumberField.RingOfIntegers (QuadK d)) := by linear_combination huO
      rwa [heq] at this
    by_contra hndvd
    have hr_pos : 0 < r.toNat := by
      have : r ≠ 0 := fun h => hndvd (Int.dvd_of_emod_eq_zero h)
      omega
    exact Nat.find_min hex_m (by omega : r.toNat < mN) ⟨hr_pos, by simpa [Int.toNat_of_nonneg hr_nonneg] using hdiff⟩
  -- 3. Show gN ∣ mN and gN ∣ u₁
  have hg_dvd_m : (gN : ℤ) ∣ (mN : ℤ) := by
    have hmul : ((0 : ℤ) : O) + ((mN : ℤ) : O) * omegaO hd_mod ∈ I := by
      simpa using Ideal.mul_mem_right (omegaO hd_mod) I hmI
    exact hg_dvd_v 0 (mN : ℤ) hmul
  have hg_dvd_u1 : (gN : ℤ) ∣ u₁ := by
    set c_d : ℕ := (d + 1) / 4
    have hmul : ((u₁ : O) + ((gN : ℤ) : O) * omegaO hd_mod) * omegaO hd_mod ∈ I :=
      Ideal.mul_mem_right _ I hu₁I
    have hrew : ((u₁ : O) + ((gN : ℤ) : O) * omegaO hd_mod) * omegaO hd_mod =
        ((-(gN : ℤ) * (c_d : ℤ) : ℤ) : O) + ((u₁ + (gN : ℤ) : ℤ) : O) * omegaO hd_mod := by
      have hsq := omegaO_sq hd_mod
      dsimp only [O, c_d]
      simp only [castO_add, castO_mul, castO_neg, castO_nat]
      linear_combination (gN : NumberField.RingOfIntegers (QuadK d)) * hsq
    rw [hrew] at hmul
    have hdvd := hg_dvd_v (-(gN : ℤ) * (c_d : ℤ)) (u₁ + (gN : ℤ)) hmul
    obtain ⟨t, ht⟩ := hdvd
    exact ⟨t - 1, by linarith⟩
  obtain ⟨a, ha_eq⟩ := hg_dvd_m
  obtain ⟨k, hk_eq⟩ := hg_dvd_u1
  have hapos : 0 < a := by nlinarith
  -- 4. Show a ∣ k^2 + k + (d+1)/4
  set c_d : ℕ := (d + 1) / 4
  have ha_dvd_norm : a ∣ (k ^ 2 + k + (c_d : ℤ)) := by
    have hmul : ((u₁ : O) + ((gN : ℤ) : O) * omegaO hd_mod) *
        (((k + 1 : ℤ) : O) - omegaO hd_mod) ∈ I := Ideal.mul_mem_right _ I hu₁I
    have hrew : ((u₁ : O) + ((gN : ℤ) : O) * omegaO hd_mod) *
        (((k + 1 : ℤ) : O) - omegaO hd_mod) =
        (((gN : ℤ) * (k ^ 2 + k + (c_d : ℤ)) : ℤ) : O) := by
      have hsq := omegaO_sq hd_mod
      have hu1O := congrArg (Int.cast : ℤ → O) hk_eq
      dsimp only [O, c_d] at hu1O ⊢
      simp only [castO_add, castO_mul, castO_pow, castO_nat, castO_one] at hu1O ⊢
      linear_combination ((k : NumberField.RingOfIntegers (QuadK d)) + 1 - omegaO hd_mod) * hu1O -
        (gN : NumberField.RingOfIntegers (QuadK d)) * hsq
    rw [hrew] at hmul
    obtain ⟨c, hc⟩ := hm_dvd_u _ hmul
    refine ⟨c, ?_⟩
    rw [ha_eq] at hc
    exact mul_left_cancel₀ hgpos.ne' (by linarith)
  obtain ⟨c, hc_eq⟩ := ha_dvd_norm
  have h4 : 4 * (c_d : ℤ) = (d : ℤ) + 1 := by exact_mod_cast (show 4 * c_d = d + 1 by omega)
  have hdisc : 4 * a * c - (2 * k + 1) ^ 2 = (d : ℤ) := by linear_combination -4 * hc_eq + h4
  have hcpos : 0 < c := by
    have hdpos : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd_pos_of_mod8 hd_mod
    nlinarith [sq_nonneg (2 * k + 1)]
  let f : BQF d := ⟨a, 2 * k + 1, c, hapos, hcpos, hdisc⟩
  have hkf : (f.b - 1) / 2 = k := by dsimp only [f]; omega
  refine ⟨(gN : ℤ), f, hgpos, ?_⟩
  apply le_antisymm
  · intro z hzI
    obtain ⟨u, v, rfl⟩ := exists_int_add_int_mul_omegaO hd_sf hd_mod z
    obtain ⟨y, hy⟩ := hg_dvd_v u v hzI
    have hrem : ((u - y * u₁ : ℤ) : O) ∈ I := by
      have := Ideal.sub_mem I hzI (Ideal.mul_mem_left I (y : O) hu₁I)
      have hvO := congrArg (Int.cast : ℤ → O) hy
      dsimp only [O] at hvO this ⊢
      simp only [castO_mul] at hvO
      have heq : (u : NumberField.RingOfIntegers (QuadK d)) +
          (v : NumberField.RingOfIntegers (QuadK d)) * omegaO hd_mod -
          (y : NumberField.RingOfIntegers (QuadK d)) *
            ((u₁ : NumberField.RingOfIntegers (QuadK d)) +
              ((gN : ℤ) : NumberField.RingOfIntegers (QuadK d)) * omegaO hd_mod) =
          ((u - y * u₁ : ℤ) : NumberField.RingOfIntegers (QuadK d)) := by
        simp only [castO_sub, castO_mul]
        linear_combination hvO * omegaO hd_mod
      rwa [heq] at this
    obtain ⟨x, hx⟩ := hm_dvd_u _ hrem
    have hrew : (u : O) + (v : O) * omegaO hd_mod =
        ((gN : ℤ) : O) * ((x : O) * (f.a : O) + (y : O) * gammaOfBQF hd_mod f) := by
      have huO := congrArg (Int.cast : ℤ → O) hx
      have hvO := congrArg (Int.cast : ℤ → O) hy
      have hmO := congrArg (Int.cast : ℤ → O) ha_eq
      have hu1O := congrArg (Int.cast : ℤ → O) hk_eq
      dsimp only [gammaOfBQF, O, f] at huO hvO hmO hu1O ⊢
      rw [show (2 * k + 1 - 1) / 2 = k by omega]
      simp only [castO_sub, castO_mul, castO_nat] at huO hvO hmO hu1O ⊢
      linear_combination huO + (x : NumberField.RingOfIntegers (QuadK d)) * hmO +
        (y : NumberField.RingOfIntegers (QuadK d)) * hu1O + omegaO hd_mod * hvO
    rw [hrew]
    exact Ideal.mul_mem_mul (Ideal.subset_span rfl) ((mem_idealOfBQF_iff hd_sf hd_mod f _).mpr ⟨x, y, rfl⟩)
  · rw [Ideal.mul_le]
    intro r hr z hz
    rw [Ideal.mem_span_singleton] at hr
    obtain ⟨w, rfl⟩ := hr
    obtain ⟨x, y, rfl⟩ := (mem_idealOfBQF_iff hd_sf hd_mod f z).mp hz
    have hrew : ((gN : ℤ) : O) * ((x : O) * (f.a : O) + (y : O) * gammaOfBQF hd_mod f) =
        (x : O) * ((mN : ℤ) : O) + (y : O) * ((u₁ : O) + ((gN : ℤ) : O) * omegaO hd_mod) := by
      have hmO := congrArg (Int.cast : ℤ → O) ha_eq
      have hu1O := congrArg (Int.cast : ℤ → O) hk_eq
      dsimp only [gammaOfBQF, O, f] at hmO hu1O ⊢
      rw [show (2 * k + 1 - 1) / 2 = k by omega]
      simp only [castO_mul, castO_nat] at hmO hu1O ⊢
      linear_combination -(x : NumberField.RingOfIntegers (QuadK d)) * hmO -
        (y : NumberField.RingOfIntegers (QuadK d)) * hu1O
    have hmem : ((gN : ℤ) : O) * ((x : O) * (f.a : O) + (y : O) * gammaOfBQF hd_mod f) ∈ I := by
      rw [hrew]
      exact Ideal.add_mem I (Ideal.mul_mem_left I _ hmI) (Ideal.mul_mem_left I _ hu₁I)
    rw [mul_comm ((gN : ℤ) : O) w, mul_assoc]
    exact Ideal.mul_mem_left I w hmem

/-!
### Section 3: Coprime Representative and Genus Homomorphism
-/

/-- CRT helper over a finite set of distinct primes. -/
private lemma crt_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : ℕ → ℕ) : ∃ x : ℕ, ∀ p ∈ S, x ≡ a p [MOD p] := by
  classical
  induction S using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | @insert p s hps ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    obtain ⟨y, hy⟩ := ih hs
    set M : ℕ := ∏ q ∈ s, q
    have hcop : Nat.Coprime p M := by
      rw [hp.coprime_iff_not_dvd]
      intro hdvd
      obtain ⟨q, hqs, hpq⟩ := (Prime.dvd_finset_prod_iff hp.prime _).mp hdvd
      exact hps ((Nat.prime_dvd_prime_iff_eq hp (hs q hqs)).mp hpq ▸ hqs)
    let crt := Nat.chineseRemainder hcop (a p) y
    refine ⟨crt.1, fun q hq => ?_⟩
    rw [Finset.mem_insert] at hq
    rcases hq with rfl | hqs
    · exact crt.2.1
    · exact (crt.2.2.of_dvd (Finset.dvd_prod_of_mem _ hqs)).trans (hy q hqs)

/-- Every `f : BQF d` is `SL₂(ℤ)`-equivalent to a form `f'` with `Nat.Coprime f'.a.toNat d`. -/
lemma exists_sl2Equiv_coprime (hd_sf : Squarefree d) (hd_mod : d % 8 = 3) (f : BQF d) :
    ∃ f' : BQF d, SL2Equiv f f' ∧ Nat.Coprime f'.a.toNat d := by
  have hS : ∀ p ∈ d.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  let xp : ℕ → ℕ := fun p => if ¬ ((p : ℤ) ∣ f.a) then 1 else if ¬ ((p : ℤ) ∣ f.c) then 0 else 1
  let yp : ℕ → ℕ := fun p => if ¬ ((p : ℤ) ∣ f.a) then 0 else if ¬ ((p : ℤ) ∣ f.c) then 1 else 1
  obtain ⟨x₀, hx₀⟩ := crt_primes hS xp
  obtain ⟨y₀, hy₀⟩ := crt_primes hS yp
  have hndvd₀ : ∀ p ∈ d.primeFactors, ¬ ((p : ℤ) ∣ f.eval x₀ y₀) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
    have hnotall : ¬ ((p : ℤ) ∣ f.a ∧ (p : ℤ) ∣ f.b ∧ (p : ℤ) ∣ f.c) := by
      rintro ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨c', hc'⟩⟩
      have hp2 : (p : ℤ) ^ 2 ∣ (d : ℤ) := ⟨4 * a' * c' - b' ^ 2, by rw [← f.hdisc, ha', hb', hc']; ring⟩
      have hp2N : p * p ∣ d := by
        have : ((p * p : ℕ) : ℤ) ∣ (d : ℤ) := by simpa [sq] using hp2
        exact_mod_cast this
      exact hpp.not_isUnit (hd_sf p hp2N)
    have hxmod : (x₀ : ZMod p) = (xp p : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff x₀ (xp p) p).mpr (hx₀ p hp)
    have hymod : (y₀ : ZMod p) = (yp p : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff y₀ (yp p) p).mpr (hy₀ p hp)
    intro hdvd
    have h0 : ((f.eval x₀ y₀ : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    have h0' : ((f.eval (xp p) (yp p) : ℤ) : ZMod p) = 0 := by
      dsimp only [eval] at h0 ⊢; push_cast at h0 ⊢; rw [← hxmod, ← hymod]; exact h0
    have hdvd' : (p : ℤ) ∣ f.eval (xp p) (yp p) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0'
    by_cases ha : (p : ℤ) ∣ f.a
    · by_cases hc : (p : ℤ) ∣ f.c
      · have hxp : xp p = 1 := by simp [xp, ha, hc]
        have hyp : yp p = 1 := by simp [yp, ha, hc]
        rw [hxp, hyp] at hdvd'
        simp only [eval, Nat.cast_one, one_pow, mul_one] at hdvd'
        have hb : (p : ℤ) ∣ f.b := by
          have := dvd_sub (dvd_sub hdvd' ha) hc
          simpa [show f.a + f.b + f.c - f.a - f.c = f.b by ring] using this
        exact hnotall ⟨ha, hb, hc⟩
      · have hxp : xp p = 0 := by simp [xp, ha, hc]
        have hyp : yp p = 1 := by simp [yp, ha, hc]
        rw [hxp, hyp] at hdvd'
        simp only [eval, Nat.cast_zero, Nat.cast_one, zero_pow two_ne_zero, mul_zero, zero_add, one_pow, mul_one] at hdvd'
        exact hc hdvd'
    · have hxp : xp p = 1 := by simp [xp, ha]
      have hyp : yp p = 0 := by simp [yp, ha]
      rw [hxp, hyp] at hdvd'
      simp only [eval, Nat.cast_one, Nat.cast_zero, one_pow, mul_one, mul_zero, zero_pow two_ne_zero, add_zero] at hdvd'
      exact ha hdvd'
  have hd_gt1 : 1 < d := by omega
  obtain ⟨p₀, hp₀, hp₀d⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  have hp₀mem : p₀ ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp₀, hp₀d, by omega⟩
  have hxy_ne : x₀ ≠ 0 ∨ y₀ ≠ 0 := by
    by_contra h; push Not at h
    have := hndvd₀ p₀ hp₀mem
    rw [h.1, h.2] at this; simp [eval] at this
  set g : ℕ := Nat.gcd x₀ y₀
  have hgpos : 0 < g := Nat.pos_of_ne_zero (by intro h; rw [Nat.gcd_eq_zero_iff] at h; omega)
  set x : ℤ := ((x₀ / g : ℕ) : ℤ)
  set y : ℤ := ((y₀ / g : ℕ) : ℤ)
  have hcop_xy : Int.gcd x y = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact Nat.coprime_div_gcd_div_gcd hgpos
  have hndvd : ∀ p ∈ d.primeFactors, ¬ ((p : ℤ) ∣ f.eval x y) := by
    intro p hp hdvd
    apply hndvd₀ p hp
    have hx0 : (x₀ : ℤ) = (g : ℤ) * x := by
      dsimp only [x, g]; exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left x₀ y₀)).symm
    have hy0 : (y₀ : ℤ) = (g : ℤ) * y := by
      dsimp only [y, g]; exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right x₀ y₀)).symm
    have hev : f.eval x₀ y₀ = (g : ℤ) ^ 2 * f.eval x y := by
      dsimp only [eval]; rw [hx0, hy0]; ring
    rw [hev]; exact dvd_mul_of_dvd_right hdvd _
  set q : ℤ := -Int.gcdB x y
  set s : ℤ := Int.gcdA x y
  have hdet : x * s - q * y = 1 := by
    have := Int.gcd_eq_gcd_ab x y; rw [hcop_xy, Nat.cast_one] at this; dsimp only [q, s]; linarith
  have hxy_nz : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h; push Not at h; rw [h.1, h.2] at hdet; norm_num at hdet
  have hqs_nz : q ≠ 0 ∨ s ≠ 0 := by
    by_contra h; push Not at h; rw [h.1, h.2] at hdet; norm_num at hdet
  have hd_pos : 0 < d := by omega
  let f' : BQF d :=
    ⟨f.eval x y, 2 * f.a * x * q + f.b * (x * s + q * y) + 2 * f.c * y * s, f.eval q s,
      eval_pos hd_pos f hxy_nz, eval_pos hd_pos f hqs_nz, by
        dsimp only [eval]
        have h1 : 4 * (f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2) * (f.a * q ^ 2 + f.b * q * s + f.c * s ^ 2) -
            (2 * f.a * x * q + f.b * (x * s + q * y) + 2 * f.c * y * s) ^ 2 =
            (4 * f.a * f.c - f.b ^ 2) * (x * s - q * y) ^ 2 := by ring
        rw [h1, hdet, one_pow, mul_one, f.hdisc]⟩
  refine ⟨f', ⟨!![x, q; y, s], by simp [Matrix.det_fin_two, hdet], fun u v => ?_⟩, ?_⟩
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Fin.isValue, eval, f']
    ring
  · rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpf : p ∣ f'.a.toNat := dvd_trans hpg (Nat.gcd_dvd_left _ _)
    have hpd : p ∣ d := dvd_trans hpg (Nat.gcd_dvd_right _ _)
    have hpmem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩
    apply hndvd p hpmem
    have : ((p : ℕ) : ℤ) ∣ ((f'.a.toNat : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hpf
    rwa [Int.toNat_of_nonneg f'.ha.le] at this

/-- For an odd prime `p ∥ d` and `4 * N = r^2 + d * v^2` (`N > 0`), the Legendre symbol of the
prime-to-`p` part of `N` depends ONLY on the parity of `v_p(N)`. -/
private lemma legendre_of_four_mul_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpd : p ∣ d) (hp2d : ¬ p ^ 2 ∣ d) :
    ∀ (k : ℕ) (m : ℕ) (r v : ℤ), ¬ p ∣ m → 0 < m →
      4 * ((p ^ k * m : ℕ) : ℤ) = r ^ 2 + (d : ℤ) * v ^ 2 →
      legendreSym p (m : ℤ) = if Even k then 1 else legendreSym p ((d / p : ℕ) : ℤ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m r v hpm hmpos heq
    have hp : p.Prime := Fact.out
    have hpdZ : (p : ℤ) ∣ (d : ℤ) := Int.natCast_dvd_natCast.mpr hpd
    have h4m_ndvd : ¬ (p : ℤ) ∣ (4 * (m : ℤ)) := by
      intro hdvd
      rcases (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hdvd with h4 | hm'
      · have h4N : p ∣ 4 := by exact_mod_cast h4
        have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4N)
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
      · exact hpm (Int.natCast_dvd_natCast.mp hm')
    match k with
    | 0 =>
      simp only [Even.zero, ↓reduceIte, pow_zero, one_mul] at heq ⊢
      have hmod : ((4 * (m : ℤ) : ℤ) : ZMod p) = ((r : ZMod p)) ^ 2 := by
        have hcast := congrArg (fun w : ℤ => (w : ZMod p)) heq
        have hd0 : (d : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).mpr hpd
        push_cast at hcast ⊢; rw [hd0, zero_mul, add_zero] at hcast; exact hcast
      have hr_ne : (r : ZMod p) ≠ 0 := by
        intro hr0; rw [hr0, zero_pow two_ne_zero] at hmod
        exact h4m_ndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hmod)
      have hleg4m : legendreSym p (4 * (m : ℤ)) = 1 := by
        rw [legendreSym.eq_one_iff]
        · exact ⟨(r : ZMod p), by rw [hmod, sq]⟩
        · intro h0; exact h4m_ndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0)
      have hleg4 : legendreSym p (4 : ℤ) = 1 := by
        rw [show (4 : ℤ) = 2 * 2 by norm_num, legendreSym.mul, ← sq, legendreSym.sq_one]
        intro h0
        have h2 : p ∣ 2 := by
          have := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp h0
          exact_mod_cast this
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      rw [legendreSym.mul, hleg4, one_mul] at hleg4m
      exact hleg4m
    | 1 =>
      have hneven : ¬ Even (1 : ℕ) := by decide
      simp only [hneven, ↓reduceIte, pow_one] at heq ⊢
      have hpr : (p : ℤ) ∣ r := by
        have hpr2 : (p : ℤ) ∣ r ^ 2 := by
          have : r ^ 2 = (p : ℤ) * (4 * (m : ℤ) - ((d / p : ℕ) : ℤ) * v ^ 2) := by
            have hd_eq : (d : ℤ) = (p : ℤ) * ((d / p : ℕ) : ℤ) := by
              exact_mod_cast (Nat.mul_div_cancel' hpd).symm
            push_cast at heq; linear_combination -heq - v ^ 2 * hd_eq
          exact ⟨_, this⟩
        exact (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hpr2
      obtain ⟨r₁, rfl⟩ := hpr
      have hd_eq : (d : ℤ) = (p : ℤ) * ((d / p : ℕ) : ℤ) := by
        exact_mod_cast (Nat.mul_div_cancel' hpd).symm
      have hdiv : 4 * (m : ℤ) = (p : ℤ) * r₁ ^ 2 + ((d / p : ℕ) : ℤ) * v ^ 2 := by
        apply mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)
        push_cast at heq; linear_combination heq + v ^ 2 * hd_eq
      have hmod : ((4 * (m : ℤ) : ℤ) : ZMod p) = ((((d / p : ℕ) : ℤ) * v ^ 2 : ℤ) : ZMod p) := by
        have hcast := congrArg (fun w : ℤ => (w : ZMod p)) hdiv
        push_cast at hcast ⊢
        rw [ZMod.natCast_self, zero_mul, zero_add] at hcast
        exact hcast
      have hv_ne : (v : ZMod p) ≠ 0 := by
        intro hv0; push_cast at hmod; rw [hv0, zero_pow two_ne_zero, mul_zero] at hmod
        exact h4m_ndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (by push_cast; exact hmod))
      have hleg_eq : legendreSym p (4 * (m : ℤ)) = legendreSym p (((d / p : ℕ) : ℤ) * v ^ 2) := by
        unfold legendreSym; rw [hmod]
      have hleg4 : legendreSym p (4 : ℤ) = 1 := by
        rw [show (4 : ℤ) = 2 * 2 by norm_num, legendreSym.mul, ← sq, legendreSym.sq_one]
        intro h0
        have h2 : p ∣ 2 := by
          have := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp h0
          exact_mod_cast this
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      have hlegv2 : legendreSym p (v ^ 2) = 1 := by
        rw [sq, legendreSym.mul, ← sq, legendreSym.sq_one p hv_ne]
      rw [legendreSym.mul, hleg4, one_mul, legendreSym.mul, hlegv2, mul_one] at hleg_eq
      exact hleg_eq
    | k' + 2 =>
      have hpr : (p : ℤ) ∣ r := by
        have hpr2 : (p : ℤ) ∣ r ^ 2 := by
          have hp_lhs : (p : ℤ) ∣ 4 * ((p ^ (k' + 2) * m : ℕ) : ℤ) := by
            push_cast
            exact ⟨4 * (p : ℤ) ^ (k' + 1) * (m : ℤ), by ring⟩
          have : r ^ 2 = 4 * ((p ^ (k' + 2) * m : ℕ) : ℤ) - (d : ℤ) * v ^ 2 := by linarith
          rw [this]
          exact dvd_sub hp_lhs (dvd_mul_of_dvd_left hpdZ _)
        exact (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hpr2
      obtain ⟨r₁, rfl⟩ := hpr
      have hd_eq : (d : ℤ) = (p : ℤ) * ((d / p : ℕ) : ℤ) := by
        exact_mod_cast (Nat.mul_div_cancel' hpd).symm
      have hpv : (p : ℤ) ∣ v := by
        have hp_dv2 : (p : ℤ) ∣ ((d / p : ℕ) : ℤ) * v ^ 2 := by
          have : ((d / p : ℕ) : ℤ) * v ^ 2 = (p : ℤ) * (4 * (p : ℤ) ^ k' * (m : ℤ) - r₁ ^ 2) := by
            apply mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)
            push_cast at heq; linear_combination -heq - v ^ 2 * hd_eq
          exact ⟨_, this⟩
        rcases (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hp_dv2 with hdp | hv2
        · exfalso; apply hp2d
          have hdpN : p ∣ d / p := Int.natCast_dvd_natCast.mp hdp
          obtain ⟨t, ht⟩ := hdpN
          exact ⟨t, by rw [← Nat.mul_div_cancel' hpd, ht]; ring⟩
        · exact (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hv2
      obtain ⟨v₁, rfl⟩ := hpv
      have heq' : 4 * ((p ^ k' * m : ℕ) : ℤ) = r₁ ^ 2 + (d : ℤ) * v₁ ^ 2 := by
        apply mul_left_cancel₀ (show ((p : ℤ) ^ 2) ≠ 0 by exact pow_ne_zero 2 (by exact_mod_cast hp.ne_zero))
        push_cast at heq ⊢; linear_combination heq
      have hih := ih k' (by omega) m r₁ v₁ hpm hmpos heq'
      have hev_iff : Even (k' + 2) ↔ Even k' := ⟨fun ⟨t, ht⟩ => ⟨t - 1, by omega⟩, fun ⟨t, ht⟩ => ⟨t + 1, by omega⟩⟩
      simpa [hev_iff] using hih

lemma legendre_absNorm_eq_of_classGroup_eq (hd_sf : Squarefree d) (hd_mod : d % 8 = 3) :
    haveI := quadK_numberField (d := d)
    ∀ (I₁ I₂ : (Ideal (NumberField.RingOfIntegers (QuadK d)))⁰),
      ClassGroup.mk0 I₁ = ClassGroup.mk0 I₂ →
      ∀ (p : ℕ) (hp : p ∈ d.primeFactors),
        haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
        ¬ p ∣ Ideal.absNorm (I₁ : Ideal (NumberField.RingOfIntegers (QuadK d))) →
        ¬ p ∣ Ideal.absNorm (I₂ : Ideal (NumberField.RingOfIntegers (QuadK d))) →
        legendreSym p (Ideal.absNorm (I₁ : Ideal (NumberField.RingOfIntegers (QuadK d))) : ℤ) =
        legendreSym p (Ideal.absNorm (I₂ : Ideal (NumberField.RingOfIntegers (QuadK d))) : ℤ) := by
  haveI := quadK_numberField (d := d)
  intro I₁ I₂ heq p hp hp1 hp2
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
  have hp2_ne : p ≠ 2 := by intro h; subst h; omega
  have hp2d : ¬ p ^ 2 ∣ d := fun h => hpp.not_isUnit (hd_sf p (by simpa [sq] using h))
  rw [ClassGroup.mk0_eq_mk0_iff] at heq
  obtain ⟨u, v, hu0, hv0, huv⟩ := heq
  have hN := congrArg Ideal.absNorm huv
  rw [map_mul, map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at hN
  set Nu : ℕ := (Algebra.norm ℤ u).natAbs
  set Nv : ℕ := (Algebra.norm ℤ v).natAbs
  set N1 : ℕ := Ideal.absNorm (I₁ : Ideal (NumberField.RingOfIntegers (QuadK d)))
  set N2 : ℕ := Ideal.absNorm (I₂ : Ideal (NumberField.RingOfIntegers (QuadK d)))
  have hNu_pos : 0 < Nu := Int.natAbs_pos.mpr (norm_omegaO_pos hd_sf hd_mod hu0).ne'
  have hNv_pos : 0 < Nv := Int.natAbs_pos.mpr (norm_omegaO_pos hd_sf hd_mod hv0).ne'
  have hN1_pos : 0 < N1 := Nat.pos_of_ne_zero (fun h => hp1 (h ▸ dvd_zero p))
  have hN2_pos : 0 < N2 := Nat.pos_of_ne_zero (fun h => hp2 (h ▸ dvd_zero p))
  set ku : ℕ := padicValNat p Nu
  set kv : ℕ := padicValNat p Nv
  have hk_eq : ku = kv := by
    have hval := congrArg (padicValNat p) hN
    rw [padicValNat.mul hNu_pos.ne' hN1_pos.ne', padicValNat.mul hNv_pos.ne' hN2_pos.ne',
      padicValNat.eq_zero_of_not_dvd hp1, padicValNat.eq_zero_of_not_dvd hp2, add_zero, add_zero] at hval
    exact hval
  have hpu : p ^ ku ∣ Nu := pow_padicValNat_dvd
  have hpv : p ^ kv ∣ Nv := pow_padicValNat_dvd
  set mu : ℕ := Nu / p ^ ku
  set mv : ℕ := Nv / p ^ kv
  have hNu_eq : p ^ ku * mu = Nu := Nat.mul_div_cancel' hpu
  have hNv_eq : p ^ kv * mv = Nv := Nat.mul_div_cancel' hpv
  have hmu_pos : 0 < mu := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hNu_eq; omega)
  have hmv_pos : 0 < mv := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hNv_eq; omega)
  have hpmu : ¬ p ∣ mu := by
    intro h
    have hpow : p ^ (ku + 1) ∣ Nu := by
      obtain ⟨t, ht⟩ := h; exact ⟨t, by rw [← hNu_eq, ht]; ring⟩
    have hle := (padicValNat_dvd_iff_le hNu_pos.ne').mp hpow
    omega
  have hpmv : ¬ p ∣ mv := by
    intro h
    have hpow : p ^ (kv + 1) ∣ Nv := by
      obtain ⟨t, ht⟩ := h; exact ⟨t, by rw [← hNv_eq, ht]; ring⟩
    have hle := (padicValNat_dvd_iff_le hNv_pos.ne').mp hpow
    omega
  have hmeq : mu * N1 = mv * N2 := by
    apply mul_left_cancel₀ (pow_ne_zero ku hpp.ne_zero)
    calc p ^ ku * (mu * N1) = (p ^ ku * mu) * N1 := by ring
      _ = Nu * N1 := by rw [hNu_eq]
      _ = Nv * N2 := hN
      _ = (p ^ kv * mv) * N2 := by rw [hNv_eq]
      _ = p ^ ku * (mv * N2) := by rw [hk_eq]; ring
  obtain ⟨xu, yu, hxu⟩ := exists_int_add_int_mul_omegaO hd_sf hd_mod u
  obtain ⟨xv, yv, hxv⟩ := exists_int_add_int_mul_omegaO hd_sf hd_mod v
  have h4u : 4 * ((p ^ ku * mu : ℕ) : ℤ) = (2 * xu + yu) ^ 2 + (d : ℤ) * yu ^ 2 := by
    rw [hNu_eq, show (Nu : ℤ) = Algebra.norm ℤ u from Int.natAbs_of_nonneg (norm_omegaO_nonneg hd_sf hd_mod u), hxu]
    exact four_mul_norm_omegaO hd_mod xu yu
  have h4v : 4 * ((p ^ kv * mv : ℕ) : ℤ) = (2 * xv + yv) ^ 2 + (d : ℤ) * yv ^ 2 := by
    rw [hNv_eq, show (Nv : ℤ) = Algebra.norm ℤ v from Int.natAbs_of_nonneg (norm_omegaO_nonneg hd_sf hd_mod v), hxv]
    exact four_mul_norm_omegaO hd_mod xv yv
  have hleg_u := legendre_of_four_mul_eq hp2_ne hpd hp2d ku mu (2 * xu + yu) yu hpmu hmu_pos h4u
  have hleg_v := legendre_of_four_mul_eq hp2_ne hpd hp2d kv mv (2 * xv + yv) yv hpmv hmv_pos h4v
  have hleg_uv : legendreSym p (mu : ℤ) = legendreSym p (mv : ℤ) := by rw [hleg_u, hleg_v, hk_eq]
  have hleg_ne : legendreSym p (mu : ℤ) ≠ 0 := by
    intro h0
    rw [legendreSym.eq_zero_iff] at h0
    exact hpmu ((CharP.cast_eq_zero_iff (ZMod p) p mu).mp (by simpa using h0))
  have hprod : legendreSym p (mu : ℤ) * legendreSym p (N1 : ℤ) =
      legendreSym p (mv : ℤ) * legendreSym p (N2 : ℤ) := by
    rw [← legendreSym.mul, ← legendreSym.mul]
    exact congrArg (legendreSym p) (by exact_mod_cast hmeq)
  rw [← hleg_uv] at hprod
  exact mul_left_cancel₀ hleg_ne hprod

/-- Every ideal class contains an ideal of norm coprime to `d`. -/
lemma exists_coprime_rep (hd_sf : Squarefree d) (hd_mod : d % 8 = 3) :
    haveI := quadK_numberField (d := d)
    ∀ c : ClassGroup (NumberField.RingOfIntegers (QuadK d)),
      ∃ f : BQF d,
        ClassGroup.mk0 ⟨idealOfBQF hd_mod f, mem_nonZeroDivisors_of_ne_zero (idealOfBQF_ne_bot hd_mod f)⟩ = c ∧
        Nat.Coprime f.a.toNat d := by
  haveI := quadK_numberField (d := d)
  intro c
  obtain ⟨I, hIc⟩ := ClassGroup.mk0_surjective c
  have hIne : (I : Ideal (NumberField.RingOfIntegers (QuadK d))) ≠ ⊥ :=
    nonZeroDivisors.ne_zero I.2
  obtain ⟨g, f, hgpos, hIeq⟩ := exists_bqf_of_ideal hd_sf hd_mod I hIne
  obtain ⟨f', hff', hcop⟩ := exists_sl2Equiv_coprime hd_sf hd_mod f
  refine ⟨f', ?_, hcop⟩
  rw [← sl2Equiv_imp_classGroup_eq hd_sf hd_mod hff', ← hIc]
  rw [ClassGroup.mk0_eq_mk0_iff]
  have hgne : ((g : ℤ) : NumberField.RingOfIntegers (QuadK d)) ≠ 0 := by
    intro h0
    have := congrArg (fun z : NumberField.RingOfIntegers (QuadK d) => (z : QuadK d).re) h0
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap,
      map_intCast, map_zero] at this
    simp at this
    have : g = 0 := by exact_mod_cast this
    linarith
  exact ⟨(g : NumberField.RingOfIntegers (QuadK d)), 1, hgne, one_ne_zero, by simpa using hIeq.symm⟩

/-- Helper turning a nonzero Legendre symbol (`±1`) into a unit in `ℤˣ`. -/
private def legendreUnit (p : ℕ) [Fact p.Prime] (a : ℤ) (_h : legendreSym p a ≠ 0) : ℤˣ :=
  if legendreSym p a = 1 then 1 else -1

private lemma legendreUnit_val (p : ℕ) [Fact p.Prime] (a : ℤ) (h : legendreSym p a ≠ 0) :
    ((legendreUnit p a h : ℤˣ) : ℤ) = legendreSym p a := by
  dsimp only [legendreUnit]
  have hne : (a : ZMod p) ≠ 0 := fun h0 => h ((legendreSym.eq_zero_iff p a).mpr h0)
  rcases legendreSym.eq_one_or_neg_one p hne with h1 | h1
  · rw [if_pos h1, h1]; rfl
  · rw [if_neg (by rw [h1]; decide), h1]; rfl

/-- The genus homomorphism `ClassGroup (𝓞 (QuadK d)) →* (d.primeFactors → ℤˣ)`. -/
noncomputable def genusHom (hd_sf : Squarefree d) (hd_mod : d % 8 = 3) :
    haveI := quadK_numberField (d := d)
    ClassGroup (NumberField.RingOfIntegers (QuadK d)) →* (d.primeFactors → ℤˣ) := by
  haveI := quadK_numberField (d := d)
  refine
    { toFun := fun c p =>
        let f := (exists_coprime_rep hd_sf hd_mod c).choose
        haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
        have hndvd : ¬ p.1 ∣ f.a.toNat := by
          have hcop := (exists_coprime_rep hd_sf hd_mod c).choose_spec.2
          have hpd := Nat.dvd_of_mem_primeFactors p.2
          intro hpf
          have := Nat.dvd_gcd hpf hpd
          rw [hcop] at this
          exact (Nat.prime_of_mem_primeFactors p.2).not_dvd_one this
        legendreUnit p.1 f.a (by
          intro h0
          rw [legendreSym.eq_zero_iff] at h0
          have hdvdZ := (ZMod.intCast_zmod_eq_zero_iff_dvd f.a p.1).mp h0
          rw [← Int.toNat_of_nonneg f.ha.le] at hdvdZ
          exact hndvd (Int.natCast_dvd_natCast.mp hdvdZ))
      map_one' := by
        ext p
        haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
        set f := (exists_coprime_rep hd_sf hd_mod 1).choose
        have hf_eq := (exists_coprime_rep hd_sf hd_mod 1).choose_spec.1
        have hf_cop := (exists_coprime_rep hd_sf hd_mod 1).choose_spec.2
        have hndvd : ¬ p.1 ∣ Ideal.absNorm (idealOfBQF hd_mod f) := by
          rw [absNorm_idealOfBQF hd_sf hd_mod f]
          intro hpf
          have := Nat.dvd_gcd hpf (Nat.dvd_of_mem_primeFactors p.2)
          rw [hf_cop] at this
          exact (Nat.prime_of_mem_primeFactors p.2).not_dvd_one this
        have htop_ndvd : ¬ p.1 ∣ Ideal.absNorm ((1 : (Ideal (NumberField.RingOfIntegers (QuadK d)))⁰) :
            Ideal (NumberField.RingOfIntegers (QuadK d))) := by
          change ¬ p.1 ∣ Ideal.absNorm (1 : Ideal (NumberField.RingOfIntegers (QuadK d)))
          rw [Ideal.one_eq_top, Ideal.absNorm_top]
          exact (Nat.prime_of_mem_primeFactors p.2).not_dvd_one
        have h1eq : (1 : ClassGroup (NumberField.RingOfIntegers (QuadK d))) =
            ClassGroup.mk0 1 := (map_one _).symm
        have hleg := legendre_absNorm_eq_of_classGroup_eq hd_sf hd_mod
          ⟨idealOfBQF hd_mod f, mem_nonZeroDivisors_of_ne_zero (idealOfBQF_ne_bot hd_mod f)⟩
          1 (hf_eq.trans h1eq) p.1 p.2 hndvd htop_ndvd
        change legendreSym p.1 (Ideal.absNorm (idealOfBQF hd_mod f) : ℤ) =
          legendreSym p.1 (Ideal.absNorm (1 : Ideal (NumberField.RingOfIntegers (QuadK d))) : ℤ) at hleg
        rw [absNorm_idealOfBQF hd_sf hd_mod f, Int.toNat_of_nonneg f.ha.le, Ideal.one_eq_top, Ideal.absNorm_top] at hleg
        dsimp only
        rw [legendreUnit_val, hleg]
        simp
      map_mul' := fun c₁ c₂ => by
        ext p
        haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
        set f₁ := (exists_coprime_rep hd_sf hd_mod c₁).choose
        set f₂ := (exists_coprime_rep hd_sf hd_mod c₂).choose
        set f₁₂ := (exists_coprime_rep hd_sf hd_mod (c₁ * c₂)).choose
        have hf₁_eq := (exists_coprime_rep hd_sf hd_mod c₁).choose_spec.1
        have hf₂_eq := (exists_coprime_rep hd_sf hd_mod c₂).choose_spec.1
        have hf₁₂_eq := (exists_coprime_rep hd_sf hd_mod (c₁ * c₂)).choose_spec.1
        have hf₁_cop := (exists_coprime_rep hd_sf hd_mod c₁).choose_spec.2
        have hf₂_cop := (exists_coprime_rep hd_sf hd_mod c₂).choose_spec.2
        have hf₁₂_cop := (exists_coprime_rep hd_sf hd_mod (c₁ * c₂)).choose_spec.2
        have hnd : ∀ (f : BQF d), Nat.Coprime f.a.toNat d → ¬ p.1 ∣ Ideal.absNorm (idealOfBQF hd_mod f) := by
          intro f hcop hpf
          rw [absNorm_idealOfBQF hd_sf hd_mod f] at hpf
          have := Nat.dvd_gcd hpf (Nat.dvd_of_mem_primeFactors p.2)
          rw [hcop] at this
          exact (Nat.prime_of_mem_primeFactors p.2).not_dvd_one this
        have hnd1 := hnd f₁ hf₁_cop
        have hnd2 := hnd f₂ hf₂_cop
        have hnd12 := hnd f₁₂ hf₁₂_cop
        let I₁ : (Ideal (NumberField.RingOfIntegers (QuadK d)))⁰ :=
          ⟨idealOfBQF hd_mod f₁, mem_nonZeroDivisors_of_ne_zero (idealOfBQF_ne_bot hd_mod f₁)⟩
        let I₂ : (Ideal (NumberField.RingOfIntegers (QuadK d)))⁰ :=
          ⟨idealOfBQF hd_mod f₂, mem_nonZeroDivisors_of_ne_zero (idealOfBQF_ne_bot hd_mod f₂)⟩
        let I₁₂ : (Ideal (NumberField.RingOfIntegers (QuadK d)))⁰ :=
          ⟨idealOfBQF hd_mod f₁₂, mem_nonZeroDivisors_of_ne_zero (idealOfBQF_ne_bot hd_mod f₁₂)⟩
        have hnd_mul : ¬ p.1 ∣ Ideal.absNorm ((I₁ * I₂ : (Ideal (NumberField.RingOfIntegers (QuadK d)))⁰) :
            Ideal (NumberField.RingOfIntegers (QuadK d))) := by
          change ¬ p.1 ∣ Ideal.absNorm (idealOfBQF hd_mod f₁ * idealOfBQF hd_mod f₂)
          rw [map_mul]
          intro h
          rcases (Nat.prime_of_mem_primeFactors p.2).dvd_mul.mp h with h1 | h2
          · exact hnd1 h1
          · exact hnd2 h2
        have hmk : ClassGroup.mk0 I₁₂ = ClassGroup.mk0 (I₁ * I₂) := by
          rw [map_mul, hf₁_eq, hf₂_eq, hf₁₂_eq]
        have hleg := legendre_absNorm_eq_of_classGroup_eq hd_sf hd_mod I₁₂ (I₁ * I₂) hmk p.1 p.2 hnd12 hnd_mul
        change legendreSym p.1 (Ideal.absNorm (idealOfBQF hd_mod f₁₂) : ℤ) =
          legendreSym p.1 (Ideal.absNorm (idealOfBQF hd_mod f₁ * idealOfBQF hd_mod f₂) : ℤ) at hleg
        rw [map_mul, absNorm_idealOfBQF hd_sf hd_mod f₁₂, absNorm_idealOfBQF hd_sf hd_mod f₁,
          absNorm_idealOfBQF hd_sf hd_mod f₂, Nat.cast_mul, Int.toNat_of_nonneg f₁₂.ha.le,
          Int.toNat_of_nonneg f₁.ha.le, Int.toNat_of_nonneg f₂.ha.le, legendreSym.mul] at hleg
        dsimp only
        rw [Pi.mul_apply, Units.val_mul, legendreUnit_val, legendreUnit_val, legendreUnit_val, hleg] }

lemma genusHom_apply_bqf (hd_sf : Squarefree d) (hd_mod : d % 8 = 3) (f : BQF d)
    (hcop : Nat.Coprime f.a.toNat d) (p : d.primeFactors) :
    haveI := quadK_numberField (d := d)
    haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    ((genusHom hd_sf hd_mod
      (ClassGroup.mk0 ⟨idealOfBQF hd_mod f, mem_nonZeroDivisors_of_ne_zero (idealOfBQF_ne_bot hd_mod f)⟩) p : ℤˣ) : ℤ) =
      legendreSym p.1 f.a := by
  haveI := quadK_numberField (d := d)
  haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  set c := ClassGroup.mk0 ⟨idealOfBQF hd_mod f, mem_nonZeroDivisors_of_ne_zero (idealOfBQF_ne_bot hd_mod f)⟩
  set g := (exists_coprime_rep hd_sf hd_mod c).choose
  have hg_eq := (exists_coprime_rep hd_sf hd_mod c).choose_spec.1
  have hg_cop := (exists_coprime_rep hd_sf hd_mod c).choose_spec.2
  have hnd : ∀ (h : BQF d), Nat.Coprime h.a.toNat d → ¬ p.1 ∣ Ideal.absNorm (idealOfBQF hd_mod h) := by
    intro h hc hpf
    rw [absNorm_idealOfBQF hd_sf hd_mod h] at hpf
    have := Nat.dvd_gcd hpf (Nat.dvd_of_mem_primeFactors p.2)
    rw [hc] at this
    exact (Nat.prime_of_mem_primeFactors p.2).not_dvd_one this
  have hleg := legendre_absNorm_eq_of_classGroup_eq hd_sf hd_mod
    ⟨idealOfBQF hd_mod g, mem_nonZeroDivisors_of_ne_zero (idealOfBQF_ne_bot hd_mod g)⟩
    ⟨idealOfBQF hd_mod f, mem_nonZeroDivisors_of_ne_zero (idealOfBQF_ne_bot hd_mod f)⟩
    hg_eq p.1 p.2 (hnd g hg_cop) (hnd f hcop)
  rw [absNorm_idealOfBQF hd_sf hd_mod g, absNorm_idealOfBQF hd_sf hd_mod f,
    Int.toNat_of_nonneg g.ha.le, Int.toNat_of_nonneg f.ha.le] at hleg
  dsimp only [genusHom, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [legendreUnit_val]
  exact hleg

end RingOfIntegers

/-!
### Section 4: Base Form `f₀` in the Target Genus (`2 * f₀.a ≡ -1 (mod d)`)
-/

open scoped NumberTheorySymbols in
lemma exists_target_bqf {d : ℕ} (hd_mod : d % 8 = 3) :
    ∃ f₀ : BQF d, (d : ℤ) ∣ 2 * f₀.a + 1 ∧ Nat.Coprime f₀.a.toNat d := by
  have hd_pos : 0 < d := by omega
  have hodd : ¬ 2 ∣ d := by omega
  haveI : NeZero d := ⟨hd_pos.ne'⟩
  haveI : NeZero (8 * d) := ⟨by positivity⟩
  have h8d : Nat.Coprime 8 d := by
    have h2 : Nat.Coprime 2 d := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
    simpa using h2.pow_left 3
  have h2u : IsUnit ((2 : ℕ) : ZMod d) :=
    (ZMod.isUnit_iff_coprime 2 d).mpr ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  set w : ZMod d := -((2 : ZMod d))⁻¹
  have hwu : IsUnit w := by
    have hmul : (-((2 : ZMod d))⁻¹) * (-((2 : ZMod d))) = 1 := by
      rw [neg_mul_neg, mul_comm]; exact ZMod.mul_inv_of_unit _ h2u
    exact ⟨⟨_, _, hmul, by rwa [mul_comm] at hmul⟩, rfl⟩
  let e2 := ZMod.chineseRemainder h8d
  let α : ZMod (8 * d) := e2.symm (1, w)
  have hunitα : IsUnit α := IsUnit.map e2.symm (Prod.isUnit_iff.mpr ⟨isUnit_one, hwu⟩)
  obtain ⟨q, hqgt, hqp, hqeq⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunitα d
  have hsplit : ((q : ZMod 8), (q : ZMod d)) = (1, w) := by
    have h1 : e2 (q : ZMod (8 * d)) = (1, w) := by rw [hqeq]; exact e2.apply_symm_apply _
    rw [map_natCast] at h1
    rw [← h1, Prod.ext_iff]
    exact ⟨(Prod.fst_natCast q).symm, (Prod.snd_natCast q).symm⟩
  have hq8 : q % 8 = 1 := by
    have h1 : (q : ZMod 8) = (1 : ZMod 8) := congrArg Prod.fst hsplit
    have h2 : q % 8 = 1 % 8 := (ZMod.natCast_eq_natCast_iff' q 1 8).mp (by simpa using h1)
    omega
  have hd_dvd : (d : ℤ) ∣ 2 * (q : ℤ) + 1 := by
    have h1 : (q : ZMod d) = w := congrArg Prod.snd hsplit
    have h2 : ((2 * (q : ℤ) + 1 : ℤ) : ZMod d) = 0 := by
      push_cast; rw [h1]
      have hmul := ZMod.mul_inv_of_unit (2 : ZMod d) h2u
      dsimp only [w]; linear_combination -hmul
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp h2
  haveI : Fact q.Prime := ⟨hqp⟩
  have hq4 : q % 4 = 1 := by omega
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hdodd : Odd d := Nat.odd_iff.mpr (by omega)
  -- Quadratic reciprocity: J(-d | q) = 1
  have hJ : J((-(d : ℤ)) | q) = 1 := by
    have h1 : J((-(d : ℤ)) | q) = J((-1 : ℤ) | q) * J(((d : ℕ) : ℤ) | q) := by
      rw [← jacobiSym.mul_left]; congr 1; ring
    have h2 : J((-1 : ℤ) | q) = 1 := by
      rw [jacobiSym.at_neg_one hqodd, ZMod.χ₄_nat_eq_if_mod_four]; simp [show q % 2 = 1 by omega, hq4]
    have h3 : J(((d : ℕ) : ℤ) | q) = J(((q : ℕ) : ℤ) | d) :=
      (jacobiSym.quadratic_reciprocity_one_mod_four hq4 hdodd).symm
    have h2d : Int.gcd (2 : ℤ) d = 1 := by
      have hcop : Nat.Coprime 2 d := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
      simpa [Int.gcd] using hcop
    have h4 : J((2 : ℤ) | d) * J(((q : ℕ) : ℤ) | d) = J((-1 : ℤ) | d) := by
      rw [← jacobiSym.mul_left]
      refine jacobiSym.mod_left' (Int.ModEq.symm (Int.modEq_iff_dvd.mpr ?_))
      simpa [show (2 : ℤ) * (q : ℤ) - (-1) = 2 * (q : ℤ) + 1 by ring] using hd_dvd
    have hsq := jacobiSym.sq_one h2d
    have h5 : J(((q : ℕ) : ℤ) | d) = J((2 : ℤ) | d) * J((-1 : ℤ) | d) := by
      calc J(((q : ℕ) : ℤ) | d) = J((2 : ℤ) | d) ^ 2 * J(((q : ℕ) : ℤ) | d) := by rw [hsq, one_mul]
        _ = J((2 : ℤ) | d) * (J((2 : ℤ) | d) * J(((q : ℕ) : ℤ) | d)) := by ring
        _ = J((2 : ℤ) | d) * J((-1 : ℤ) | d) := by rw [h4]
    have e1 : J((2 : ℤ) | d) = -1 := by
      rw [jacobiSym.at_two hdodd, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [hd_mod, show d % 2 = 1 by omega]
    have e2 : J((-1 : ℤ) | d) = -1 := by
      rw [jacobiSym.at_neg_one hdodd, ZMod.χ₄_nat_eq_if_mod_four]
      simp [show d % 2 = 1 by omega, show d % 4 = 3 by omega]
    rw [h1, h2, h3, h5, e1, e2]; norm_num
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJ
  set b : ℤ := if (r.val : ℤ) % 2 = 1 then (r.val : ℤ) else (r.val : ℤ) + (q : ℤ)
  have hbodd : b % 2 = 1 := by dsimp only [b]; split_ifs <;> omega
  have hqb : (q : ℤ) ∣ b ^ 2 + (d : ℤ) := by
    have hr0 : (q : ℤ) ∣ (r.val : ℤ) ^ 2 + (d : ℤ) := by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp ?_
      push_cast at hr ⊢
      rw [ZMod.natCast_zmod_val r]
      linear_combination -hr
    dsimp only [b]; split_ifs
    · exact hr0
    · obtain ⟨t, ht⟩ := hr0
      exact ⟨t + 2 * (r.val : ℤ) + (q : ℤ), by linear_combination ht⟩
  have h4b : (4 : ℤ) ∣ b ^ 2 + (d : ℤ) := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, b = 2 * k + 1 := ⟨(b - 1) / 2, by omega⟩
    exact ⟨k ^ 2 + k + ((d + 1) / 4 : ℕ), by
      have h4 : 4 * (((d + 1) / 4 : ℕ) : ℤ) = (d : ℤ) + 1 := by exact_mod_cast (show 4 * ((d + 1) / 4) = d + 1 by omega)
      rw [hk]; linear_combination -h4⟩
  have hcop4q : IsCoprime (4 : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, Int.gcd_natCast_natCast]
    have h2 : Nat.Coprime 2 q := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
    simpa using h2.pow_left 2
  obtain ⟨c, hc⟩ := hcop4q.mul_dvd h4b hqb
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hqp.pos
  have hcpos : 0 < c := by nlinarith [sq_nonneg b]
  have hcop_qd : Nat.Coprime q d := by
    rw [hqp.coprime_iff_not_dvd]
    intro h; exact absurd (Nat.le_of_dvd hd_pos h) (by omega)
  exact ⟨⟨(q : ℤ), b, c, hqZ, hcpos, by linarith⟩, hd_dvd, by simpa using hcop_qd⟩

/-!
### Section 5: Hermite–Minkowski Reduction of Positive Definite Det-1 `3×3` Integer Matrices
-/

private lemma volume_ball_two_gt_eight :
    (8 : ℝ) < Real.sqrt 2 ^ 3 * (Real.sqrt Real.pi ^ 3 / Real.Gamma ((3 : ℝ) / 2 + 1)) := by
  have hgam : Real.Gamma ((3 : ℝ) / 2 + 1) = 3 / 4 * Real.sqrt Real.pi := by
    rw [Real.Gamma_add_one (by norm_num), show ((3 : ℝ) / 2) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
  have hsπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hππ : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have hs21 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hrat : Real.sqrt Real.pi ^ 3 / (3 / 4 * Real.sqrt Real.pi) = 4 / 3 * Real.pi := by
    rw [div_eq_iff (by positivity)]; linear_combination Real.sqrt Real.pi * hππ
  have hcube : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by linear_combination Real.sqrt 2 * h22
  rw [hgam, hrat, hcube]
  nlinarith [Real.pi_gt_three, hs21, hs2]

open MeasureTheory in
private lemma exists_minkowski_unit_vec {A : Matrix (Fin 3) (Fin 3) ℤ}
    {L : Matrix (Fin 3) (Fin 3) ℝ} (hLdet : L.det = 1)
    (hLnorm : ∀ w : Fin 3 → ℝ,
      (L.mulVec w 0) ^ 2 + (L.mulVec w 1) ^ 2 + (L.mulVec w 2) ^ 2 =
      ∑ i : Fin 3, ∑ j : Fin 3, (A i j : ℝ) * w i * w j) :
    ∃ n : Fin 3 → ℤ, (∑ i : Fin 3, ∑ j : Fin 3, A i j * n i * n j) = 1 := by
  classical
  have hrpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hdet : LinearMap.det (Matrix.toLin' L) = 1 := by rw [LinearMap.det_toLin']; exact hLdet
  have hdetne : LinearMap.det (Matrix.toLin' L) ≠ 0 := by rw [hdet]; exact one_ne_zero
  have hs₀ball : {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2} =
      (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) ⁻¹' Metric.ball 0 (Real.sqrt 2) := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    rw [EuclideanSpace.norm_eq]
    have hcoords : ∀ i : Fin 3, ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3)) i‖ = |v i| := fun _ => rfl
    simp only [hcoords, Fin.sum_univ_three, sq_abs]
    rw [Real.sqrt_lt_sqrt_iff (by positivity)]
  have hs₀vol : volume {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2} =
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt 2)) := by
    rw [hs₀ball]
    exact (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage measurableSet_ball.nullMeasurableSet
  have hs₀conv : Convex ℝ {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2} := by
    rw [hs₀ball]
    exact Convex.linear_preimage (f := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap) (convex_ball 0 _)
  let S : Set (Fin 3 → ℝ) := ⇑(Matrix.toLin' L) ⁻¹' {v : Fin 3 → ℝ | v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 < 2}
  have hSconv : Convex ℝ S := Convex.linear_preimage hs₀conv (Matrix.toLin' L)
  have hSsymm : ∀ x ∈ S, -x ∈ S := fun x hx => by
    simp only [S, Set.mem_preimage, map_neg, Set.mem_setOf_eq, Pi.neg_apply, neg_sq] at hx ⊢; exact hx
  have hSvol : volume S = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt 2)) := by
    rw [Measure.addHaar_preimage_linearMap volume hdetne, hdet, hs₀vol]
    simp
  have hfund := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 3)) volume
  have hvolF : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) = 1 := by
    rw [ZSpan.volume_fundamentalDomain]
    have hone : Matrix.of ⇑(Pi.basisFun ℝ (Fin 3)) = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
      ext i j; simp [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [hone, Matrix.det_one]; simp
  have hballvol : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt 2)) =
      ENNReal.ofReal (Real.sqrt 2 ^ 3 * (Real.sqrt Real.pi ^ 3 / Real.Gamma ((3 : ℝ) / 2 + 1))) := by
    rw [EuclideanSpace.volume_ball, ← ENNReal.ofReal_pow hrpos.le, ← ENNReal.ofReal_mul (by positivity)]
    norm_num [Fintype.card_fin]
  have hineq : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) *
      2 ^ Module.finrank ℝ (Fin 3 → ℝ) < volume S := by
    rw [hvolF, one_mul, hSvol, hballvol]
    have hrank : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
    rw [hrank, show ((2 : ENNReal) ^ 3) = ENNReal.ofReal 8 by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ENNReal.ofReal_pow (by norm_num)]; norm_num,
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact volume_ball_two_gt_eight
  haveI : Countable ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin 3)))).toAddSubgroup :=
    (inferInstance : Countable ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin 3)))))
  obtain ⟨x, hx0, hxS⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hfund hSsymm hSconv hineq
  have hxmem : (x : Fin 3 → ℝ) ∈ Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin 3))) := by
    have := x.2; rwa [Submodule.mem_toAddSubgroup] at this
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hxmem
  have hxfun : (x : Fin 3 → ℝ) = fun j => (n j : ℝ) := by
    ext j; rw [← hn]; simp [Pi.basisFun_apply, Pi.single_apply, zsmul_eq_mul]
  have hlt2 : (∑ i : Fin 3, ∑ j : Fin 3, (A i j : ℝ) * (n i : ℝ) * (n j : ℝ)) < 2 := by
    have hmem : (L.mulVec (x : Fin 3 → ℝ) 0) ^ 2 + (L.mulVec (x : Fin 3 → ℝ) 1) ^ 2 +
        (L.mulVec (x : Fin 3 → ℝ) 2) ^ 2 < 2 := by
      simpa [S, Matrix.toLin'_apply] using hxS
    rw [hxfun, hLnorm] at hmem
    exact hmem
  have hpos : (0 : ℝ) < ∑ i : Fin 3, ∑ j : Fin 3, (A i j : ℝ) * (n i : ℝ) * (n j : ℝ) := by
    rw [← hLnorm]
    have hLne : L.mulVec (fun j => (n j : ℝ)) ≠ 0 := by
      intro h0
      have hxzero : (x : Fin 3 → ℝ) = 0 := by
        rw [hxfun]
        have hmul : L.adjugate.mulVec (L.mulVec (fun j => (n j : ℝ))) = fun j => (n j : ℝ) := by
          rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, hLdet, one_smul, Matrix.one_mulVec]
        rw [← hmul, h0, Matrix.mulVec_zero]
      exact hx0 (Subtype.ext hxzero)
    have hsome : L.mulVec (fun j => (n j : ℝ)) 0 ≠ 0 ∨ L.mulVec (fun j => (n j : ℝ)) 1 ≠ 0 ∨
        L.mulVec (fun j => (n j : ℝ)) 2 ≠ 0 := by
      by_contra h; push Not at h
      exact hLne (funext fun i => by fin_cases i <;> [exact h.1; exact h.2.1; exact h.2.2])
    rcases hsome with h0 | h1 | h2
    · have : 0 < (L.mulVec (fun j => (n j : ℝ)) 0) ^ 2 := sq_pos_of_ne_zero h0
      nlinarith [sq_nonneg (L.mulVec (fun j => (n j : ℝ)) 1), sq_nonneg (L.mulVec (fun j => (n j : ℝ)) 2)]
    · have : 0 < (L.mulVec (fun j => (n j : ℝ)) 1) ^ 2 := sq_pos_of_ne_zero h1
      nlinarith [sq_nonneg (L.mulVec (fun j => (n j : ℝ)) 0), sq_nonneg (L.mulVec (fun j => (n j : ℝ)) 2)]
    · have : 0 < (L.mulVec (fun j => (n j : ℝ)) 2) ^ 2 := sq_pos_of_ne_zero h2
      nlinarith [sq_nonneg (L.mulVec (fun j => (n j : ℝ)) 0), sq_nonneg (L.mulVec (fun j => (n j : ℝ)) 1)]
  have hposZ : (0 : ℤ) < ∑ i : Fin 3, ∑ j : Fin 3, A i j * n i * n j := by
    have : (0 : ℝ) < ((∑ i : Fin 3, ∑ j : Fin 3, A i j * n i * n j : ℤ) : ℝ) := by
      push_cast; exact hpos
    exact_mod_cast this
  have hltZ : (∑ i : Fin 3, ∑ j : Fin 3, A i j * n i * n j) < 2 := by
    have : ((∑ i : Fin 3, ∑ j : Fin 3, A i j * n i * n j : ℤ) : ℝ) < 2 := by
      push_cast; exact hlt2
    exact_mod_cast this
  exact ⟨n, by omega⟩

/-- Extend a primitive vector `n : Fin 3 → ℤ` (with `gcd(n 0, n 1, n 2) = 1`) to `U ∈ SL₃(ℤ)`
with first column `n`. -/
private lemma exists_sl3_first_col (n : Fin 3 → ℤ)
    (hprim : Int.gcd ((Int.gcd (n 0) (n 1) : ℕ) : ℤ) (n 2) = 1) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℤ, U.det = 1 ∧ ∀ i : Fin 3, U i 0 = n i := by
  set g : ℕ := Int.gcd (n 0) (n 1)
  by_cases hg : g = 0
  · have h0 : n 0 = 0 ∧ n 1 = 0 := Int.gcd_eq_zero_iff.mp hg
    rw [hg] at hprim
    have h2 : (n 2).natAbs = 1 := by simpa using hprim
    have h2sq : n 2 ^ 2 = 1 := by
      rcases Int.natAbs_eq (n 2) with h | h <;> rw [h, h2] <;> norm_num
    refine ⟨!![0, 1, 0; 0, 0, n 2; n 2, 0, 0], ?_, ?_⟩
    · rw [Matrix.det_fin_three]; simp; linarith
    · intro i; fin_cases i <;> simp [h0.1, h0.2]
  · have hgpos : (0 : ℤ) < (g : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hg
    obtain ⟨a, ha⟩ := Int.gcd_dvd_left (n 0) (n 1)
    obtain ⟨b, hb⟩ := Int.gcd_dvd_right (n 0) (n 1)
    have hcop_ab : Int.gcd a b = 1 := by
      have h1 : Int.gcd ((g : ℤ) * a) ((g : ℤ) * b) = g := by rw [← ha, ← hb]
      rw [Int.gcd_mul_left, Int.natAbs_natCast] at h1
      exact mul_left_cancel₀ hg (by simpa using h1)
    set d' : ℤ := Int.gcdA a b
    set c' : ℤ := -Int.gcdB a b
    have hab : a * d' - b * c' = 1 := by
      have := Int.gcd_eq_gcd_ab a b; rw [hcop_ab, Nat.cast_one] at this; dsimp only [d', c']; linarith
    set s' : ℤ := Int.gcdA (g : ℤ) (n 2)
    set r' : ℤ := -Int.gcdB (g : ℤ) (n 2)
    have hgn : (g : ℤ) * s' - (n 2) * r' = 1 := by
      have := Int.gcd_eq_gcd_ab (g : ℤ) (n 2); rw [hprim, Nat.cast_one] at this; dsimp only [s', r']; linarith
    refine ⟨!![n 0, c', a * r'; n 1, d', b * r'; n 2, 0, s'], ?_, ?_⟩
    · rw [Matrix.det_fin_three]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
      have ha' : n 0 = (g : ℤ) * a := ha
      have hb' : n 1 = (g : ℤ) * b := hb
      linear_combination (d' * s') * ha' - (c' * s') * hb' + ((g : ℤ) * s' - n 2 * r') * hab + hgn
    · intro i; fin_cases i <;> simp

set_option maxHeartbeats 600000 in
/-- Every symmetric positive definite det-1 `3×3` integer matrix `A` with Cholesky factor `L`
(`L.det = 1`) factors as `A = Pᵀ * P` for some `P ∈ SL₃(ℤ)`. -/
private lemma exists_sl3_gram_eq {A : Matrix (Fin 3) (Fin 3) ℤ} (hAsymm : A.IsSymm) (hAdet : A.det = 1)
    {L : Matrix (Fin 3) (Fin 3) ℝ} (hLdet : L.det = 1)
    (hLnorm : ∀ w : Fin 3 → ℝ,
      (L.mulVec w 0) ^ 2 + (L.mulVec w 1) ^ 2 + (L.mulVec w 2) ^ 2 =
      ∑ i : Fin 3, ∑ j : Fin 3, (A i j : ℝ) * w i * w j) :
    ∃ P : Matrix (Fin 3) (Fin 3) ℤ, P.det = 1 ∧ Pᵀ * P = A := by
  obtain ⟨n, hn1⟩ := exists_minkowski_unit_vec hLdet hLnorm
  have hprim : Int.gcd ((Int.gcd (n 0) (n 1) : ℕ) : ℤ) (n 2) = 1 := by
    set g : ℕ := Int.gcd ((Int.gcd (n 0) (n 1) : ℕ) : ℤ) (n 2)
    have hg0 : (g : ℤ) ∣ n 0 := dvd_trans (Int.gcd_dvd_left _ _) (Int.gcd_dvd_left _ _)
    have hg1 : (g : ℤ) ∣ n 1 := dvd_trans (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
    have hg2 : (g : ℤ) ∣ n 2 := Int.gcd_dvd_right _ _
    have hgi : ∀ i : Fin 3, (g : ℤ) ∣ n i := fun i => by fin_cases i <;> assumption
    have hg2_1 : (g : ℤ) ^ 2 ∣ (1 : ℤ) := by
      rw [← hn1]
      refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
      obtain ⟨ni, hni⟩ := hgi i; obtain ⟨nj, hnj⟩ := hgi j
      exact ⟨A i j * ni * nj, by rw [hni, hnj]; ring⟩
    have hg1' : (g : ℤ) ∣ 1 := dvd_trans (dvd_pow_self _ two_ne_zero) hg2_1
    have hgN : g ∣ 1 := by exact_mod_cast hg1'
    exact Nat.dvd_one.mp hgN
  obtain ⟨U, hUdet, hUcol⟩ := exists_sl3_first_col n hprim
  let A₁ : Matrix (Fin 3) (Fin 3) ℤ := Uᵀ * A * U
  have hA₁symm : A₁.IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hAsymm.eq, ← Matrix.mul_assoc]
  have hA₁det : A₁.det = 1 := by simp [A₁, hUdet, hAdet]
  have hA₁00 : A₁ 0 0 = 1 := by
    have h : A₁ 0 0 = ∑ i : Fin 3, ∑ j : Fin 3, A i j * n i * n j := by
      simp only [A₁, Matrix.mul_apply, Matrix.transpose_apply, hUcol]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [h, hn1]
  let E : Matrix (Fin 3) (Fin 3) ℤ := !![1, -A₁ 0 1, -A₁ 0 2; 0, 1, 0; 0, 0, 1]
  have hEdet : E.det = 1 := by rw [Matrix.det_fin_three]; simp [E]
  let A₂ : Matrix (Fin 3) (Fin 3) ℤ := Eᵀ * A₁ * E
  have hA₂det : A₂.det = 1 := by simp [A₂, hEdet, hA₁det]
  have hA₂00 : A₂ 0 0 = 1 := by
    simp [A₂, E, Matrix.mul_apply, Fin.sum_univ_three, hA₁00]
  have hA₂01 : A₂ 0 1 = 0 := by
    simp [A₂, E, Matrix.mul_apply, Fin.sum_univ_three, hA₁00]
  have hA₂02 : A₂ 0 2 = 0 := by
    simp [A₂, E, Matrix.mul_apply, Fin.sum_univ_three, hA₁00]
  have hA₁10 : A₁ 1 0 = A₁ 0 1 := congrFun (congrFun hA₁symm 0) 1
  have hA₁20 : A₁ 2 0 = A₁ 0 2 := congrFun (congrFun hA₁symm 0) 2
  have hA₁21 : A₁ 2 1 = A₁ 1 2 := congrFun (congrFun hA₁symm 1) 2
  have hA₂10 : A₂ 1 0 = 0 := by
    simp [A₂, E, Matrix.mul_apply, Fin.sum_univ_three, hA₁00, hA₁10]
  have hA₂20 : A₂ 2 0 = 0 := by
    simp [A₂, E, Matrix.mul_apply, Fin.sum_univ_three, hA₁00, hA₁20]
  have hA₂21 : A₂ 2 1 = A₂ 1 2 := by
    simp [A₂, E, Matrix.mul_apply, Fin.sum_univ_three, hA₁00, hA₁10, hA₁20, hA₁21]; ring
  -- Bottom-right 2x2 block of A₂ has det 1 and is positive definite
  set p := A₂ 1 1; set q := A₂ 1 2; set r := A₂ 2 2
  have hBdet : p * r - q ^ 2 = 1 := by
    have hd := hA₂det
    rw [Matrix.det_fin_three, hA₂00, hA₂01, hA₂02, hA₂10, hA₂20, hA₂21] at hd
    linarith
  -- Positive definiteness of A₂ implies p > 0 and r > 0
  have hA₂_pos : ∀ w : Fin 3 → ℤ, w ≠ 0 → 0 < ∑ i : Fin 3, ∑ j : Fin 3, A₂ i j * w i * w j := by
    intro w hw
    let MUE : Matrix (Fin 3) (Fin 3) ℝ := (U * E).map (Int.cast : ℤ → ℝ)
    let v : Fin 3 → ℝ := MUE.mulVec (fun j => (w j : ℝ))
    have hUEdet : MUE.det = 1 := by
      change ((Int.castRingHom ℝ).mapMatrix (U * E)).det = 1
      rw [← RingHom.map_det, Matrix.det_mul, hUdet, hEdet]; simp
    have hvne : v ≠ 0 := by
      intro h0
      have hw0 : (fun j => (w j : ℝ)) = 0 := by
        have hmul : MUE.adjugate.mulVec (MUE.mulVec (fun j => (w j : ℝ))) = fun j => (w j : ℝ) := by
          rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, hUEdet, one_smul, Matrix.one_mulVec]
        rw [← hmul, show MUE.mulVec (fun j => (w j : ℝ)) = 0 from h0, Matrix.mulVec_zero]
      exact hw (funext fun j => Int.cast_eq_zero.mp (congrFun hw0 j))
    have hLne : L.mulVec v ≠ 0 := by
      intro h0
      have hmul : L.adjugate.mulVec (L.mulVec v) = v := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, hLdet, one_smul, Matrix.one_mulVec]
      exact hvne (by rw [← hmul, h0, Matrix.mulVec_zero])
    have hsum_eq : (∑ i : Fin 3, ∑ j : Fin 3, (A₂ i j : ℝ) * (w i : ℝ) * (w j : ℝ)) =
        ∑ i : Fin 3, ∑ j : Fin 3, (A i j : ℝ) * v i * v j := by
      have hA₂_eq : A₂.map (Int.cast : ℤ → ℝ) = MUEᵀ * A.map (Int.cast : ℤ → ℝ) * MUE := by
        have h1 : A₂ = (U * E)ᵀ * A * (U * E) := by simp [A₂, A₁, Matrix.transpose_mul, Matrix.mul_assoc]
        have h2 : (Int.castRingHom ℝ).mapMatrix A₂ =
            (Int.castRingHom ℝ).mapMatrix ((U * E)ᵀ * A * (U * E)) := congrArg _ h1
        conv_rhs at h2 => rw [map_mul, map_mul]
        change A₂.map (Int.cast : ℤ → ℝ) =
          ((U * E)ᵀ.map (Int.cast : ℤ → ℝ)) * (A.map (Int.cast : ℤ → ℝ)) * MUE at h2
        rwa [Matrix.transpose_map] at h2
      let wR : Fin 3 → ℝ := fun j => (w j : ℝ)
      have hquad : ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ),
          (∑ i : Fin 3, ∑ j : Fin 3, M i j * x i * x j) = dotProduct x (M.mulVec x) := by
        intro M x
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      have hlhs : (∑ i : Fin 3, ∑ j : Fin 3, (A₂ i j : ℝ) * (w i : ℝ) * (w j : ℝ)) =
          dotProduct wR ((A₂.map (Int.cast : ℤ → ℝ)).mulVec wR) := hquad _ wR
      have hrhs : (∑ i : Fin 3, ∑ j : Fin 3, (A i j : ℝ) * v i * v j) =
          dotProduct v ((A.map (Int.cast : ℤ → ℝ)).mulVec v) := hquad _ v
      rw [hlhs, hrhs, hA₂_eq]
      change dotProduct wR ((MUEᵀ * A.map (Int.cast : ℤ → ℝ) * MUE).mulVec wR) =
        dotProduct (MUE.mulVec wR) ((A.map (Int.cast : ℤ → ℝ)).mulVec (MUE.mulVec wR))
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose, ← Matrix.mulVec_mulVec]
    have hposR : (0 : ℝ) < ∑ i : Fin 3, ∑ j : Fin 3, (A₂ i j : ℝ) * (w i : ℝ) * (w j : ℝ) := by
      rw [hsum_eq, ← hLnorm]
      have hsome : L.mulVec v 0 ≠ 0 ∨ L.mulVec v 1 ≠ 0 ∨ L.mulVec v 2 ≠ 0 := by
        by_contra h; push Not at h
        exact hLne (funext fun i => by fin_cases i <;> [exact h.1; exact h.2.1; exact h.2.2])
      rcases hsome with h0 | h1 | h2
      · have := sq_pos_of_ne_zero h0; nlinarith [sq_nonneg (L.mulVec v 1), sq_nonneg (L.mulVec v 2)]
      · have := sq_pos_of_ne_zero h1; nlinarith [sq_nonneg (L.mulVec v 0), sq_nonneg (L.mulVec v 2)]
      · have := sq_pos_of_ne_zero h2; nlinarith [sq_nonneg (L.mulVec v 0), sq_nonneg (L.mulVec v 1)]
    have : (0 : ℝ) < ((∑ i : Fin 3, ∑ j : Fin 3, A₂ i j * w i * w j : ℤ) : ℝ) := by
      push_cast; exact hposR
    exact_mod_cast this
  have hp_pos : 0 < p := by
    have := hA₂_pos ![0, 1, 0] (by intro h; exact one_ne_zero (congrFun h 1))
    simpa [Fin.sum_univ_three, p] using this
  have hr_pos : 0 < r := by
    have := hA₂_pos ![0, 0, 1] (by intro h; exact one_ne_zero (congrFun h 2))
    simpa [Fin.sum_univ_three, r] using this
  -- Reduce the 2x2 form `g_B` of discriminant -4 to `x^2 + y^2`
  let gB : BQF 4 := ⟨p, 2 * q, r, hp_pos, hr_pos, by linear_combination 4 * hBdet⟩
  obtain ⟨gRed, hgRed, hstep⟩ := exists_reduced_stepEquiv (by norm_num : 0 < 4) gB
  obtain ⟨V, hVdet, hVeval⟩ := hstep.toSL2
  have hgRed_a : gRed.a = 1 := by
    have hb2 : gRed.b ^ 2 ≤ gRed.a ^ 2 := by nlinarith [abs_le.mp hgRed.1]
    have hac : gRed.a ^ 2 ≤ gRed.a * gRed.c := by nlinarith [gRed.ha, hgRed.2]
    have hd4 : 4 * gRed.a * gRed.c - gRed.b ^ 2 = 4 := gRed.hdisc
    have h3 : 3 * gRed.a ^ 2 ≤ 4 := by linarith
    nlinarith [gRed.ha]
  have hgRed_b : gRed.b = 0 := by
    have hba : |gRed.b| ≤ 1 := by rw [← hgRed_a]; exact hgRed.1
    have hdisc := gRed.hdisc
    rw [hgRed_a] at hdisc
    have : gRed.b = -1 ∨ gRed.b = 0 ∨ gRed.b = 1 := by
      have := abs_le.mp hba; omega
    rcases this with hb | hb | hb <;> rw [hb] at hdisc <;> omega
  have hgRed_c : gRed.c = 1 := by
    have := gRed.hdisc; rw [hgRed_a, hgRed_b] at this; omega
  let W : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, V 0 0, V 0 1; 0, V 1 0, V 1 1]
  have hWdet : W.det = 1 := by
    rw [Matrix.det_fin_three]
    simp only [W, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_fin_one, Fin.isValue]
    have := hVdet; rw [Matrix.det_fin_two] at this; linarith
  have hWgram : Wᵀ * A₂ * W = 1 := by
    have he10 := hVeval 1 0
    have he01 := hVeval 0 1
    have he11 := hVeval 1 1
    simp only [gB, eval, hgRed_a, hgRed_b, hgRed_c, mul_one, mul_zero, add_zero, zero_add,
      one_pow, zero_pow two_ne_zero] at he10 he01 he11
    have h11 : p * V 0 0 ^ 2 + 2 * q * V 0 0 * V 1 0 + r * V 1 0 ^ 2 = 1 := by linarith
    have h22 : p * V 0 1 ^ 2 + 2 * q * V 0 1 * V 1 1 + r * V 1 1 ^ 2 = 1 := by linarith
    have h12 : p * V 0 0 * V 0 1 + q * (V 0 0 * V 1 1 + V 0 1 * V 1 0) + r * V 1 0 * V 1 1 = 0 := by linarith
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, W,
        hA₂00, hA₂01, hA₂02, hA₂10, hA₂20, hA₂21, show A₂ 1 1 = p from rfl,
        show A₂ 1 2 = q from rfl, show A₂ 2 2 = r from rfl] <;>
      first | linear_combination h11 | linear_combination h12 | linear_combination h22
  let Q : Matrix (Fin 3) (Fin 3) ℤ := U * E * W
  have hQdet : Q.det = 1 := by simp [Q, hUdet, hEdet, hWdet]
  have hQgram : Qᵀ * A * Q = 1 := by
    calc Qᵀ * A * Q = Wᵀ * (Eᵀ * (Uᵀ * A * U) * E) * W := by
          simp [Q, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Wᵀ * A₂ * W := rfl
      _ = 1 := hWgram
  let P : Matrix (Fin 3) (Fin 3) ℤ := Q.adjugate
  have hPQ : P * Q = 1 := by rw [Matrix.adjugate_mul, hQdet, one_smul]
  have hQP : Q * P = 1 := by rw [Matrix.mul_adjugate, hQdet, one_smul]
  have hPdet : P.det = 1 := by
    have := Matrix.det_adjugate Q
    rw [hQdet, one_pow] at this; exact this
  refine ⟨P, hPdet, ?_⟩
  calc Pᵀ * P = Pᵀ * 1 * P := by simp
    _ = Pᵀ * (Qᵀ * A * Q) * P := by rw [hQgram]
    _ = (Q * P)ᵀ * A * (Q * P) := by simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = A := by rw [hQP, Matrix.transpose_one, one_mul, mul_one]

/-!
### Section 6: Genus-to-3-Squares Map and Main Lower Bound `r3_ge_class_number`
-/

/-- Given `f : BQF d` with `legendreSym p (-2 * f.a) = 1` for all `p ∣ d`, produce `P ∈ SL₃(ℤ)`
whose first two columns have Gram matrix `!![2 f.a, f.b; f.b, 2 f.c]`. -/
private lemma exists_sl3_for_bqf {d : ℕ} (hd_sf : Squarefree d) (hd_mod : d % 8 = 3) (f : BQF d)
    (hleg : ∀ p : d.primeFactors,
      haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
      legendreSym p.1 (-2 * f.a) = 1) :
    ∃ P : Matrix (Fin 3) (Fin 3) ℤ, P.det = 1 ∧
      (∑ i : Fin 3, P i 0 * P i 0) = 2 * f.a ∧
      (∑ i : Fin 3, P i 0 * P i 1) = f.b ∧
      (∑ i : Fin 3, P i 1 * P i 1) = 2 * f.c := by
  have hd_pos : 0 < d := by omega
  have hS : ∀ p ∈ d.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  -- Solve 2 * f.a * s^2 ≡ -1 (mod p) for each p ∈ d.primeFactors
  have hsol_p : ∀ p : ℕ, p ∈ d.primeFactors → ∃ s_p : ℕ, (p : ℤ) ∣ 2 * f.a * (s_p : ℤ) ^ 2 + 1 := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hpp⟩
    have hl := hleg ⟨p, hp⟩
    have hne : ((-2 * f.a : ℤ) : ZMod p) ≠ 0 := by
      intro h0; rw [(legendreSym.eq_zero_iff p _).mpr h0] at hl; norm_num at hl
    obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p hne).mp hl
    have hrne : r ≠ 0 := by intro h; rw [h, mul_zero] at hr; exact hne hr
    let s_mod : ZMod p := r⁻¹
    refine ⟨s_mod.val, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
    push_cast
    rw [ZMod.natCast_zmod_val]
    have h2a : (2 : ZMod p) * (f.a : ZMod p) = -(r * r) := by
      have : ((-2 * f.a : ℤ) : ZMod p) = r * r := hr
      push_cast at this; linear_combination -this
    rw [h2a]
    dsimp only [s_mod]
    have hinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hrne
    linear_combination -(r * r⁻¹ + 1) * hinv
  let sp : ℕ → ℕ := fun p => if hp : p ∈ d.primeFactors then (hsol_p p hp).choose else 0
  obtain ⟨sN, hsN⟩ := crt_primes hS sp
  set s : ℤ := (sN : ℤ)
  have hd_dvd : (d : ℤ) ∣ 2 * f.a * s ^ 2 + 1 := by
    have hprod_eq : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hd_sf
    have hprod_dvd : (∏ p ∈ d.primeFactors, (p : ℤ)) ∣ 2 * f.a * s ^ 2 + 1 := by
      refine Finset.prod_dvd_of_coprime ?_ ?_
      · intro p hp q hq hpq
        dsimp only [Function.onFun]
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
        exact (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq
      · intro p hp
        have hsp := (hsol_p p hp).choose_spec
        have hsmod : (s : ZMod p) = ((sp p : ℕ) : ZMod p) := by
          dsimp only [s]
          exact_mod_cast (ZMod.natCast_eq_natCast_iff sN (sp p) p).mpr (hsN p hp)
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_
        push_cast; rw [hsmod]; simp only [sp, dif_pos hp]
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hsp
        simpa using this
    have hcast : ((∏ p ∈ d.primeFactors, p : ℕ) : ℤ) = (d : ℤ) := by exact_mod_cast hprod_eq
    rw [← hcast, Nat.cast_prod]
    exact hprod_dvd
  obtain ⟨t, ht⟩ := hd_dvd
  let A : Matrix (Fin 3) (Fin 3) ℤ := !![2 * f.a, f.b, 0; f.b, 2 * f.c, s; 0, s, t]
  have hAsymm : A.IsSymm := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A]
  have hAdet : A.det = 1 := by
    rw [Matrix.det_fin_three]
    simp only [A, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_fin_one, Fin.isValue]
    linear_combination t * f.hdisc - ht
  set aR : ℝ := (f.a : ℝ)
  set bR : ℝ := (f.b : ℝ)
  set cR : ℝ := (f.c : ℝ)
  set dR : ℝ := (d : ℝ)
  set sR : ℝ := (s : ℝ)
  set tR : ℝ := (t : ℝ)
  have haR : 0 < aR := by dsimp only [aR]; exact_mod_cast f.ha
  have hdR : 0 < dR := by dsimp only [dR]; exact_mod_cast hd_pos
  have hdiscR : 4 * aR * cR - bR ^ 2 = dR := by dsimp only [aR, bR, cR, dR]; exact_mod_cast f.hdisc
  have htR : 2 * aR * sR ^ 2 + 1 = dR * tR := by dsimp only [aR, dR, sR, tR]; exact_mod_cast ht
  let L : Matrix (Fin 3) (Fin 3) ℝ :=
    !![Real.sqrt (2 * aR), bR / Real.sqrt (2 * aR), 0;
       0, Real.sqrt (dR / (2 * aR)), sR * Real.sqrt (2 * aR / dR);
       0, 0, 1 / Real.sqrt dR]
  have hLdet : L.det = 1 := by
    rw [Matrix.det_fin_three]
    simp only [L, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_fin_one, Fin.isValue]
    have h1 : Real.sqrt (2 * aR) * Real.sqrt (dR / (2 * aR)) = Real.sqrt dR := by
      rw [← Real.sqrt_mul (by positivity), mul_div_cancel₀ _ (by positivity)]
    have h2 : Real.sqrt dR ≠ 0 := (Real.sqrt_pos.mpr hdR).ne'
    calc Real.sqrt (2 * aR) * Real.sqrt (dR / (2 * aR)) * (1 / Real.sqrt dR) -
          Real.sqrt (2 * aR) * (sR * Real.sqrt (2 * aR / dR)) * 0 -
          bR / Real.sqrt (2 * aR) * 0 * (1 / Real.sqrt dR) +
          bR / Real.sqrt (2 * aR) * (sR * Real.sqrt (2 * aR / dR)) * 0 +
          0 * 0 * 0 - 0 * Real.sqrt (dR / (2 * aR)) * 0
        = (Real.sqrt (2 * aR) * Real.sqrt (dR / (2 * aR))) * (1 / Real.sqrt dR) := by ring
      _ = Real.sqrt dR * (1 / Real.sqrt dR) := by rw [h1]
      _ = 1 := by field_simp
  have hLnorm : ∀ w : Fin 3 → ℝ,
      (L.mulVec w 0) ^ 2 + (L.mulVec w 1) ^ 2 + (L.mulVec w 2) ^ 2 =
      ∑ i : Fin 3, ∑ j : Fin 3, (A i j : ℝ) * w i * w j := by
    intro w
    simp only [L, A, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_fin_one, Fin.isValue, Int.cast_mul, Int.cast_ofNat, Int.cast_zero]
    have hs1 : Real.sqrt (2 * aR) ^ 2 = 2 * aR := Real.sq_sqrt (by positivity)
    have hs2 : Real.sqrt (dR / (2 * aR)) ^ 2 = dR / (2 * aR) := Real.sq_sqrt (by positivity)
    have hs3 : Real.sqrt (2 * aR / dR) ^ 2 = 2 * aR / dR := Real.sq_sqrt (by positivity)
    have hs4 : Real.sqrt dR ^ 2 = dR := Real.sq_sqrt hdR.le
    have hmul1 : Real.sqrt (2 * aR) * (bR / Real.sqrt (2 * aR)) = bR := by
      have : Real.sqrt (2 * aR) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      field_simp
    have hmul2 : Real.sqrt (dR / (2 * aR)) * Real.sqrt (2 * aR / dR) = 1 := by
      rw [← Real.sqrt_mul (by positivity),
        show dR / (2 * aR) * (2 * aR / dR) = 1 by field_simp, Real.sqrt_one]
    have h1 : (Real.sqrt (2 * aR) * w 0 + bR / Real.sqrt (2 * aR) * w 1 + 0 * w 2) ^ 2 =
        2 * aR * w 0 ^ 2 + 2 * bR * w 0 * w 1 + bR ^ 2 / (2 * aR) * w 1 ^ 2 := by
      have hne : Real.sqrt (2 * aR) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      calc (Real.sqrt (2 * aR) * w 0 + bR / Real.sqrt (2 * aR) * w 1 + 0 * w 2) ^ 2
          = Real.sqrt (2 * aR) ^ 2 * w 0 ^ 2 + 2 * (Real.sqrt (2 * aR) * (bR / Real.sqrt (2 * aR))) * w 0 * w 1 +
            bR ^ 2 / Real.sqrt (2 * aR) ^ 2 * w 1 ^ 2 := by ring
        _ = 2 * aR * w 0 ^ 2 + 2 * bR * w 0 * w 1 + bR ^ 2 / (2 * aR) * w 1 ^ 2 := by rw [hs1, hmul1]
    have h2 : (0 * w 0 + Real.sqrt (dR / (2 * aR)) * w 1 + sR * Real.sqrt (2 * aR / dR) * w 2) ^ 2 =
        dR / (2 * aR) * w 1 ^ 2 + 2 * sR * w 1 * w 2 + 2 * aR * sR ^ 2 / dR * w 2 ^ 2 := by
      calc (0 * w 0 + Real.sqrt (dR / (2 * aR)) * w 1 + sR * Real.sqrt (2 * aR / dR) * w 2) ^ 2
          = Real.sqrt (dR / (2 * aR)) ^ 2 * w 1 ^ 2 +
            2 * sR * (Real.sqrt (dR / (2 * aR)) * Real.sqrt (2 * aR / dR)) * w 1 * w 2 +
            sR ^ 2 * Real.sqrt (2 * aR / dR) ^ 2 * w 2 ^ 2 := by ring
        _ = dR / (2 * aR) * w 1 ^ 2 + 2 * sR * w 1 * w 2 + 2 * aR * sR ^ 2 / dR * w 2 ^ 2 := by
            rw [hs2, hmul2, hs3]; ring
    have h3 : (0 * w 0 + 0 * w 1 + 1 / Real.sqrt dR * w 2) ^ 2 = 1 / dR * w 2 ^ 2 := by
      calc (0 * w 0 + 0 * w 1 + 1 / Real.sqrt dR * w 2) ^ 2 = 1 / Real.sqrt dR ^ 2 * w 2 ^ 2 := by ring
        _ = 1 / dR * w 2 ^ 2 := by rw [hs4]
    rw [h1, h2, h3]
    have hb2d : bR ^ 2 / (2 * aR) + dR / (2 * aR) = 2 * cR := by
      rw [← add_div, div_eq_iff (by positivity)]; linarith
    have hs2t : 2 * aR * sR ^ 2 / dR + 1 / dR = tR := by
      rw [← add_div, div_eq_iff hdR.ne']; linarith
    dsimp only [aR, bR, cR, sR, tR] at hb2d hs2t ⊢
    linear_combination (w 1 ^ 2) * hb2d + (w 2 ^ 2) * hs2t
  obtain ⟨P, hPdet, hPgram⟩ := exists_sl3_gram_eq hAsymm hAdet hLdet hLnorm
  refine ⟨P, hPdet, ?_, ?_, ?_⟩
  · have h := congrFun (congrFun hPgram 0) 0
    simpa [Matrix.mul_apply, Matrix.transpose_apply, A] using h
  · have h := congrFun (congrFun hPgram 0) 1
    simpa [Matrix.mul_apply, Matrix.transpose_apply, A] using h
  · have h := congrFun (congrFun hPgram 1) 1
    simpa [Matrix.mul_apply, Matrix.transpose_apply, A] using h

private def crossCols (P : Matrix (Fin 3) (Fin 3) ℤ) : ℤ × ℤ × ℤ :=
  (P 1 0 * P 2 1 - P 2 0 * P 1 1,
   P 2 0 * P 0 1 - P 0 0 * P 2 1,
   P 0 0 * P 1 1 - P 1 0 * P 0 1)

private lemma crossCols_mem_rep3Z {d : ℕ} {f : BQF d} {P : Matrix (Fin 3) (Fin 3) ℤ}
    (h00 : (∑ i : Fin 3, P i 0 * P i 0) = 2 * f.a)
    (h01 : (∑ i : Fin 3, P i 0 * P i 1) = f.b)
    (h11 : (∑ i : Fin 3, P i 1 * P i 1) = 2 * f.c) :
    crossCols P ∈ rep3Z d := by
  rw [mem_rep3Z_iff]
  dsimp only [crossCols]
  simp only [Fin.sum_univ_three] at h00 h01 h11
  have hlag : (P 1 0 * P 2 1 - P 2 0 * P 1 1) ^ 2 + (P 2 0 * P 0 1 - P 0 0 * P 2 1) ^ 2 +
      (P 0 0 * P 1 1 - P 1 0 * P 0 1) ^ 2 =
      (P 0 0 * P 0 0 + P 1 0 * P 1 0 + P 2 0 * P 2 0) *
        (P 0 1 * P 0 1 + P 1 1 * P 1 1 + P 2 1 * P 2 1) -
      (P 0 0 * P 0 1 + P 1 0 * P 1 1 + P 2 0 * P 2 1) ^ 2 := by ring
  rw [hlag, h00, h01, h11]
  linear_combination f.hdisc

private lemma gl2Equiv_of_crossCols_eq {d : ℕ} {f₁ f₂ : BQF d} {P₁ P₂ : Matrix (Fin 3) (Fin 3) ℤ}
    (hdet1 : P₁.det = 1) (hdet2 : P₂.det = 1)
    (h1_00 : (∑ i : Fin 3, P₁ i 0 * P₁ i 0) = 2 * f₁.a)
    (h1_01 : (∑ i : Fin 3, P₁ i 0 * P₁ i 1) = f₁.b)
    (h1_11 : (∑ i : Fin 3, P₁ i 1 * P₁ i 1) = 2 * f₁.c)
    (h2_00 : (∑ i : Fin 3, P₂ i 0 * P₂ i 0) = 2 * f₂.a)
    (h2_01 : (∑ i : Fin 3, P₂ i 0 * P₂ i 1) = f₂.b)
    (h2_11 : (∑ i : Fin 3, P₂ i 1 * P₂ i 1) = 2 * f₂.c)
    (hcross : crossCols P₁ = crossCols P₂) :
    GL2Equiv f₁ f₂ := by
  let R : Matrix (Fin 3) (Fin 3) ℤ := P₁.adjugate * P₂
  have hP₁R : P₁ * R = P₂ := by rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet1, one_smul, one_mul]
  have hRdet : R.det = 1 := by
    rw [Matrix.det_mul, Matrix.det_adjugate, hdet1, one_pow, hdet2, mul_one]
  set v := crossCols P₁
  have hdot : ∀ w : Fin 3 → ℤ,
      v.1 * (P₁.mulVec w 0) + v.2.1 * (P₁.mulVec w 1) + v.2.2 * (P₁.mulVec w 2) = w 2 := by
    intro w
    have hd := hdet1
    rw [Matrix.det_fin_three] at hd
    simp only [v, crossCols, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination w 2 * hd
  have hdot_v2 : ∀ j : Fin 3, j = 0 ∨ j = 1 →
      v.1 * P₂ 0 j + v.2.1 * P₂ 1 j + v.2.2 * P₂ 2 j = 0 := by
    intro j hj
    rw [hcross]
    rcases hj with rfl | rfl <;> dsimp only [crossCols] <;> ring
  have hR20 : R 2 0 = 0 := by
    have h1 := hdot (fun i => R i 0)
    have hcol : ∀ k : Fin 3, P₁.mulVec (fun i => R i 0) k = P₂ k 0 := fun k => by
      have := congrFun (congrFun hP₁R k) 0
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
    rw [hcol 0, hcol 1, hcol 2] at h1
    linarith [hdot_v2 0 (Or.inl rfl)]
  have hR21 : R 2 1 = 0 := by
    have h1 := hdot (fun i => R i 1)
    have hcol : ∀ k : Fin 3, P₁.mulVec (fun i => R i 1) k = P₂ k 1 := fun k => by
      have := congrFun (congrFun hP₁R k) 1
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
    rw [hcol 0, hcol 1, hcol 2] at h1
    linarith [hdot_v2 1 (Or.inr rfl)]
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![R 0 0, R 0 1; R 1 0, R 1 1]
  have hMdet : M.det = 1 ∨ M.det = -1 := by
    have h1 : M.det * R 2 2 = 1 := by
      have hd := hRdet
      rw [Matrix.det_fin_three, hR20, hR21] at hd
      rw [Matrix.det_fin_two]
      simp only [M, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Fin.isValue]
      linarith
    exact Int.eq_one_or_neg_one_of_mul_eq_one h1
  refine ⟨M, hMdet, fun x y => ?_⟩
  have hvec : ∀ k : Fin 3,
      P₂ k 0 * x + P₂ k 1 * y =
      P₁ k 0 * (M 0 0 * x + M 0 1 * y) + P₁ k 1 * (M 1 0 * x + M 1 1 * y) := by
    intro k
    have hc0 : P₂ k 0 = P₁ k 0 * R 0 0 + P₁ k 1 * R 1 0 := by
      have := congrFun (congrFun hP₁R k) 0
      simp only [Matrix.mul_apply, Fin.sum_univ_three, hR20, mul_zero, add_zero] at this
      exact this.symm
    have hc1 : P₂ k 1 = P₁ k 0 * R 0 1 + P₁ k 1 * R 1 1 := by
      have := congrFun (congrFun hP₁R k) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_three, hR21, mul_zero, add_zero] at this
      exact this.symm
    simp only [M, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Fin.isValue]
    rw [hc0, hc1]; ring
  have hsq : ∑ k : Fin 3, (P₂ k 0 * x + P₂ k 1 * y) ^ 2 =
      ∑ k : Fin 3, (P₁ k 0 * (M 0 0 * x + M 0 1 * y) + P₁ k 1 * (M 1 0 * x + M 1 1 * y)) ^ 2 :=
    Finset.sum_congr rfl fun k _ => by rw [hvec k]
  have h2lhs : ∑ k : Fin 3, (P₂ k 0 * x + P₂ k 1 * y) ^ 2 = 2 * f₂.eval x y := by
    simp only [Fin.sum_univ_three, eval] at h2_00 h2_01 h2_11 ⊢
    linear_combination x ^ 2 * h2_00 + (2 * x * y) * h2_01 + y ^ 2 * h2_11
  have h2rhs : ∑ k : Fin 3, (P₁ k 0 * (M 0 0 * x + M 0 1 * y) + P₁ k 1 * (M 1 0 * x + M 1 1 * y)) ^ 2 =
      2 * f₁.eval (M 0 0 * x + M 0 1 * y) (M 1 0 * x + M 1 1 * y) := by
    simp only [Fin.sum_univ_three, eval] at h1_00 h1_01 h1_11 ⊢
    linear_combination (M 0 0 * x + M 0 1 * y) ^ 2 * h1_00 +
      (2 * (M 0 0 * x + M 0 1 * y) * (M 1 0 * x + M 1 1 * y)) * h1_01 +
      (M 1 0 * x + M 1 1 * y) ^ 2 * h1_11
  linarith

/-- For squarefree `d`, `2 ^ d.primeFactors.card ≤ d.divisors.card`. -/
private lemma two_pow_primeFactors_le_divisors {d : ℕ} (hd_sf : Squarefree d) :
    2 ^ d.primeFactors.card ≤ d.divisors.card := by
  have hcard : 2 ^ d.primeFactors.card = d.primeFactors.powerset.card := (Finset.card_powerset _).symm
  rw [hcard]
  refine Finset.card_le_card_of_injOn (fun T => ∏ p ∈ T, p) ?_ ?_
  · intro T hT
    rw [Finset.mem_coe, Finset.mem_powerset] at hT
    rw [Finset.mem_coe, Nat.mem_divisors]
    refine ⟨?_, hd_sf.ne_zero⟩
    have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hd_sf
    rw [← hprod]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hT
  · intro T₁ hT₁ T₂ hT₂ heq
    rw [Finset.mem_coe, Finset.mem_powerset] at hT₁ hT₂
    dsimp only at heq
    ext p
    constructor
    · intro hp1
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (hT₁ hp1)
      have hdvd : p ∣ ∏ q ∈ T₂, q := heq ▸ Finset.dvd_prod_of_mem _ hp1
      obtain ⟨q, hq2, hpq⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hdvd
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors (hT₂ hq2)
      rwa [(Nat.prime_dvd_prime_iff_eq hpp hqp).mp hpq]
    · intro hp2
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (hT₂ hp2)
      have hdvd : p ∣ ∏ q ∈ T₁, q := heq.symm ▸ Finset.dvd_prod_of_mem _ hp2
      obtain ⟨q, hq1, hpq⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hdvd
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors (hT₁ hq1)
      rwa [(Nat.prime_dvd_prime_iff_eq hpp hqp).mp hpq]

set_option maxHeartbeats 600000 in
/-- Gauss's three-square class number lower bound: for squarefree `d ≡ 3 (mod 8)`,
`(reducedForms d).card ≤ 4 * d.divisors.card * (rep3Z d).card`. -/
theorem r3_ge_class_number {d : ℕ} (hd_sf : Squarefree d) (hd_mod : d % 8 = 3) :
    (reducedForms d).card ≤ 4 * d.divisors.card * (rep3Z d).card := by
  classical
  have hd_pos : 0 < d := by omega
  haveI := quadK_fact hd_pos
  haveI := quadK_numberField (d := d)
  set Cl := ClassGroup (NumberField.RingOfIntegers (QuadK d))
  -- Step 1: (reducedForms d).card ≤ 2 * Fintype.card Cl via f ↦ [idealOfBQF f]
  let clOfForm : BQF d → Cl := fun f =>
    ClassGroup.mk0 ⟨idealOfBQF hd_mod f, mem_nonZeroDivisors_of_ne_zero (idealOfBQF_ne_bot hd_mod f)⟩
  have hred_le_2cl : (reducedForms d).card ≤ 2 * Fintype.card Cl := by
    have hsum := Finset.card_eq_sum_card_fiberwise (f := clOfForm) (s := reducedForms d) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    rw [hsum]
    calc ∑ c : Cl, ((reducedForms d).filter (fun f => clOfForm f = c)).card
        ≤ ∑ _c : Cl, 2 := by
          refine Finset.sum_le_sum fun c _ => ?_
          by_cases hne : ((reducedForms d).filter (fun f => clOfForm f = c)).Nonempty
          · obtain ⟨f₀, hf₀⟩ := hne
            have hsub : (reducedForms d).filter (fun f => clOfForm f = c) ⊆ {f₀, f₀.conj} := by
              intro f hf
              have hf_red : f.isReduced := (mem_reducedForms_iff hd_pos f).mp (Finset.mem_filter.mp hf).1
              have hf₀_red : f₀.isReduced := (mem_reducedForms_iff hd_pos f₀).mp (Finset.mem_filter.mp hf₀).1
              have hceq : clOfForm f₀ = clOfForm f :=
                (Finset.mem_filter.mp hf₀).2.trans (Finset.mem_filter.mp hf).2.symm
              have hgl : GL2Equiv f₀ f := classGroup_eq_imp_gl2Equiv hd_sf hd_mod hceq
              rcases reduced_gl2Equiv_eq_or_conj hd_pos hf₀_red hf_red hgl with rfl | rfl
              · simp
              · simp
            exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
          · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]; omega
      _ = 2 * Fintype.card Cl := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  -- Step 2: Target genus coset S_gen has |Cl| ≤ d.divisors.card * S_gen.card
  obtain ⟨f₀, hf₀_dvd, hf₀_cop⟩ := exists_target_bqf hd_mod
  let χ := genusHom hd_sf hd_mod
  let c₀ : Cl := clOfForm f₀
  let S_gen : Finset Cl := Finset.univ.filter (fun c => χ c = χ c₀)
  have hcl_le_gen : Fintype.card Cl ≤ d.divisors.card * S_gen.card := by
    have hcard_ker : S_gen.card = Fintype.card χ.ker := by
      rw [← Finset.card_univ]
      refine Finset.card_bij (fun c hc => ⟨c * c₀⁻¹, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, (Finset.mem_filter.mp hc).2, mul_inv_cancel]⟩) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro c₁ _ c₂ _ heq
        exact mul_right_cancel (congrArg Subtype.val heq)
      · intro x _
        refine ⟨x.1 * c₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [map_mul, MonoidHom.mem_ker.mp x.2, one_mul]⟩, Subtype.ext (by group)⟩
    have hlag : Fintype.card Cl = Fintype.card χ.range * Fintype.card χ.ker := by
      have heq := Subgroup.card_eq_card_quotient_mul_card_subgroup χ.ker
      have hq : Fintype.card (Cl ⧸ χ.ker) = Fintype.card χ.range :=
        Fintype.card_congr (QuotientGroup.quotientKerEquivRange χ)
      rw [← hq]
      simpa [Nat.card_eq_fintype_card] using heq
    have hrange_le : Fintype.card χ.range ≤ d.divisors.card := by
      calc Fintype.card χ.range
          ≤ Fintype.card (d.primeFactors → ℤˣ) := Fintype.card_subtype_le _
        _ = (Fintype.card ℤˣ) ^ Fintype.card d.primeFactors := Fintype.card_fun
        _ = 2 ^ d.primeFactors.card := by
            rw [Fintype.card_coe]
            have hz : Fintype.card ℤˣ = 2 := by decide
            rw [hz]
        _ ≤ d.divisors.card := two_pow_primeFactors_le_divisors hd_sf
    rw [hlag, ← hcard_ker]
    exact Nat.mul_le_mul_right _ hrange_le
  -- Step 3: Map each c ∈ S_gen to v(c) ∈ rep3Z d with fiber size ≤ 2
  have hex_P : ∀ c ∈ S_gen, ∃ (f : BQF d) (P : Matrix (Fin 3) (Fin 3) ℤ),
      clOfForm f = c ∧ P.det = 1 ∧
      (∑ i : Fin 3, P i 0 * P i 0) = 2 * f.a ∧
      (∑ i : Fin 3, P i 0 * P i 1) = f.b ∧
      (∑ i : Fin 3, P i 1 * P i 1) = 2 * f.c := by
    intro c hc
    have hχc : χ c = χ c₀ := (Finset.mem_filter.mp hc).2
    obtain ⟨f, hfc, hfcop⟩ := exists_coprime_rep hd_sf hd_mod c
    have hleg : ∀ p : d.primeFactors,
        haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
        legendreSym p.1 (-2 * f.a) = 1 := by
      intro p
      haveI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
      have hpeq : χ c p = χ c₀ p := congrFun hχc p
      have h1 := genusHom_apply_bqf hd_sf hd_mod f hfcop p
      have h2 := genusHom_apply_bqf hd_sf hd_mod f₀ hf₀_cop p
      have hleg_fa : legendreSym p.1 f.a = legendreSym p.1 f₀.a := by
        have hval := congrArg (fun u : ℤˣ => (u : ℤ)) hpeq
        change ((χ c p : ℤˣ) : ℤ) = ((χ c₀ p : ℤˣ) : ℤ) at hval
        rw [← hfc] at hval
        rw [← h1, ← h2]; exact hval
      have hp_dvd : (p.1 : ℤ) ∣ 2 * f₀.a + 1 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_primeFactors p.2)) hf₀_dvd
      have hmod_neg : ((-2 * f₀.a : ℤ) : ZMod p.1) = (1 : ZMod p.1) := by
        have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p.1).mpr hp_dvd
        push_cast at h0 ⊢; linear_combination -h0
      have hleg_f0 : legendreSym p.1 (-2 * f₀.a) = 1 := by
        have : legendreSym p.1 (-2 * f₀.a) = legendreSym p.1 (1 : ℤ) := by
          unfold legendreSym; simpa using congrArg (quadraticChar (ZMod p.1)) hmod_neg
        rw [this]; unfold legendreSym; simp
      rw [legendreSym.mul, hleg_fa, ← legendreSym.mul]
      exact hleg_f0
    obtain ⟨P, hPdet, h00, h01, h11⟩ := exists_sl3_for_bqf hd_sf hd_mod f hleg
    exact ⟨f, P, hfc, hPdet, h00, h01, h11⟩
  let vOfClass : Cl → ℤ × ℤ × ℤ := fun c =>
    if hc : c ∈ S_gen then crossCols (hex_P c hc).choose_spec.choose else (0, 0, 0)
  have hS_le_2r3 : S_gen.card ≤ 2 * (rep3Z d).card := by
    have hmaps : ∀ c ∈ S_gen, vOfClass c ∈ rep3Z d := by
      intro c hc
      simp only [vOfClass, dif_pos hc]
      have hspec := (hex_P c hc).choose_spec.choose_spec
      exact crossCols_mem_rep3Z hspec.2.2.1 hspec.2.2.2.1 hspec.2.2.2.2
    have hsum := Finset.card_eq_sum_card_fiberwise hmaps
    rw [hsum]
    calc ∑ v ∈ rep3Z d, (S_gen.filter (fun c => vOfClass c = v)).card
        ≤ ∑ _v ∈ rep3Z d, 2 := by
          refine Finset.sum_le_sum fun v _ => ?_
          by_cases hne : (S_gen.filter (fun c => vOfClass c = v)).Nonempty
          · obtain ⟨c₁, hc₁⟩ := hne
            have hsub : S_gen.filter (fun c => vOfClass c = v) ⊆ {c₁, c₁⁻¹} := by
              intro c₂ hc₂
              have hc₁S : c₁ ∈ S_gen := (Finset.mem_filter.mp hc₁).1
              have hc₂S : c₂ ∈ S_gen := (Finset.mem_filter.mp hc₂).1
              have hv_eq : vOfClass c₁ = vOfClass c₂ :=
                (Finset.mem_filter.mp hc₁).2.trans (Finset.mem_filter.mp hc₂).2.symm
              simp only [vOfClass, dif_pos hc₁S, dif_pos hc₂S] at hv_eq
              set f₁ := (hex_P c₁ hc₁S).choose
              set P₁ := (hex_P c₁ hc₁S).choose_spec.choose
              have hs₁ := (hex_P c₁ hc₁S).choose_spec.choose_spec
              set f₂ := (hex_P c₂ hc₂S).choose
              set P₂ := (hex_P c₂ hc₂S).choose_spec.choose
              have hs₂ := (hex_P c₂ hc₂S).choose_spec.choose_spec
              have hgl : GL2Equiv f₁ f₂ :=
                gl2Equiv_of_crossCols_eq hs₁.2.1 hs₂.2.1 hs₁.2.2.1 hs₁.2.2.2.1 hs₁.2.2.2.2
                  hs₂.2.2.1 hs₂.2.2.2.1 hs₂.2.2.2.2 hv_eq
              obtain ⟨r₁, hr₁, hstep₁⟩ := exists_reduced_stepEquiv hd_pos f₁
              obtain ⟨r₂, hr₂, hstep₂⟩ := exists_reduced_stepEquiv hd_pos f₂
              have hgl_r : GL2Equiv r₁ r₂ :=
                (hstep₁.toSL2.toGL2.symm.trans hgl).trans hstep₂.toSL2.toGL2
              have hc₁_eq : c₁ = clOfForm r₁ := by
                rw [← hs₁.1]; exact sl2Equiv_imp_classGroup_eq hd_sf hd_mod hstep₁.toSL2
              have hc₂_eq : c₂ = clOfForm r₂ := by
                rw [← hs₂.1]; exact sl2Equiv_imp_classGroup_eq hd_sf hd_mod hstep₂.toSL2
              rcases reduced_gl2Equiv_eq_or_conj hd_pos hr₁ hr₂ hgl_r with rfl | rfl
              · simp [hc₁_eq, hc₂_eq]
              · have hinv : clOfForm r₁.conj = (clOfForm r₁)⁻¹ := by
                  rw [eq_inv_iff_mul_eq_one]
                  dsimp only [clOfForm]
                  rw [← map_mul, ClassGroup.mk0_eq_one_iff]
                  change Submodule.IsPrincipal (idealOfBQF hd_mod r₁.conj * idealOfBQF hd_mod r₁)
                  rw [mul_comm, idealOfBQF_mul_conj hd_sf hd_mod r₁]
                  exact ⟨⟨((r₁.a : ℤ) : NumberField.RingOfIntegers (QuadK d)), rfl⟩⟩
                simp [hc₁_eq, hc₂_eq, hinv]
            exact (Finset.card_le_card hsub).trans Finset.card_le_two
          · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]; omega
      _ = 2 * (rep3Z d).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  calc (reducedForms d).card
      ≤ 2 * Fintype.card Cl := hred_le_2cl
    _ ≤ 2 * (d.divisors.card * S_gen.card) := Nat.mul_le_mul_left 2 hcl_le_gen
    _ ≤ 2 * (d.divisors.card * (2 * (rep3Z d).card)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hS_le_2r3)
    _ = 4 * d.divisors.card * (rep3Z d).card := by ring

end E940.Genus

end ModGenus

section ModMain

open Finset Filter Real
open E940.Siegel E940.QuaternionLift E940.ClassNumber E940.ClassNumber.BQF E940.Genus
open E940.QuaternionLift.HQ (rep3Z mem_rep3Z_iff r3_mul_sq_ge_mul_totient)

namespace E940.Main

/-- For squarefree `d ≥ 1`, `d.divisors.card ≤ 2^(2^500) * d^(1/500)`. -/
private lemma squarefree_divisors_card_le {d : ℕ} (hd_sf : Squarefree d) :
    (d.divisors.card : ℝ) ≤ ((2 : ℝ) ^ (2 ^ 500 : ℕ)) * (d : ℝ) ^ (1 / 500 : ℝ) := by
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd_sf.ne_zero
  -- For squarefree d, d.divisors.card = 2 ^ d.primeFactors.card
  have hdiv_eq : d.divisors.card = 2 ^ d.primeFactors.card := by
    have hpow : 2 ^ d.primeFactors.card = d.primeFactors.powerset.card := (Finset.card_powerset _).symm
    rw [hpow]
    symm
    refine Finset.card_bij (fun T _ => ∏ p ∈ T, p) ?_ ?_ ?_
    · intro T hT
      rw [Finset.mem_powerset] at hT
      rw [Nat.mem_divisors]
      refine ⟨?_, hd_sf.ne_zero⟩
      rw [← Nat.prod_primeFactors_of_squarefree hd_sf]
      exact Finset.prod_dvd_prod_of_subset _ _ _ hT
    · intro T₁ hT₁ T₂ hT₂ heq
      rw [Finset.mem_powerset] at hT₁ hT₂
      ext p
      constructor
      · intro hp1
        have hpp := Nat.prime_of_mem_primeFactors (hT₁ hp1)
        obtain ⟨q, hq2, hpq⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp
          (heq ▸ Finset.dvd_prod_of_mem _ hp1)
        rwa [(Nat.prime_dvd_prime_iff_eq hpp (Nat.prime_of_mem_primeFactors (hT₂ hq2))).mp hpq]
      · intro hp2
        have hpp := Nat.prime_of_mem_primeFactors (hT₂ hp2)
        obtain ⟨q, hq1, hpq⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp
          (heq.symm ▸ Finset.dvd_prod_of_mem _ hp2)
        rwa [(Nat.prime_dvd_prime_iff_eq hpp (Nat.prime_of_mem_primeFactors (hT₁ hq1))).mp hpq]
    · intro k hk
      obtain ⟨hkd, _⟩ := Nat.mem_divisors.mp hk
      have hksf : Squarefree k := hd_sf.squarefree_of_dvd hkd
      refine ⟨k.primeFactors, Finset.mem_powerset.mpr (Nat.primeFactors_mono hkd hd_sf.ne_zero),
        Nat.prod_primeFactors_of_squarefree hksf⟩
  set P₀ : ℕ := 2 ^ 500
  have hprod_d : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd_sf]
  have hprod_rpow : (d : ℝ) ^ (1 / 500 : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) ^ (1 / 500 : ℝ) := by
    rw [hprod_d, Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
  have h2_le : ∀ p ∈ d.primeFactors,
      (2 : ℝ) ≤ (if p < P₀ then (2 : ℝ) else 1) * (p : ℝ) ^ (1 / 500 : ℝ) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    split_ifs with hlt
    · have h1 : (1 : ℝ) ≤ (p : ℝ) ^ (1 / 500 : ℝ) := Real.one_le_rpow hp1 (by norm_num)
      linarith
    · rw [one_mul]
      have hge : ((2 : ℝ) ^ (500 : ℕ)) ≤ (p : ℝ) := by exact_mod_cast (show P₀ ≤ p by omega)
      have hr := Real.rpow_le_rpow (pow_nonneg (by norm_num) _) hge (by norm_num : (0 : ℝ) ≤ 1 / 500)
      have hpow2 : ((2 : ℝ) ^ (500 : ℕ)) ^ (1 / 500 : ℝ) = 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      linarith
  have hsmall_le : (∏ p ∈ d.primeFactors, if p < P₀ then (2 : ℝ) else 1) ≤ (2 : ℝ) ^ P₀ := by
    have h1 : (∏ p ∈ d.primeFactors, if p < P₀ then (2 : ℝ) else 1) =
        (2 : ℝ) ^ (d.primeFactors.filter (· < P₀)).card := by
      rw [← Finset.prod_filter, Finset.prod_const]
    rw [h1]
    have hcard : (d.primeFactors.filter (· < P₀)).card ≤ P₀ := by
      have hsub : d.primeFactors.filter (· < P₀) ⊆ Finset.range P₀ := fun p hp =>
        Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      exact (Finset.card_le_card hsub).trans (by rw [Finset.card_range])
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcard
  rw [hdiv_eq, Nat.cast_pow, Nat.cast_ofNat, ← Finset.prod_const (s := d.primeFactors), hprod_rpow]
  calc (∏ _p ∈ d.primeFactors, (2 : ℝ))
      ≤ ∏ p ∈ d.primeFactors, ((if p < P₀ then (2 : ℝ) else 1) * (p : ℝ) ^ (1 / 500 : ℝ)) :=
        Finset.prod_le_prod (fun _ _ => by norm_num) h2_le
    _ = (∏ p ∈ d.primeFactors, if p < P₀ then (2 : ℝ) else 1) *
          (∏ p ∈ d.primeFactors, (p : ℝ) ^ (1 / 500 : ℝ)) := Finset.prod_mul_distrib
    _ ≤ ((2 : ℝ) ^ P₀) * (∏ p ∈ d.primeFactors, (p : ℝ) ^ (1 / 500 : ℝ)) :=
        mul_le_mul_of_nonneg_right hsmall_le
          (Finset.prod_nonneg fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)

/-- For all `s ≥ 1`, `(1/2)^(2^500) * s^(499/500) ≤ s.totient`. -/
private lemma totient_ge_rpow {s : ℕ} (hs : 1 ≤ s) :
    ((1 / 2 : ℝ) ^ (2 ^ 500 : ℕ)) * (s : ℝ) ^ (499 / 500 : ℝ) ≤ (s.totient : ℝ) := by
  set P₀ : ℕ := 2 ^ 500
  have hs0 : s ≠ 0 := by omega
  have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have htot : (s.totient : ℝ) = (s : ℝ) * ∏ p ∈ s.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have hq := Nat.totient_eq_mul_prod_factors s
    have hR := congrArg (Rat.cast (K := ℝ)) hq
    simpa [Rat.cast_prod] using hR
  have hprod_le_s : (∏ p ∈ s.primeFactors, (p : ℝ)) ≤ (s : ℝ) := by
    have hdvd : (∏ p ∈ s.primeFactors, p) ∣ s := Nat.prod_primeFactors_dvd s
    have hle : (∏ p ∈ s.primeFactors, p) ≤ s := Nat.le_of_dvd (by omega) hdvd
    rw [← Nat.cast_prod]
    exact_mod_cast hle
  have hprod_pos : (0 : ℝ) < ∏ p ∈ s.primeFactors, (p : ℝ) :=
    Finset.prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hs_neg_le : (s : ℝ) ^ (-(1 / 500 : ℝ)) ≤ ∏ p ∈ s.primeFactors, (p : ℝ) ^ (-(1 / 500 : ℝ)) := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
    exact Real.rpow_le_rpow_of_nonpos hprod_pos hprod_le_s (by norm_num)
  have hterm_ge : ∀ p ∈ s.primeFactors,
      (if p < P₀ then (1 / 2 : ℝ) else 1) * (p : ℝ) ^ (-(1 / 500 : ℝ)) ≤ 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    have h1sub : (1 / 2 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by
      have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
        rw [inv_le_comm₀ hp_pos (by norm_num)]; linarith
      linarith
    split_ifs with hlt
    · have hle1 : (p : ℝ) ^ (-(1 / 500 : ℝ)) ≤ 1 := by
        rw [Real.rpow_neg hp_pos.le]
        exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith) (by norm_num))
      exact (mul_le_mul_of_nonneg_left hle1 (by norm_num)).trans (by linarith)
    · rw [one_mul, Real.rpow_neg hp_pos.le]
      have hge : ((2 : ℝ) ^ (500 : ℕ)) ≤ (p : ℝ) := by exact_mod_cast (show P₀ ≤ p by omega)
      have hr := Real.rpow_le_rpow (pow_nonneg (by norm_num) _) hge (by norm_num : (0 : ℝ) ≤ 1 / 500)
      have hpow2 : ((2 : ℝ) ^ (500 : ℕ)) ^ (1 / 500 : ℝ) = 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      have h2le : (2 : ℝ) ≤ (p : ℝ) ^ (1 / 500 : ℝ) := by linarith
      have hinv : ((p : ℝ) ^ (1 / 500 : ℝ))⁻¹ ≤ 1 / 2 := by
        rw [inv_le_comm₀ (Real.rpow_pos_of_pos hp_pos _) (by norm_num)]; linarith
      linarith
  have hsmall_ge : ((1 / 2 : ℝ) ^ P₀) ≤ ∏ p ∈ s.primeFactors, if p < P₀ then (1 / 2 : ℝ) else 1 := by
    have h1 : (∏ p ∈ s.primeFactors, if p < P₀ then (1 / 2 : ℝ) else 1) =
        (1 / 2 : ℝ) ^ (s.primeFactors.filter (· < P₀)).card := by
      rw [← Finset.prod_filter, Finset.prod_const]
    rw [h1]
    have hcard : (s.primeFactors.filter (· < P₀)).card ≤ P₀ := by
      have hsub : s.primeFactors.filter (· < P₀) ⊆ Finset.range P₀ := fun p hp =>
        Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      exact (Finset.card_le_card hsub).trans (by rw [Finset.card_range])
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
  have hprod_ge : ((1 / 2 : ℝ) ^ P₀) * (s : ℝ) ^ (-(1 / 500 : ℝ)) ≤
      ∏ p ∈ s.primeFactors, (1 - (p : ℝ)⁻¹) := by
    calc ((1 / 2 : ℝ) ^ P₀) * (s : ℝ) ^ (-(1 / 500 : ℝ))
        ≤ (∏ p ∈ s.primeFactors, if p < P₀ then (1 / 2 : ℝ) else 1) *
            (∏ p ∈ s.primeFactors, (p : ℝ) ^ (-(1 / 500 : ℝ))) :=
          mul_le_mul hsmall_ge hs_neg_le (Real.rpow_nonneg hs_pos.le _)
            (Finset.prod_nonneg fun _ _ => by split_ifs <;> norm_num)
      _ = ∏ p ∈ s.primeFactors, ((if p < P₀ then (1 / 2 : ℝ) else 1) * (p : ℝ) ^ (-(1 / 500 : ℝ))) :=
          Finset.prod_mul_distrib.symm
      _ ≤ ∏ p ∈ s.primeFactors, (1 - (p : ℝ)⁻¹) :=
          Finset.prod_le_prod (fun p _ =>
            mul_nonneg (by split_ifs <;> norm_num) (Real.rpow_nonneg (Nat.cast_nonneg p) _)) hterm_ge
  have hexp : (s : ℝ) ^ (499 / 500 : ℝ) = (s : ℝ) * (s : ℝ) ^ (-(1 / 500 : ℝ)) := by
    calc (s : ℝ) ^ (499 / 500 : ℝ)
        = (s : ℝ) ^ ((1 : ℝ) + -(1 / 500 : ℝ)) := by congr 1; norm_num
      _ = (s : ℝ) ^ (1 : ℝ) * (s : ℝ) ^ (-(1 / 500 : ℝ)) := Real.rpow_add hs_pos _ _
      _ = (s : ℝ) * (s : ℝ) ^ (-(1 / 500 : ℝ)) := by rw [Real.rpow_one]
  rw [htot, hexp, ← mul_assoc, mul_comm ((1 / 2 : ℝ) ^ P₀) (s : ℝ), mul_assoc]
  exact mul_le_mul_of_nonneg_left hprod_ge hs_pos.le

/-- Passing from signed integer triples `rep3Z (5 * n)` to nonnegative triples `S n` loses at most a factor of `8`. -/
private lemma card_rep3Z_le_eight_mul_S (n : ℕ) :
    (rep3Z (5 * n)).card ≤
      8 * (((Finset.range (5 * n + 1)) ×ˢ ((Finset.range (5 * n + 1)) ×ˢ (Finset.range (5 * n + 1)))).filter
        (fun v : ℕ × ℕ × ℕ => 5 * n = v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)).card := by
  classical
  set S_n := ((Finset.range (5 * n + 1)) ×ˢ ((Finset.range (5 * n + 1)) ×ˢ (Finset.range (5 * n + 1)))).filter
    (fun v : ℕ × ℕ × ℕ => 5 * n = v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)
  let φ : ℤ × ℤ × ℤ → ℕ × ℕ × ℕ := fun v => (v.1.natAbs, v.2.1.natAbs, v.2.2.natAbs)
  have hmaps : ∀ v ∈ rep3Z (5 * n), φ v ∈ S_n := by
    intro v hv
    rw [mem_rep3Z_iff] at hv
    have hsq : v.1.natAbs ^ 2 + v.2.1.natAbs ^ 2 + v.2.2.natAbs ^ 2 = 5 * n := by
      have hcast : ((v.1.natAbs ^ 2 + v.2.1.natAbs ^ 2 + v.2.2.natAbs ^ 2 : ℕ) : ℤ) = ((5 * n : ℕ) : ℤ) := by
        push_cast; rw [sq_abs, sq_abs, sq_abs]; exact_mod_cast hv
      exact_mod_cast hcast
    have hb1 : v.1.natAbs < 5 * n + 1 := by nlinarith
    have hb2 : v.2.1.natAbs < 5 * n + 1 := by nlinarith
    have hb3 : v.2.2.natAbs < 5 * n + 1 := by nlinarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hb1,
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr hb2, Finset.mem_range.mpr hb3⟩⟩, hsq.symm⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ w ∈ S_n, ((rep3Z (5 * n)).filter (fun v => φ v = w)).card
      ≤ ∑ _w ∈ S_n, 8 := by
        refine Finset.sum_le_sum fun w _ => ?_
        let box : Finset (ℤ × ℤ × ℤ) :=
          ({(w.1 : ℤ), -(w.1 : ℤ)} : Finset ℤ) ×ˢ
            (({(w.2.1 : ℤ), -(w.2.1 : ℤ)} : Finset ℤ) ×ˢ ({(w.2.2 : ℤ), -(w.2.2 : ℤ)} : Finset ℤ))
        have hsub : (rep3Z (5 * n)).filter (fun v => φ v = w) ⊆ box := by
          intro v hv
          have hφ : φ v = w := (Finset.mem_filter.mp hv).2
          have h1 : v.1 = (w.1 : ℤ) ∨ v.1 = -(w.1 : ℤ) := by
            have := congrArg Prod.fst hφ; dsimp only [φ] at this
            rcases Int.natAbs_eq v.1 with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
          have h2 : v.2.1 = (w.2.1 : ℤ) ∨ v.2.1 = -(w.2.1 : ℤ) := by
            have := congrArg (fun p => p.2.1) hφ; dsimp only [φ] at this
            rcases Int.natAbs_eq v.2.1 with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
          have h3 : v.2.2 = (w.2.2 : ℤ) ∨ v.2.2 = -(w.2.2 : ℤ) := by
            have := congrArg (fun p => p.2.2) hφ; dsimp only [φ] at this
            rcases Int.natAbs_eq v.2.2 with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
          simp only [box, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨h1, h2, h3⟩
        have hbox_le : box.card ≤ 8 := by
          dsimp only [box]
          rw [Finset.card_product, Finset.card_product]
          have c1 : ({(w.1 : ℤ), -(w.1 : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_le_two
          have c2 : ({(w.2.1 : ℤ), -(w.2.1 : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_le_two
          have c3 : ({(w.2.2 : ℤ), -(w.2.2 : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_le_two
          exact (Nat.mul_le_mul c1 (Nat.mul_le_mul c2 c3)).trans (by norm_num)
        exact (Finset.card_le_card hsub).trans hbox_le
    _ = 8 * S_n.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem erdos_940_H2_R1_H1 : OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R1.H1 := by
  unfold OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R1.H1
  dsimp only
  obtain ⟨C_S, hC_Spos, hSiegel⟩ := siegel_theorem_jacobi (1 / 500 : ℝ) (by norm_num)
  set C₁ : ℝ := (2 : ℝ) ^ (2 ^ 500 : ℕ)
  set C₂ : ℝ := (1 / 2 : ℝ) ^ (2 ^ 500 : ℕ)
  have hC₁pos : 0 < C₁ := pow_pos (by norm_num) _
  have hC₂pos : 0 < C₂ := pow_pos (by norm_num) _
  set C_tot : ℝ := C_S * C₂ / (256 * C₁)
  have hC_tot_pos : 0 < C_tot := div_pos (mul_pos hC_Spos hC₂pos) (mul_pos (by norm_num) hC₁pos)
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (6 / 1000 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 6 / 1000)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop C_tot⁻¹, Filter.eventually_ge_atTop 1] with n hbig hn1 hmod
  -- Decompose 5 * n = s^2 * d with d squarefree
  obtain ⟨d, s, hds, hd_sf⟩ := Nat.sq_mul_squarefree (5 * n)
  have h5n_mod : (5 * n) % 8 = 3 := by omega
  have hs_odd : ¬ 2 ∣ s := by
    intro ⟨k, hk⟩
    have : 4 ∣ 5 * n := ⟨k ^ 2 * d, by rw [← hds, hk]; ring⟩
    omega
  have hs_mod2 : s % 2 = 1 := by
    have : s % 2 ≠ 0 := fun h => hs_odd (Nat.dvd_of_mod_eq_zero h)
    omega
  have hs_sq_mod : s ^ 2 % 8 = 1 := by
    obtain ⟨j, hj⟩ : ∃ j, s = 2 * j + 1 := ⟨s / 2, by omega⟩
    obtain ⟨t, ht⟩ : ∃ t, j * (j + 1) = 2 * t := (Nat.even_mul_succ_self j).exists_two_nsmul _
    have : s ^ 2 = 8 * t + 1 := by subst hj; ring_nf; nlinarith [ht]
    omega
  have hd_mod : d % 8 = 3 := by
    have h1 : (5 * n) % 8 = (s ^ 2 % 8 * (d % 8)) % 8 := by rw [← Nat.mul_mod, hds]
    rw [h5n_mod, hs_sq_mod, one_mul] at h1
    omega
  have hd_gt : 1 < d := by omega
  have hd_pos : 0 < d := by omega
  have hs_pos : 1 ≤ s := by
    by_contra h; push Not at h
    have hs0 : s = 0 := by omega
    rw [hs0] at hds; simp at hds; omega
  haveI : NeZero d := ⟨hd_pos.ne'⟩
  -- Step 1: Siegel lower bound on L(1, jacobiChar d)
  have hL_ge := hSiegel d hd_gt hd_sf hd_mod
  -- Step 2: Class number lower bound
  have hCl_ge := class_number_lower_bound hd_gt hd_sf hd_mod
  -- Step 3: Gauss 3-square lower bound
  have hGauss : ((reducedForms d).card : ℝ) ≤ 4 * (d.divisors.card : ℝ) * ((rep3Z d).card : ℝ) := by
    exact_mod_cast r3_ge_class_number hd_sf hd_mod
  -- Step 4: Quaternion lifting bound for s^2 * d = 5 * n
  have hLift : ((rep3Z d).card : ℝ) * (s.totient : ℝ) ≤ ((rep3Z (5 * n)).card : ℝ) := by
    have h := r3_mul_sq_ge_mul_totient hd_sf (Nat.odd_iff.mpr hs_mod2)
    rw [mul_comm d (s ^ 2), hds] at h
    exact_mod_cast h
  -- Step 5: Signed to unsigned bound
  have hSign : ((rep3Z (5 * n)).card : ℝ) ≤
      8 * (((((Finset.range (5 * n + 1)) ×ˢ ((Finset.range (5 * n + 1)) ×ˢ (Finset.range (5 * n + 1)))).filter
        (fun v : ℕ × ℕ × ℕ => 5 * n = v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)).card : ℝ)) := by
    exact_mod_cast card_rep3Z_le_eight_mul_S n
  -- Step 6: Combine inequalities
  have hdiv_le : (d.divisors.card : ℝ) ≤ C₁ * (d : ℝ) ^ (1 / 500 : ℝ) :=
    squarefree_divisors_card_le hd_sf
  have htot_ge : C₂ * (s : ℝ) ^ (499 / 500 : ℝ) ≤ (s.totient : ℝ) :=
    totient_ge_rpow hs_pos
  have hdR_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
  have hsR_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs_pos
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hr3d_ge : (C_S / (32 * C₁)) * (d : ℝ) ^ (248 / 500 : ℝ) ≤ ((rep3Z d).card : ℝ) := by
    have h1 : (Real.sqrt (d : ℝ) / 8) * (C_S * (d : ℝ) ^ (-(1 / 500 : ℝ))) ≤
        4 * (C₁ * (d : ℝ) ^ (1 / 500 : ℝ)) * ((rep3Z d).card : ℝ) := by
      have ha : (Real.sqrt (d : ℝ) / 8) * (C_S * (d : ℝ) ^ (-(1 / 500 : ℝ))) ≤
          (Real.sqrt (d : ℝ) / 8) * (DirichletCharacter.LFunction (jacobiChar d hd_gt) 1).re :=
        mul_le_mul_of_nonneg_left hL_ge (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
      have hb : 4 * (d.divisors.card : ℝ) * ((rep3Z d).card : ℝ) ≤
          4 * (C₁ * (d : ℝ) ^ (1 / 500 : ℝ)) * ((rep3Z d).card : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv_le (by norm_num)) (Nat.cast_nonneg _)
      linarith
    have hsqrt_eq : Real.sqrt (d : ℝ) = (d : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow (d : ℝ)
    have hpow_comb : (d : ℝ) ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-(1 / 500 : ℝ)) =
        (d : ℝ) ^ (1 / 500 : ℝ) * (d : ℝ) ^ (248 / 500 : ℝ) := by
      rw [← Real.rpow_add hdR_pos, ← Real.rpow_add hdR_pos]; congr 1; norm_num
    rw [hsqrt_eq] at h1
    have h2 : (C_S / 8) * ((d : ℝ) ^ (1 / 500 : ℝ) * (d : ℝ) ^ (248 / 500 : ℝ)) ≤
        (4 * C₁ * (d : ℝ) ^ (1 / 500 : ℝ)) * ((rep3Z d).card : ℝ) := by
      rw [← hpow_comb]; linarith
    have hdiv_pos : (0 : ℝ) < 4 * C₁ * (d : ℝ) ^ (1 / 500 : ℝ) :=
      mul_pos (mul_pos (by norm_num) hC₁pos) (Real.rpow_pos_of_pos hdR_pos _)
    rw [show (C_S / 8) * ((d : ℝ) ^ (1 / 500 : ℝ) * (d : ℝ) ^ (248 / 500 : ℝ)) =
        (4 * C₁ * (d : ℝ) ^ (1 / 500 : ℝ)) * ((C_S / (32 * C₁)) * (d : ℝ) ^ (248 / 500 : ℝ)) by
          field_simp; ring] at h2
    exact le_of_mul_le_mul_left h2 hdiv_pos
  have h5n_eq : (5 * (n : ℝ)) = (s : ℝ) ^ 2 * (d : ℝ) := by exact_mod_cast hds.symm
  have hpow_prod : (n : ℝ) ^ (248 / 500 : ℝ) ≤ (d : ℝ) ^ (248 / 500 : ℝ) * (s : ℝ) ^ (499 / 500 : ℝ) := by
    have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos
    have hs_exp : (s : ℝ) ^ (496 / 500 : ℝ) ≤ (s : ℝ) ^ (499 / 500 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num)
    have hsq_rpow : ((s : ℝ) ^ 2) ^ (248 / 500 : ℝ) = (s : ℝ) ^ (496 / 500 : ℝ) := by
      rw [show (s : ℝ) ^ 2 = (s : ℝ) ^ (2 : ℕ) by rfl, ← Real.rpow_natCast,
        ← Real.rpow_mul hsR_pos.le]; congr 1; norm_num
    have h5n_ge : (n : ℝ) ≤ (s : ℝ) ^ 2 * (d : ℝ) := by linarith [h5n_eq]
    calc (n : ℝ) ^ (248 / 500 : ℝ)
        ≤ ((s : ℝ) ^ 2 * (d : ℝ)) ^ (248 / 500 : ℝ) :=
          Real.rpow_le_rpow hnR_pos.le h5n_ge (by norm_num)
      _ = ((s : ℝ) ^ 2) ^ (248 / 500 : ℝ) * (d : ℝ) ^ (248 / 500 : ℝ) :=
          Real.mul_rpow (sq_nonneg _) hdR_pos.le
      _ = (d : ℝ) ^ (248 / 500 : ℝ) * (s : ℝ) ^ (496 / 500 : ℝ) := by rw [hsq_rpow, mul_comm]
      _ ≤ (d : ℝ) ^ (248 / 500 : ℝ) * (s : ℝ) ^ (499 / 500 : ℝ) :=
          mul_le_mul_of_nonneg_left hs_exp (Real.rpow_nonneg hdR_pos.le _)
  have hS_ge_tot : C_tot * (n : ℝ) ^ (248 / 500 : ℝ) ≤
      (((((Finset.range (5 * n + 1)) ×ˢ ((Finset.range (5 * n + 1)) ×ˢ (Finset.range (5 * n + 1)))).filter
        (fun v : ℕ × ℕ × ℕ => 5 * n = v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)).card : ℝ)) := by
    have hmul := mul_le_mul hr3d_ge htot_ge (mul_nonneg hC₂pos.le (Real.rpow_nonneg hsR_pos.le _)) (Nat.cast_nonneg _)
    have h1 : (C_S * C₂ / (32 * C₁)) * ((d : ℝ) ^ (248 / 500 : ℝ) * (s : ℝ) ^ (499 / 500 : ℝ)) ≤
        ((rep3Z (5 * n)).card : ℝ) := by
      have heq : (C_S / (32 * C₁)) * (d : ℝ) ^ (248 / 500 : ℝ) * (C₂ * (s : ℝ) ^ (499 / 500 : ℝ)) =
          (C_S * C₂ / (32 * C₁)) * ((d : ℝ) ^ (248 / 500 : ℝ) * (s : ℝ) ^ (499 / 500 : ℝ)) := by ring
      linarith [hmul, hLift]
    have h2 : (C_S * C₂ / (32 * C₁)) * (n : ℝ) ^ (248 / 500 : ℝ) ≤ ((rep3Z (5 * n)).card : ℝ) :=
      (mul_le_mul_of_nonneg_left hpow_prod
        (div_nonneg (mul_nonneg hC_Spos.le hC₂pos.le) (mul_nonneg (by norm_num) hC₁pos.le))).trans h1
    have h8 : C_S * C₂ / (32 * C₁) = 8 * C_tot := by
      dsimp only [C_tot]; field_simp; ring
    rw [h8] at h2
    linarith [h2, hSign]
  have hfactor : 1 ≤ C_tot * (n : ℝ) ^ (6 / 1000 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hbig hC_tot_pos.le
    rwa [mul_inv_cancel₀ hC_tot_pos.ne'] at this
  have hexp_split : (n : ℝ) ^ (248 / 500 : ℝ) = (n : ℝ) ^ (6 / 1000 : ℝ) * (n : ℝ) ^ (49 / 100 : ℝ) := by
    rw [← Real.rpow_add hnR_pos]; congr 1; norm_num
  calc (n : ℝ) ^ (49 / 100 : ℝ)
      = 1 * (n : ℝ) ^ (49 / 100 : ℝ) := (one_mul _).symm
    _ ≤ (C_tot * (n : ℝ) ^ (6 / 1000 : ℝ)) * (n : ℝ) ^ (49 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hnR_pos.le _)
    _ = C_tot * (n : ℝ) ^ (248 / 500 : ℝ) := by rw [hexp_split, mul_assoc]
    _ ≤ _ := hS_ge_tot

end E940.Main

theorem OMA.solution : OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R1.H1 :=
  E940.Main.erdos_940_H2_R1_H1

end ModMain
