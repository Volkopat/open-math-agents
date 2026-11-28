import OMAReductions.R_EswarathasanLevineConjecture_eswarathasan_levine_harmonic_conjecture_R2
import Mathlib

namespace OMA.EswH1

/-- `x` is `p`-integral -/
def PI (p : ℕ) (x : ℚ) : Prop := ¬ p ∣ x.den

/-- `a ≡ b (mod p^e)` for rationals -/
def Cg (p e : ℕ) (a b : ℚ) : Prop := PI p ((a - b) / (p : ℚ) ^ e)

section
variable {p : ℕ} (hp : p.Prime)
include hp

lemma PI_iff (x : ℚ) : PI p x ↔ ∃ a : ℤ, ∃ d : ℕ, ¬ p ∣ d ∧ x * d = a := by
  constructor
  · intro h
    exact ⟨x.num, x.den, h, Rat.mul_den_eq_num x⟩
  · rintro ⟨a, d, hd, hx⟩ hpd
    apply hd
    have h1 : (x.num : ℚ) * d = a * x.den := by
      rw [← hx, ← Rat.mul_den_eq_num x]; ring
    have h2 : x.num * (d : ℤ) = a * (x.den : ℤ) := by exact_mod_cast h1
    have h3 : (x.den : ℤ) ∣ x.num * d := ⟨a, by rw [h2]; ring⟩
    have hc : IsCoprime (x.den : ℤ) x.num := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd, Nat.coprime_comm] using x.reduced
    have h4 : (x.den : ℤ) ∣ (d : ℤ) := hc.dvd_of_dvd_mul_left h3
    exact Nat.dvd_trans hpd (Int.natCast_dvd_natCast.mp h4)

lemma ndvd_mul {a b : ℕ} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ a * b := by
  intro h
  rcases hp.dvd_mul.mp h with h | h
  · exact ha h
  · exact hb h

lemma PI_add {x y : ℚ} (hx : PI p x) (hy : PI p y) : PI p (x + y) := by
  obtain ⟨a, d, hd, hxd⟩ := (PI_iff hp x).mp hx
  obtain ⟨b, e, he, hye⟩ := (PI_iff hp y).mp hy
  refine (PI_iff hp _).mpr ⟨a * e + b * d, d * e, ndvd_mul hp hd he, ?_⟩
  push_cast
  rw [← hxd, ← hye]; ring

lemma PI_mul {x y : ℚ} (hx : PI p x) (hy : PI p y) : PI p (x * y) := by
  obtain ⟨a, d, hd, hxd⟩ := (PI_iff hp x).mp hx
  obtain ⟨b, e, he, hye⟩ := (PI_iff hp y).mp hy
  refine (PI_iff hp _).mpr ⟨a * b, d * e, ndvd_mul hp hd he, ?_⟩
  push_cast
  rw [← hxd, ← hye]; ring

lemma PI_int (a : ℤ) : PI p (a : ℚ) :=
  (PI_iff hp _).mpr ⟨a, 1, hp.not_dvd_one, by simp⟩

lemma PI_neg {x : ℚ} (hx : PI p x) : PI p (-x) := by
  have := PI_mul hp (PI_int hp (-1)) hx
  simpa using this

lemma PI_sub {x y : ℚ} (hx : PI p x) (hy : PI p y) : PI p (x - y) := by
  rw [sub_eq_add_neg]; exact PI_add hp hx (PI_neg hp hy)

lemma PI_zero : PI p 0 := by simpa using PI_int hp 0

lemma PI_inv {s : ℕ} (hs : ¬ p ∣ s) : PI p ((s : ℚ)⁻¹) := by
  have hs0 : (s : ℚ) ≠ 0 := by
    have : s ≠ 0 := by rintro rfl; exact hs (dvd_zero p)
    exact_mod_cast this
  refine (PI_iff hp _).mpr ⟨1, s, hs, ?_⟩
  field_simp
  simp

lemma PI_pow {x : ℚ} (hx : PI p x) (n : ℕ) : PI p (x ^ n) := by
  induction n with
  | zero => simpa using PI_int hp 1
  | succ n ih => rw [pow_succ]; exact PI_mul hp ih hx

lemma PI_sum (n : ℕ) (f : ℕ → ℚ) (h : ∀ i < n, PI p (f i)) :
    PI p (∑ i ∈ Finset.range n, f i) := by
  induction n with
  | zero => simpa using PI_zero hp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact PI_add hp (ih (fun i hi => h i (by omega))) (h n (by omega))

lemma Cg_iff (e : ℕ) (a b : ℚ) : Cg p e a b ↔ ∃ u, PI p u ∧ a = b + (p : ℚ) ^ e * u := by
  have hp0 : (p : ℚ) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    field_simp; ring
  · rintro ⟨u, hu, rfl⟩
    unfold Cg
    have : (b + (p : ℚ) ^ e * u - b) / (p : ℚ) ^ e = u := by field_simp; ring
    rw [this]; exact hu

lemma Cg_refl (e : ℕ) (a : ℚ) : Cg p e a a := by
  unfold Cg; simpa using PI_zero hp

lemma Cg_add {e : ℕ} {a b c d : ℚ} (h1 : Cg p e a b) (h2 : Cg p e c d) :
    Cg p e (a + c) (b + d) := by
  unfold Cg at *
  have : (a + c - (b + d)) / (p : ℚ) ^ e = (a - b) / (p : ℚ) ^ e + (c - d) / (p : ℚ) ^ e := by ring
  rw [this]; exact PI_add hp h1 h2

lemma Cg_symm {e : ℕ} {a b : ℚ} (h : Cg p e a b) : Cg p e b a := by
  unfold Cg at *
  have : (b - a) / (p : ℚ) ^ e = -((a - b) / (p : ℚ) ^ e) := by ring
  rw [this]; exact PI_neg hp h

lemma Cg_trans {e : ℕ} {a b c : ℚ} (h1 : Cg p e a b) (h2 : Cg p e b c) : Cg p e a c := by
  unfold Cg at *
  have : (a - c) / (p : ℚ) ^ e = (a - b) / (p : ℚ) ^ e + (b - c) / (p : ℚ) ^ e := by ring
  rw [this]; exact PI_add hp h1 h2

lemma Cg_of_eq {e : ℕ} {a b c : ℚ} (h1 : Cg p e a b) (h2 : b = c) : Cg p e a c := h2 ▸ h1

lemma Cg_mulL {e : ℕ} {a b c : ℚ} (hc : PI p c) (h : Cg p e a b) : Cg p e (c * a) (c * b) := by
  unfold Cg at *
  have : (c * a - c * b) / (p : ℚ) ^ e = c * ((a - b) / (p : ℚ) ^ e) := by ring
  rw [this]; exact PI_mul hp hc h

lemma Cg_mul {e : ℕ} {a b c d : ℚ} (ha : PI p a) (hd : PI p d) (h1 : Cg p e a b)
    (h2 : Cg p e c d) : Cg p e (a * c) (b * d) := by
  unfold Cg at *
  have : (a * c - b * d) / (p : ℚ) ^ e =
      a * ((c - d) / (p : ℚ) ^ e) + d * ((a - b) / (p : ℚ) ^ e) := by ring
  rw [this]; exact PI_add hp (PI_mul hp ha h2) (PI_mul hp hd h1)

lemma PI_of_Cg {e : ℕ} {a b : ℚ} (hb : PI p b) (h : Cg p e a b) : PI p a := by
  obtain ⟨u, hu, rfl⟩ := (Cg_iff hp e a b).mp h
  exact PI_add hp hb (PI_mul hp (PI_pow hp (by simpa using PI_int hp p) e) hu)

lemma Cg_pow {e : ℕ} {a b : ℚ} (ha : PI p a) (hb : PI p b) (h : Cg p e a b) (n : ℕ) :
    Cg p e (a ^ n) (b ^ n) := by
  induction n with
  | zero => simpa using Cg_refl hp e 1
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact Cg_mul hp (PI_pow hp ha n) hb ih h

lemma Cg_mono {e : ℕ} {a b : ℚ} (h : Cg p (e + 1) a b) : Cg p e a b := by
  unfold Cg at *
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have : (a - b) / (p : ℚ) ^ e = (p : ℚ) * ((a - b) / (p : ℚ) ^ (e + 1)) := by
    field_simp; ring
  rw [this]; exact PI_mul hp (by simpa using PI_int hp p) h

lemma Cg_le {e E : ℕ} (hle : e ≤ E) {a b : ℚ} (h : Cg p E a b) : Cg p e a b := by
  induction E with
  | zero => have : e = 0 := by omega
            subst this; exact h
  | succ E ih =>
    rcases Nat.lt_or_ge e (E + 1) with h' | h'
    · exact ih (by omega) (Cg_mono hp h)
    · have : e = E + 1 := by omega
      subst this; exact h

lemma Cg_div {e : ℕ} {a b : ℚ} (h : Cg p (e + 1) a b) : Cg p e (a / p) (b / p) := by
  unfold Cg at *
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have : (a / p - b / p) / (p : ℚ) ^ e = (a - b) / (p : ℚ) ^ (e + 1) := by
    field_simp; ring
  rw [this]; exact h

lemma Cg_sum {e : ℕ} (n : ℕ) (f g : ℕ → ℚ) (h : ∀ i < n, Cg p e (f i) (g i)) :
    Cg p e (∑ i ∈ Finset.range n, f i) (∑ i ∈ Finset.range n, g i) := by
  induction n with
  | zero => exact Cg_refl hp e _
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact Cg_add hp (ih (fun i hi => h i (by omega))) (h n (by omega))

lemma Cg_emod (E : ℕ) (x : ℤ) : Cg p E (x : ℚ) ((x % ((p ^ E : ℕ) : ℤ) : ℤ) : ℚ) := by
  refine (Cg_iff hp E _ _).mpr ⟨((x / ((p ^ E : ℕ) : ℤ) : ℤ) : ℚ), PI_int hp _, ?_⟩
  have := Int.mul_ediv_add_emod x ((p ^ E : ℕ) : ℤ)
  have h2 : (x : ℚ) = ((x % ((p ^ E : ℕ) : ℤ) : ℤ) : ℚ) +
      (((p ^ E : ℕ) : ℤ) : ℚ) * ((x / ((p ^ E : ℕ) : ℤ) : ℤ) : ℚ) := by
    have h3 : x = x % ((p ^ E : ℕ) : ℤ) + ((p ^ E : ℕ) : ℤ) * (x / ((p ^ E : ℕ) : ℤ)) := by
      linarith
    exact_mod_cast h3
  rw [h2]; push_cast; ring

/-- divisibility of the numerator of a `p`-integral rational -/
lemma dvd_num_iff {q : ℚ} (hq : PI p q) : (p : ℤ) ∣ q.num ↔ PI p (q / p) := by
  constructor
  · rintro ⟨k, hk⟩
    refine (PI_iff hp _).mpr ⟨k, q.den, hq, ?_⟩
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have h1 : q * q.den = q.num := Rat.mul_den_eq_num q
    rw [hk] at h1
    push_cast at h1
    field_simp
    linarith [h1]
  · intro h
    obtain ⟨a, d, hd, hx⟩ := (PI_iff hp _).mp h
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have h1 : q * d = p * a := by
      rw [← hx]; field_simp
    have h2 : (q.num : ℚ) * d = p * a * q.den := by
      rw [← Rat.mul_den_eq_num q]; linear_combination (q.den : ℚ) * h1
    have h3 : q.num * (d : ℤ) = p * a * q.den := by exact_mod_cast h2
    have h4 : (p : ℤ) ∣ q.num * d := ⟨a * q.den, by rw [h3]; ring⟩
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h4 with h5 | h5
    · exact h5
    · exact absurd (Int.natCast_dvd_natCast.mp h5) hd

lemma dvd_int_iff (x : ℤ) : (p : ℤ) ∣ x ↔ PI p ((x : ℚ) / p) := by
  have := dvd_num_iff hp (PI_int hp x)
  simpa using this

/-- the key test: congruence mod `p` decides divisibility of the numerator -/
lemma dvd_num_of_Cg {e : ℕ} (he : 1 ≤ e) {H : ℚ} {x : ℤ} (h : Cg p e H x) :
    (p : ℤ) ∣ H.num ↔ (p : ℤ) ∣ x := by
  have h1 : Cg p 1 H x := Cg_le hp he h
  obtain ⟨u, hu, hH⟩ := (Cg_iff hp 1 _ _).mp h1
  have hHI : PI p H := PI_of_Cg hp (PI_int hp x) h1
  rw [dvd_num_iff hp hHI, dvd_int_iff hp]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e1 : H / p = (x : ℚ) / p + u := by rw [hH]; field_simp
  rw [e1]
  constructor
  · intro h2
    have := PI_sub hp h2 hu
    simpa using this
  · intro h2; exact PI_add hp h2 hu

end

end OMA.EswH1

namespace OMA.EswH1

/-- binary modular exponentiation with fuel -/
def pw (M : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % M
  | f+1, b, k => if k = 0 then 1 % M else
      if k % 2 = 1 then pw M f (b * b % M) (k / 2) * b % M else pw M f (b * b % M) (k / 2)

/-- inverse of `a` modulo `p ^ E` (Euler) -/
def inv (p E a : ℕ) : ℕ := pw (p ^ E) (p * E) (a % p ^ E) (p ^ (E - 1) * (p - 1) - 1)

def sumTo (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumTo f n + f n

def ch (n k : ℕ) : ℕ := n.factorial / (k.factorial * (n - k).factorial)

def dotF (n : ℕ) : ℕ → List ℤ → ℤ
  | _, [] => 0
  | j, x :: L => (ch n j : ℤ) * x + dotF n (j + 1) L

/-- power sums `[P_0(m), ..., P_{t-1}(m)]`, `P_j(m) = ∑_{i<m} i^j` -/
def psl (m : ℤ) : ℕ → List ℤ
  | 0 => []
  | t + 1 => let L := psl m t
      L ++ [(m ^ (t + 1) - dotF (t + 1) 0 L) / (t + 1)]

/-- Hensel lifting of the inverse of `a` modulo `p ^ (2 ^ j)` -/
def hinv (p a : ℕ) : ℕ → ℤ
  | 0 => (inv p 1 a : ℤ)
  | j + 1 => (hinv p a j * (2 - (a : ℤ) * hinv p a j)) % ((p ^ (2 ^ (j + 1)) : ℕ) : ℤ)

/-- number of Hensel steps needed for precision `E ≤ 64` -/
def jE (E : ℕ) : ℕ :=
  if E ≤ 2 then 1 else if E ≤ 4 then 2 else if E ≤ 8 then 3 else if E ≤ 16 then 4 else
    if E ≤ 32 then 5 else 6

/-- inverse of `a` modulo `p ^ E` for `E ≤ 64` -/
def iv (p E a : ℕ) : ℤ := hinv p a (jE E) % ((p ^ E : ℕ) : ℤ)

/-- `w t s = inv(s+1)^(t+1)` reduced mod `p^E` -/
def w (p E : ℕ) : ℕ → ℕ → ℤ
  | 0, s => iv p E (s + 1)
  | t + 1, s => (w p E t s * iv p E (s + 1)) % ((p ^ E : ℕ) : ℤ)

def V (p E t r : ℕ) : ℤ := sumTo (fun s => w p E t s) r

def A (p E m : ℕ) : ℤ :=
  sumTo (fun t => (-(p : ℤ)) ^ t * V p E t (p - 1) * (psl (m : ℤ) E).getD t 0) E

def Qv (p E j : ℕ) : ℤ := sumTo (fun t => (-(p : ℤ)) ^ t * V p E t (p - 1) * (j : ℤ) ^ t) E

def dd (p E k : ℕ) : ℤ := sumTo (fun j => (-1 : ℤ) ^ (k - j) * (ch k j : ℤ) * Qv p E j) (k + 1)

def cb (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => cb m k * (m - k) / (k + 1)

/-- Newton form of `A` -/
def A2 (p E m : ℕ) : ℤ := sumTo (fun k => dd p E k * (cb m (k + 1) : ℤ)) E

/-- binomial coefficients `C(m, k)` reduced mod `p ^ E` (valid for `k < p`) -/
def cbM (p E m : ℕ) : ℕ → ℤ
  | 0 => 1
  | k + 1 => cbM p E m k * (((m - k : ℕ) : ℤ) % ((p ^ E : ℕ) : ℤ)) % ((p ^ E : ℕ) : ℤ) *
      iv p E (k + 1) % ((p ^ E : ℕ) : ℤ)

def A3 (p E m : ℕ) : ℤ :=
  if E < p then sumTo (fun k => (dd p E k % ((p ^ E : ℕ) : ℤ)) * cbM p E m (k + 1)) E else A2 p E m

def Rm (p E m r : ℕ) : ℤ := sumTo (fun t => (-(p : ℤ)) ^ t * (m : ℤ) ^ t * V p E t r) E

/-- reduced powers of `-(p m)` -/
def rp (p E m : ℕ) : ℕ → ℤ
  | 0 => 1
  | t + 1 => rp p E m t * ((-((p * m : ℕ) : ℤ)) % ((p ^ E : ℕ) : ℤ)) % ((p ^ E : ℕ) : ℤ)

def Rm2 (p E m r : ℕ) : ℤ := sumTo (fun t => rp p E m t * V p E t r) E

def key (p E r : ℕ) : ℕ := (V p E 0 r % (p : ℤ)).toNat

def ins (r : ℕ) : ℕ → List (List ℕ) → List (List ℕ)
  | _, [] => []
  | 0, l :: T => (r :: l) :: T
  | k + 1, l :: T => l :: ins r k T

/-- buckets of `r < p` by the residue of `V_0(r)` -/
def tab (p E : ℕ) : List (List ℕ) :=
  (List.range p).foldl (fun T r => ins r (key p E r) T) (List.replicate p [])

def tabOK (p E : ℕ) : Bool := (List.range p).all (fun r => ((tab p E).getD (key p E r) []).contains r)

def kids (p E : ℕ) (b : Bool) (x : ℕ × ℤ) : List (ℕ × ℤ) :=
  let c := (x.2 / (p : ℤ) + A3 p E x.1) % ((p ^ E : ℕ) : ℤ)
  (if b then (tab p E).getD ((-c) % (p : ℤ)).toNat [] else List.range p).filterMap (fun r =>
    if r < p ∧ p * x.1 + r ≠ 0 ∧ (c + V p E 0 r) % (p : ℤ) = 0 then
      some (p * x.1 + r, (c + Rm2 p E x.1 r) % ((p ^ E : ℕ) : ℤ))
    else none)

def step (p E : ℕ) (b : Bool) (L : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  L.flatMap (fun x => if x.2 % (p : ℤ) = 0 then kids p E b x else [])

def check (p E K : ℕ) (b : Bool) : Bool :=
  decide (K + 2 ≤ E ∧ E ≤ 64) && (!b || tabOK p E) && ((step p E b)^[K + 1] [(0, 0)]).isEmpty

end OMA.EswH1

namespace OMA.EswH1

lemma sumTo_eq (f : ℕ → ℤ) (n : ℕ) : sumTo f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

lemma pw_eq (M : ℕ) : ∀ f b k, k < 2 ^ f → pw M f b k = b ^ k % M := by
  intro f
  induction f with
  | zero =>
    intro b k hk
    have : k = 0 := by simpa using hk
    subst this; simp [pw]
  | succ f ih =>
    intro b k hk
    by_cases hk0 : k = 0
    · subst hk0; simp [pw]
    have hk2 : k / 2 < 2 ^ f := by rw [pow_succ] at hk; omega
    have e1 := ih (b * b % M) (k / 2) hk2
    simp only [pw, if_neg hk0]
    rw [e1, ← Nat.pow_mod]
    split_ifs with h
    · rw [Nat.mod_mul_mod]
      congr 1
      rw [← pow_two, ← pow_mul, ← pow_succ]
      congr 1; omega
    · congr 1
      rw [← pow_two, ← pow_mul]
      congr 1; omega

section
variable {p : ℕ} (hp : p.Prime)
include hp

lemma inv_spec {E : ℕ} (hE : 1 ≤ E) {a : ℕ} (ha : ¬ p ∣ a) :
    a * inv p E a % p ^ E = 1 := by
  have hM : 1 < p ^ E := Nat.one_lt_pow (by omega) hp.one_lt
  have hφ : Nat.totient (p ^ E) = p ^ (E - 1) * (p - 1) := Nat.totient_prime_pow hp (by omega)
  have hφpos : 0 < p ^ (E - 1) * (p - 1) :=
    Nat.mul_pos (pow_pos hp.pos _) (by have := hp.two_le; omega)
  have hlt : p ^ (E - 1) * (p - 1) - 1 < 2 ^ (p * E) := by
    have h1 : p ^ (E - 1) * (p - 1) ≤ p ^ E := by
      calc p ^ (E - 1) * (p - 1) ≤ p ^ (E - 1) * p := Nat.mul_le_mul_left _ (by omega)
        _ = p ^ E := by rw [← pow_succ]; congr 1; omega
    have h2 : p ^ E < 2 ^ (p * E) := by
      rw [pow_mul]
      exact Nat.pow_lt_pow_left (Nat.lt_two_pow_self) (by omega)
    omega
  have hcop : a.Coprime (p ^ E) :=
    Nat.Coprime.pow_right E ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr ha))
  have he := Nat.ModEq.pow_totient hcop
  rw [hφ] at he
  unfold inv
  rw [pw_eq _ _ _ _ hlt]
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod, ← pow_succ']
  have : p ^ (E - 1) * (p - 1) - 1 + 1 = p ^ (E - 1) * (p - 1) := by omega
  rw [this]
  rw [he]; exact Nat.mod_eq_of_lt hM

lemma inv_Cg {E : ℕ} (hE : 1 ≤ E) {a : ℕ} (ha : ¬ p ∣ a) :
    Cg p E ((a : ℚ)⁻¹) ((inv p E a : ℕ) : ℚ) := by
  have hs := inv_spec hp hE ha
  have ha0 : (a : ℚ) ≠ 0 := by
    have : a ≠ 0 := by rintro rfl; exact ha (dvd_zero p)
    exact_mod_cast this
  set v := inv p E a
  have hdm := Nat.div_add_mod (a * v) (p ^ E)
  rw [hs] at hdm
  refine (Cg_iff hp E _ _).mpr ⟨-(((a * v / p ^ E : ℕ) : ℚ)) * (a : ℚ)⁻¹,
    PI_mul hp (PI_neg hp (by have h := PI_int hp ((a * v / p ^ E : ℕ) : ℤ); rwa [Int.cast_natCast] at h)) (PI_inv hp ha), ?_⟩
  have h2 : (a : ℚ) * v = (p : ℚ) ^ E * ((a * v / p ^ E : ℕ) : ℚ) + 1 := by
    exact_mod_cast hdm.symm
  calc (a : ℚ)⁻¹ = ((a : ℚ) * v - (p : ℚ) ^ E * ((a * v / p ^ E : ℕ) : ℚ)) * (a : ℚ)⁻¹ := by
        rw [h2]; ring
    _ = _ := by field_simp; ring

end

/-- the `p`-free part of the harmonic sum -/
def T (p n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1), (if p ∣ j then (0 : ℚ) else ((j : ℕ) : ℚ)⁻¹)

lemma T_succ (p n : ℕ) : T p (n + 1) = T p n + (if p ∣ n + 1 then (0 : ℚ) else ((n + 1 : ℕ) : ℚ)⁻¹) := by
  unfold T; rw [Finset.sum_range_succ]

lemma T_block (p m : ℕ) (hp : 0 < p) : ∀ r, r < p →
    T p (p * m + r) = T p (p * m) + ∑ s ∈ Finset.range r, ((p * m + s + 1 : ℕ) : ℚ)⁻¹ := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ r ih =>
    intro hr
    rw [show p * m + (r + 1) = (p * m + r) + 1 by ring, T_succ, ih (by omega), Finset.sum_range_succ]
    have : ¬ p ∣ p * m + r + 1 := by
      intro h
      have h2 : p ∣ r + 1 := by
        exact (Nat.dvd_add_right (dvd_mul_right p m)).mp (by rwa [add_assoc] at h)
      have := Nat.le_of_dvd (by omega) h2
      omega
    rw [if_neg this]; ring

lemma T_mul (p : ℕ) (hp : 0 < p) : ∀ m,
    T p (p * m) = ∑ i ∈ Finset.range m, ∑ s ∈ Finset.range (p - 1), ((p * i + s + 1 : ℕ) : ℚ)⁻¹ := by
  intro m
  induction m with
  | zero => simp [T]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    have e : p * (m + 1) = (p * m + (p - 1)) + 1 := by
      rw [Nat.mul_succ]; omega
    rw [e, T_succ, T_block p m hp (p - 1) (by omega)]
    have : p ∣ p * m + (p - 1) + 1 := by
      rw [← e]; exact dvd_mul_right p _
    rw [if_pos this]; ring

/-- geometric expansion with remainder -/
lemma geom (x s : ℚ) (hs : s ≠ 0) (hxs : x + s ≠ 0) (E : ℕ) :
    (x + s)⁻¹ = ∑ t ∈ Finset.range E, (-x) ^ t * (s⁻¹) ^ (t + 1) + (-x) ^ E * ((s⁻¹) ^ E * (x + s)⁻¹) := by
  induction E with
  | zero => simp
  | succ E ih =>
    have key : s⁻¹ + (-x) * s⁻¹ * (x + s)⁻¹ = (x + s)⁻¹ := by field_simp; ring
    conv_lhs => rw [ih]
    rw [Finset.sum_range_succ, add_assoc]
    congr 1
    rw [pow_succ, pow_succ]
    linear_combination (-((-x) ^ E * s⁻¹ ^ E)) * key

end OMA.EswH1

namespace OMA.EswH1

lemma dotF_eq (n : ℕ) : ∀ (L : List ℤ) (j : ℕ),
    dotF n j L = ∑ i ∈ Finset.range L.length, (ch n (j + i) : ℤ) * L.getD i 0 := by
  intro L
  induction L with
  | nil => intro j; simp [dotF]
  | cons x L ih =>
    intro j
    rw [dotF, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show j + 1 + i = j + (i + 1) by ring]

lemma psl_len (m : ℤ) (t : ℕ) : (psl m t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [psl, ih]

lemma faul (t m : ℕ) : ∑ j ∈ Finset.range (t + 1),
    ((t + 1).choose j : ℤ) * ∑ i ∈ Finset.range m, (i : ℤ) ^ j = (m : ℤ) ^ (t + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Finset.sum_range_succ (fun i => (i : ℤ) ^ _), mul_add, Finset.sum_add_distrib, ih]
    have h := add_pow (m : ℤ) 1 (t + 1)
    simp only [one_pow, mul_one] at h
    rw [Finset.sum_range_succ] at h
    simp only [Nat.choose_self, Nat.cast_one, mul_one] at h
    push_cast
    rw [h]
    have : ∑ x ∈ Finset.range (t + 1), ((t + 1).choose x : ℤ) * (m : ℤ) ^ x =
        ∑ x ∈ Finset.range (t + 1), (m : ℤ) ^ x * ((t + 1).choose x : ℤ) :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [this]; ring

lemma psl_get (m : ℕ) : ∀ t, ∀ j < t, (psl (m : ℤ) t).getD j 0 = ∑ i ∈ Finset.range m, (i : ℤ) ^ j := by
  intro t
  induction t with
  | zero => intro j hj; omega
  | succ t ih =>
    intro j hj
    simp only [psl]
    rcases Nat.lt_or_ge j t with h | h
    · rw [List.getD_append _ _ _ _ (by rw [psl_len]; exact h)]
      exact ih j h
    · have hj' : j = t := by omega
      subst hj'
      rw [List.getD_append_right _ _ _ _ (by rw [psl_len])]
      simp only [psl_len, Nat.sub_self, List.getD_cons_zero]
      rw [dotF_eq, psl_len]
      have hf := faul j m
      rw [Finset.sum_range_succ] at hf
      have hc : ∀ i ∈ Finset.range j, (ch (j + 1) (0 + i) : ℤ) * (psl (m : ℤ) j).getD i 0 =
          ((j + 1).choose i : ℤ) * ∑ k ∈ Finset.range m, (k : ℤ) ^ i := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [ih i hi, zero_add, ch, ← Nat.choose_eq_factorial_div_factorial (by omega)]
      rw [Finset.sum_congr rfl hc]
      have hjc : ((j + 1).choose j : ℤ) = (j + 1 : ℤ) := by
        rw [Nat.choose_succ_self_right]; push_cast; ring
      rw [hjc] at hf
      have : (m : ℤ) ^ (j + 1) - ∑ i ∈ Finset.range j, ((j + 1).choose i : ℤ) *
          ∑ k ∈ Finset.range m, (k : ℤ) ^ i = (j + 1 : ℤ) * ∑ k ∈ Finset.range m, (k : ℤ) ^ j := by
        rw [← hf]; ring
      rw [show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring] at this
      push_cast
      rw [this]
      exact Int.mul_ediv_cancel_left _ (by omega)

lemma V_eq (p E t r : ℕ) : V p E t r = ∑ s ∈ Finset.range r, w p E t s := by
  unfold V; rw [sumTo_eq]

lemma Rm_sub (p E m r : ℕ) (hE : 1 ≤ E) : (p : ℤ) ∣ Rm p E m r - V p E 0 r := by
  unfold Rm
  rw [sumTo_eq]
  obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, add_sub_cancel_right]
  refine Finset.dvd_sum (fun t _ => ?_)
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow (dvd_neg.mpr (dvd_refl _)) (Nat.succ_ne_zero t)) _) _

lemma eqA (p E m : ℕ) : ((A p E m : ℤ) : ℚ) =
    ∑ i ∈ Finset.range m, ∑ s ∈ Finset.range (p - 1), ∑ t ∈ Finset.range E,
      (-(p : ℚ)) ^ t * (i : ℚ) ^ t * (w p E t s : ℚ) := by
  unfold A
  rw [sumTo_eq]
  push_cast
  symm
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [psl_get m E t (Finset.mem_range.mp ht), V_eq]
  push_cast
  symm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  ring

lemma eqR (p E m r : ℕ) : ((Rm p E m r : ℤ) : ℚ) =
    ∑ s ∈ Finset.range r, ∑ t ∈ Finset.range E, (-(p : ℚ)) ^ t * (m : ℚ) ^ t * (w p E t s : ℚ) := by
  unfold Rm
  rw [sumTo_eq]
  simp only [V_eq]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.mul_sum]

section
variable {p : ℕ} (hp : p.Prime)
include hp

lemma hinv_dvd {a : ℕ} (ha : ¬ p ∣ a) : ∀ j,
    ((p ^ (2 ^ j) : ℕ) : ℤ) ∣ (a : ℤ) * hinv p a j - 1 := by
  intro j
  induction j with
  | zero =>
    have h := inv_spec hp (le_refl 1) ha
    have h2 := Nat.div_add_mod (a * inv p 1 a) (p ^ 1)
    rw [h] at h2
    simp only [pow_zero, pow_one, hinv]
    refine ⟨((a * inv p 1 a / p : ℕ) : ℤ), ?_⟩
    have h3 : ((a * inv p 1 a : ℕ) : ℤ) = (p : ℤ) * ((a * inv p 1 a / p : ℕ) : ℤ) + 1 := by
      rw [pow_one] at h2; exact_mod_cast h2.symm
    push_cast at h3 ⊢
    linarith
  | succ j ih =>
    obtain ⟨k, hk⟩ := ih
    set q : ℤ := ((p ^ (2 ^ j) : ℕ) : ℤ)
    have hQ : ((p ^ (2 ^ (j + 1)) : ℕ) : ℤ) = q * q := by
      simp only [q]; push_cast; rw [← pow_add]; congr 1; rw [pow_succ]; ring
    simp only [hinv]
    rw [hQ]
    set x := hinv p a j
    set y := x * (2 - (a : ℤ) * x)
    have e1 : (a : ℤ) * y - 1 = -((a : ℤ) * x - 1) ^ 2 := by simp only [y]; ring
    have e2 : (a : ℤ) * (y % (q * q)) - 1 = ((a : ℤ) * y - 1) - (a : ℤ) * ((q * q) * (y / (q * q))) := by
      rw [Int.emod_def]; ring
    rw [e2, e1, hk]
    exact ⟨-(k ^ 2) - (a : ℤ) * (y / (q * q)), by ring⟩

lemma iv_dvd {E : ℕ} (hE64 : E ≤ 64) {a : ℕ} (ha : ¬ p ∣ a) :
    ((p ^ E : ℕ) : ℤ) ∣ (a : ℤ) * iv p E a - 1 := by
  have h1 := hinv_dvd hp ha (jE E)
  have hj : E ≤ 2 ^ (jE E) := by
    unfold jE; split_ifs <;> norm_num <;> omega
  have h2 : ((p ^ E : ℕ) : ℤ) ∣ ((p ^ (2 ^ (jE E)) : ℕ) : ℤ) := by
    exact_mod_cast Nat.pow_dvd_pow p hj
  have h3 := dvd_trans h2 h1
  unfold iv
  have e2 : (a : ℤ) * (hinv p a (jE E) % ((p ^ E : ℕ) : ℤ)) - 1 = ((a : ℤ) * hinv p a (jE E) - 1) -
      (a : ℤ) * (((p ^ E : ℕ) : ℤ) * (hinv p a (jE E) / ((p ^ E : ℕ) : ℤ))) := by
    rw [Int.emod_def]; ring
  rw [e2]
  exact dvd_sub h3 (Dvd.dvd.mul_left (dvd_mul_right _ _) _)

lemma iv_Cg {E : ℕ} (hE64 : E ≤ 64) {a : ℕ} (ha : ¬ p ∣ a) :
    Cg p E ((a : ℚ)⁻¹) (iv p E a : ℚ) := by
  obtain ⟨k, hk⟩ := iv_dvd hp hE64 ha
  have ha0 : (a : ℚ) ≠ 0 := by
    have : a ≠ 0 := by rintro rfl; exact ha (dvd_zero p)
    exact_mod_cast this
  refine (Cg_iff hp E _ _).mpr ⟨-(k : ℚ) * (a : ℚ)⁻¹,
    PI_mul hp (PI_neg hp (PI_int hp k)) (PI_inv hp ha), ?_⟩
  have h2 : (a : ℚ) * (iv p E a : ℚ) = (p : ℚ) ^ E * k + 1 := by
    have : ((a : ℤ) * iv p E a : ℤ) = ((p ^ E : ℕ) : ℤ) * k + 1 := by linarith
    exact_mod_cast this
  calc (a : ℚ)⁻¹ = ((a : ℚ) * (iv p E a : ℚ) - (p : ℚ) ^ E * k) * (a : ℚ)⁻¹ := by
        rw [h2]; ring
    _ = _ := by field_simp; ring

lemma w_Cg {E : ℕ} (hE64 : E ≤ 64) (s : ℕ) (hns : ¬ p ∣ s + 1) : ∀ t,
    Cg p E ((((s + 1 : ℕ) : ℚ)⁻¹) ^ (t + 1)) (w p E t s : ℚ) := by
  have hI : PI p (((s + 1 : ℕ) : ℚ)⁻¹) := PI_inv hp hns
  have hv := iv_Cg hp hE64 hns
  have hvI : PI p ((iv p E (s + 1) : ℤ) : ℚ) := PI_int hp _
  intro t
  induction t with
  | zero =>
    simp only [zero_add, pow_one, w]
    exact hv
  | succ t ih =>
    have h1 := Cg_mul hp (PI_pow hp hI (t + 1)) hvI ih hv
    have h2 := Cg_emod hp E (w p E t s * iv p E (s + 1))
    rw [pow_succ]
    simp only [w]
    refine Cg_trans hp h1 ?_
    push_cast at h2 ⊢
    exact h2

lemma term_Cg {E : ℕ} (hE64 : E ≤ 64) (i s : ℕ) (hs : s + 1 < p) :
    Cg p E (((p * i + s + 1 : ℕ) : ℚ)⁻¹)
      (∑ t ∈ Finset.range E, (-(p : ℚ)) ^ t * (i : ℚ) ^ t * (w p E t s : ℚ)) := by
  have hns : ¬ p ∣ s + 1 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hn : ¬ p ∣ p * i + s + 1 := by
    intro h; apply hns
    exact (Nat.dvd_add_right (dvd_mul_right p i)).mp (by rwa [add_assoc] at h)
  have hs0 : ((s + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hxs : (p : ℚ) * i + ((s + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hcast : ((p * i + s + 1 : ℕ) : ℚ) = (p : ℚ) * i + ((s + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [hcast, geom _ _ hs0 hxs E]
  have hI : PI p (((s + 1 : ℕ) : ℚ)⁻¹) := PI_inv hp hns
  have hJ : PI p (((p : ℚ) * i + ((s + 1 : ℕ) : ℚ))⁻¹) := by
    rw [← hcast]; exact PI_inv hp hn
  have hpI : PI p (p : ℚ) := by simpa using PI_int hp p
  have hiI : PI p (i : ℚ) := by simpa using PI_int hp i
  refine Cg_trans hp (b := ∑ t ∈ Finset.range E, (-((p : ℚ) * i)) ^ t *
      (((s + 1 : ℕ) : ℚ)⁻¹) ^ (t + 1)) ?_ ?_
  · refine (Cg_iff hp E _ _).mpr ⟨(-(i : ℚ)) ^ E * ((((s + 1 : ℕ) : ℚ)⁻¹) ^ E *
      ((p : ℚ) * i + ((s + 1 : ℕ) : ℚ))⁻¹), ?_, ?_⟩
    · exact PI_mul hp (PI_pow hp (PI_neg hp hiI) E) (PI_mul hp (PI_pow hp hI E) hJ)
    · rw [neg_mul_eq_mul_neg, mul_pow]; ring
  · refine Cg_sum hp E _ _ (fun t _ => ?_)
    rw [neg_mul_eq_neg_mul, mul_pow, mul_assoc, mul_assoc ((-(p : ℚ)) ^ t)]
    refine Cg_mulL hp (PI_pow hp (PI_neg hp hpI) t) ?_
    refine Cg_mulL hp (PI_pow hp hiI t) ?_
    exact w_Cg hp hE64 s hns t

lemma T_Cg {E : ℕ} (hE64 : E ≤ 64) (m r : ℕ) (hr : r < p) :
    Cg p E (T p (p * m + r)) ((A p E m + Rm p E m r : ℤ) : ℚ) := by
  rw [T_block p m hp.pos r hr, T_mul p hp.pos m]
  rw [Int.cast_add, eqA, eqR]
  refine Cg_add hp (Cg_sum hp m _ _ (fun i _ => Cg_sum hp (p - 1) _ _ (fun s hs => ?_)))
    (Cg_sum hp r _ _ (fun s hs => ?_))
  · exact term_Cg hp hE64 i s (by omega)
  · exact term_Cg hp hE64 m s (by omega)

end

end OMA.EswH1

namespace OMA.EswH1

lemma cb_eq (m : ℕ) : ∀ k, cb m k = m.choose k := by
  intro k
  induction k with
  | zero => simp [cb]
  | succ k ih =>
    rw [cb, ih, ← Nat.choose_succ_right_eq]
    exact Nat.mul_div_cancel _ (by omega)

lemma hockey (k : ℕ) : ∀ m, ∑ i ∈ Finset.range m, ((i.choose k : ℕ) : ℤ) = ((m.choose (k + 1) : ℕ) : ℤ) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ' m k]
    push_cast; ring

lemma iter_zero (j : ℕ) : (fwdDiff (1 : ℤ))^[j] (0 : ℤ → ℤ) = 0 := by
  apply Function.iterate_fixed
  funext y; simp [fwdDiff]

lemma A2_eq (p E m : ℕ) : A2 p E m = A p E m := by
  set a : ℕ → ℤ := fun t => (-(p : ℤ)) ^ t * V p E t (p - 1) with ha
  set Q : ℤ → ℤ := fun r => ∑ t ∈ Finset.range E, a t * r ^ t with hQ
  set D : ℕ → ℤ := fun k => (fwdDiff (1 : ℤ))^[k] Q 0 with hD
  have hDz : ∀ k, E ≤ k → D k = 0 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    simp only [hD]
    rw [add_comm, Function.iterate_add_apply, hQ, fwdDiff_iter_sum_mul_pow_eq_zero, iter_zero]
    rfl
  have hDd : ∀ k, D k = dd p E k := by
    intro k
    simp only [hD]
    rw [fwdDiff_iter_eq_sum_shift, dd, sumTo_eq]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    rw [smul_eq_mul, ch, ← Nat.choose_eq_factorial_div_factorial (by omega), Qv, sumTo_eq]
    simp only [zero_add, hQ, ha, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp only [nsmul_eq_mul, mul_one] <;> ring
  have hQi : ∀ i : ℕ, Q i = ∑ k ∈ Finset.range E, ((i.choose k : ℕ) : ℤ) * D k := by
    intro i
    have h := shift_eq_sum_fwdDiff_iter (1 : ℤ) Q i 0
    simp only [zero_add, nsmul_eq_mul, mul_one] at h
    rw [h]
    have h1 : ∑ k ∈ Finset.range (i + 1), ((i.choose k : ℕ) : ℤ) * D k =
        ∑ k ∈ Finset.range (i + 1 + E), ((i.choose k : ℕ) : ℤ) * D k := by
      apply Finset.sum_subset
      · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
      · intro x hx hx'
        simp only [Finset.mem_range] at hx hx'
        rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have h2 : ∑ k ∈ Finset.range E, ((i.choose k : ℕ) : ℤ) * D k =
        ∑ k ∈ Finset.range (i + 1 + E), ((i.choose k : ℕ) : ℤ) * D k := by
      apply Finset.sum_subset
      · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
      · intro x hx hx'
        simp only [Finset.mem_range] at hx hx'
        rw [hDz x (by omega)]; simp
    simp only [hD] at h1 h2 ⊢
    rw [h1, h2]
  -- A as a sum of Q
  have hA : A p E m = ∑ i ∈ Finset.range m, Q i := by
    unfold A
    rw [sumTo_eq]
    rw [Finset.sum_congr rfl (fun t ht => by rw [psl_get m E t (Finset.mem_range.mp ht)])]
    simp only [hQ, ha]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
  rw [hA]
  simp only [hQi]
  rw [Finset.sum_comm]
  unfold A2
  rw [sumTo_eq]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_mul, hockey, cb_eq, hDd]
  ring

end OMA.EswH1

namespace OMA.EswH1

lemma rp_mod (p E m : ℕ) : ∀ t, ((p ^ E : ℕ) : ℤ) ∣ rp p E m t - (-(p : ℤ)) ^ t * (m : ℤ) ^ t := by
  intro t
  induction t with
  | zero => simp [rp]
  | succ t ih =>
    simp only [rp]
    set M : ℤ := ((p ^ E : ℕ) : ℤ)
    set x : ℤ := -((p * m : ℕ) : ℤ) with hx
    have e : rp p E m t * (x % M) % M - (-(p : ℤ)) ^ (t + 1) * (m : ℤ) ^ (t + 1) =
        (rp p E m t - (-(p : ℤ)) ^ t * (m : ℤ) ^ t) * x + rp p E m t * (x % M - x) -
          M * (rp p E m t * (x % M) / M) := by
      rw [Int.emod_def (rp p E m t * (x % M))]; rw [hx]; push_cast; ring
    rw [e]
    have hxm : M ∣ x % M - x := by rw [Int.emod_def]; exact ⟨-(x / M), by ring⟩
    exact dvd_sub (dvd_add (Dvd.dvd.mul_right ih _) (Dvd.dvd.mul_left hxm _)) (dvd_mul_right _ _)

lemma Rm2_mod (p E m r : ℕ) : ((p ^ E : ℕ) : ℤ) ∣ Rm2 p E m r - Rm p E m r := by
  unfold Rm2 Rm
  rw [sumTo_eq, sumTo_eq, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum (fun t _ => ?_)
  have e : rp p E m t * V p E t r - (-(p : ℤ)) ^ t * (m : ℤ) ^ t * V p E t r =
      (rp p E m t - (-(p : ℤ)) ^ t * (m : ℤ) ^ t) * V p E t r := by ring
  rw [e]; exact Dvd.dvd.mul_right (rp_mod p E m t) _

lemma Rm2_sub (p E m r : ℕ) (hE : 1 ≤ E) : (p : ℤ) ∣ Rm2 p E m r - V p E 0 r := by
  have h1 := Rm2_mod p E m r
  have hpM : (p : ℤ) ∣ ((p ^ E : ℕ) : ℤ) := by push_cast; exact dvd_pow_self _ (by omega)
  have e : Rm2 p E m r - V p E 0 r = (Rm2 p E m r - Rm p E m r) + (Rm p E m r - V p E 0 r) := by ring
  rw [e]; exact dvd_add (dvd_trans hpM h1) (Rm_sub p E m r hE)

lemma Cg_of_Mdvd {p : ℕ} (hp : p.Prime) {E : ℕ} {x y : ℤ} (h : ((p ^ E : ℕ) : ℤ) ∣ x - y) :
    Cg p E (x : ℚ) (y : ℚ) := by
  obtain ⟨k, hk⟩ := h
  refine (Cg_iff hp E _ _).mpr ⟨k, PI_int hp k, ?_⟩
  have h2 : x = y + ((p ^ E : ℕ) : ℤ) * k := by linarith
  have h3 : (x : ℚ) = (y : ℚ) + (((p ^ E : ℕ) : ℤ) : ℚ) * (k : ℚ) := by exact_mod_cast h2
  rw [h3]; push_cast; ring

end OMA.EswH1

namespace OMA.EswH1

section
variable {p : ℕ} (hp : p.Prime)
include hp

lemma cbM_mod {E : ℕ} (hE64 : E ≤ 64) (hEp : E < p) (m : ℕ) : ∀ k, k ≤ E →
    Int.ModEq ((p ^ E : ℕ) : ℤ) (cbM p E m k) ((m.choose k : ℕ) : ℤ) := by
  intro k
  induction k with
  | zero => intro _; simp [cbM]
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    set M : ℤ := ((p ^ E : ℕ) : ℤ)
    have hnd : ¬ p ∣ k + 1 := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    have hu : Int.ModEq M (((k + 1 : ℕ) : ℤ) * iv p E (k + 1)) 1 := by
      have := iv_dvd hp hE64 hnd
      exact (Int.modEq_iff_dvd.mpr this).symm
    have hc : ((m.choose (k + 1) : ℕ) : ℤ) * ((k + 1 : ℕ) : ℤ) = ((m.choose k : ℕ) : ℤ) * ((m - k : ℕ) : ℤ) := by
      exact_mod_cast Nat.choose_succ_right_eq m k
    simp only [cbM]
    have s1 : Int.ModEq M (cbM p E m k * (((m - k : ℕ) : ℤ) % M) % M * iv p E (k + 1) % M)
        (cbM p E m k * ((m - k : ℕ) : ℤ) * iv p E (k + 1)) := by
      refine (Int.mod_modEq _ _).trans ?_
      refine Int.ModEq.mul_right _ ?_
      refine (Int.mod_modEq _ _).trans ?_
      exact Int.ModEq.mul_left _ (Int.mod_modEq _ _)
    refine s1.trans ?_
    have s2 : Int.ModEq M (cbM p E m k * ((m - k : ℕ) : ℤ) * iv p E (k + 1))
        (((m.choose k : ℕ) : ℤ) * ((m - k : ℕ) : ℤ) * iv p E (k + 1)) :=
      Int.ModEq.mul_right _ (Int.ModEq.mul_right _ ih')
    refine s2.trans ?_
    rw [← hc]
    have s3 := Int.ModEq.mul_left ((m.choose (k + 1) : ℕ) : ℤ) hu
    rw [mul_one, ← mul_assoc] at s3
    exact s3

lemma A3_mod {E : ℕ} (hE64 : E ≤ 64) (E' : ℕ) (m : ℕ) (hEE : E' = E) :
    ((p ^ E : ℕ) : ℤ) ∣ A3 p E m - A2 p E m := by
  subst hEE
  unfold A3
  split_ifs with hEp
  · unfold A2
    rw [sumTo_eq, sumTo_eq, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum (fun k hk => ?_)
    rw [Finset.mem_range] at hk
    have h1 := cbM_mod hp hE64 hEp m (k + 1) (by omega)
    have h2 : Int.ModEq ((p ^ E' : ℕ) : ℤ) (dd p E' k % ((p ^ E' : ℕ) : ℤ) * cbM p E' m (k + 1))
        (dd p E' k * ((m.choose (k + 1) : ℕ) : ℤ)) := Int.ModEq.mul (Int.mod_modEq _ _) h1
    rw [cb_eq]
    exact (Int.modEq_iff_dvd.mp h2.symm)
  · simp

end

end OMA.EswH1

namespace OMA.EswH1
open EswarathasanLevineConjecture

def Good (p e lo hi : ℕ) (L : List (ℕ × ℤ)) : Prop :=
  ∀ m ∈ harmonicNumDivisibleSet p, lo ≤ m → m < hi → ∃ h : ℤ, (m, h) ∈ L ∧ Cg p e (harmonic m) h

def HypS (p e lo hi : ℕ) (L : List (ℕ × ℤ)) : Prop :=
  ∀ m ∈ harmonicNumDivisibleSet p, lo ≤ m → m < hi →
    ∃ h : ℤ, (m / p, h) ∈ L ∧ Cg p (e + 1) (harmonic (m / p)) h ∧ (p : ℤ) ∣ h

section
variable {p : ℕ} (hp : p.Prime)
include hp

lemma hyp_root (e : ℕ) : HypS p e 0 p [(0, 0)] := by
  intro m _ _ hm
  refine ⟨0, ?_, ?_, dvd_zero _⟩
  · rw [Nat.div_eq_of_lt hm]; simp
  · rw [Nat.div_eq_of_lt hm]; simpa using Cg_refl hp (e + 1) 0

lemma hyp_of_good {e lo hi : ℕ} {L : List (ℕ × ℤ)} (hA : 1 ≤ lo) (hG : Good p (e + 1) lo hi L) :
    HypS p e (lo * p) (hi * p) L := by
  intro m hm h1 h2
  have hq1 : lo ≤ m / p := (Nat.le_div_iff_mul_le hp.pos).mpr h1
  have hq2 : m / p < hi := (Nat.div_lt_iff_lt_mul hp.pos).mpr h2
  have hpm : p ≤ m := by nlinarith
  have hqJ := OMA.R_EswarathasanLevineConjecture_eswarathasan_levine_harmonic_conjecture_R2.descent
    hp hpm hm.2
  obtain ⟨h, hmem, hc⟩ := hG (m / p) hqJ hq1 hq2
  exact ⟨h, hmem, hc, (dvd_num_of_Cg hp (by omega) hc).mp hqJ.2⟩

lemma good_step {e E lo hi : ℕ} {L : List (ℕ × ℤ)} (he : 1 ≤ e) (heE : e ≤ E) (hE64 : E ≤ 64)
    (b : Bool) (hH : HypS p e lo hi L) (htab : b = true → tabOK p E = true) :
    Good p e lo hi (step p E b L) := by
  intro m hm h1 h2
  obtain ⟨h, hmem, hc, hdvd⟩ := hH m hm h1 h2
  have hE : 1 ≤ E := le_trans he heE
  set q := m / p
  set r := m % p
  have hmqr : m = p * q + r := (Nat.div_add_mod m p).symm
  have hr : r < p := Nat.mod_lt _ hp.pos
  set nh : ℤ := (h / (p : ℤ) + A3 p E q + Rm2 p E q r) % ((p ^ E : ℕ) : ℤ)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  -- the congruence
  have hsplit := OMA.R_EswarathasanLevineConjecture_eswarathasan_levine_harmonic_conjecture_R2.harmonic_split
    p hp.pos m
  have hT : Cg p E (T p m) ((A3 p E q + Rm2 p E q r : ℤ) : ℚ) := by
    have := T_Cg hp hE64 q r hr
    rw [← A2_eq, ← hmqr] at this
    refine Cg_trans hp this (Cg_of_Mdvd hp ?_)
    obtain ⟨k, hk⟩ := Rm2_mod p E q r
    obtain ⟨k2, hk2⟩ := A3_mod hp hE64 E q rfl
    exact ⟨-k - k2, by rw [mul_sub, mul_neg]; linarith⟩
  have hdiv : Cg p e (harmonic q / p) ((h / (p : ℤ) : ℤ) : ℚ) := by
    rw [Int.cast_div hdvd (by exact_mod_cast hp.ne_zero)]
    simpa using Cg_div hp hc
  have hsum : Cg p e (harmonic m) (((h / (p : ℤ) + (A3 p E q + Rm2 p E q r)) : ℤ) : ℚ) := by
    rw [hsplit, Int.cast_add]
    exact Cg_add hp hdiv (Cg_le hp heE hT)
  have hnh : Cg p e (harmonic m) (nh : ℚ) := by
    refine Cg_trans hp hsum (Cg_le hp heE ?_)
    have := Cg_emod hp E (h / (p : ℤ) + A3 p E q + Rm2 p E q r)
    have e2 : h / (p : ℤ) + (A3 p E q + Rm2 p E q r) = h / (p : ℤ) + A3 p E q + Rm2 p E q r := by ring
    rw [e2]
    exact this
  refine ⟨nh, ?_, hnh⟩
  have hnd : (p : ℤ) ∣ nh := (dvd_num_of_Cg hp he hnh).mp hm.2
  unfold step
  rw [List.mem_flatMap]
  refine ⟨(q, h), hmem, ?_⟩
  rw [if_pos (Int.emod_eq_zero_of_dvd hdvd)]
  have hm0 : p * q + r ≠ 0 := by have := hm.1; omega
  set X : ℤ := h / (p : ℤ) + A3 p E q
  have hpM : (p : ℤ) ∣ ((p ^ E : ℕ) : ℤ) := by
    push_cast; exact dvd_pow_self _ (by omega)
  have hXR : (p : ℤ) ∣ X + Rm2 p E q r := by
    have e3 : X + Rm2 p E q r = nh + ((p ^ E : ℕ) : ℤ) * ((X + Rm2 p E q r) / ((p ^ E : ℕ) : ℤ)) := by
      have := Int.emod_def (X + Rm2 p E q r) ((p ^ E : ℕ) : ℤ)
      simp only [nh, X] at this ⊢
      linarith
    rw [e3]; exact dvd_add hnd (dvd_mul_of_dvd_left hpM _)
  have hcheap : (p : ℤ) ∣ X % ((p ^ E : ℕ) : ℤ) + V p E 0 r := by
    have e4 : X % ((p ^ E : ℕ) : ℤ) + V p E 0 r = (X + Rm2 p E q r) - (Rm2 p E q r - V p E 0 r) -
        ((p ^ E : ℕ) : ℤ) * (X / ((p ^ E : ℕ) : ℤ)) := by
      rw [Int.emod_def]; ring
    rw [e4]
    exact dvd_sub (dvd_sub hXR (Rm2_sub p E q r hE)) (dvd_mul_of_dvd_left hpM _)
  have hkey : key p E r = ((-(X % ((p ^ E : ℕ) : ℤ))) % (p : ℤ)).toNat := by
    unfold key
    congr 1
    have : Int.ModEq p (V p E 0 r) (-(X % ((p ^ E : ℕ) : ℤ))) := by
      rw [Int.modEq_iff_dvd]
      have e5 : -(X % ((p ^ E : ℕ) : ℤ)) - V p E 0 r = -(X % ((p ^ E : ℕ) : ℤ) + V p E 0 r) := by ring
      rw [e5]; exact dvd_neg.mpr hcheap
    exact this
  have hmemT : r ∈ (if b then (tab p E).getD ((-(X % ((p ^ E : ℕ) : ℤ))) % (p : ℤ)).toNat []
      else List.range p) := by
    cases b with
    | false => simpa using hr
    | true =>
      have := List.all_eq_true.mp (htab rfl) r (List.mem_range.mpr hr)
      rw [hkey] at this
      simpa using this
  unfold kids
  simp only [List.mem_filterMap]
  refine ⟨r, hmemT, ?_⟩
  rw [if_pos ⟨hr, hm0, Int.emod_eq_zero_of_dvd hcheap⟩]
  simp only [Option.some.injEq, Prod.mk.injEq]
  refine ⟨hmqr.symm, ?_⟩
  simp only [nh, X]
  rw [Int.emod_add_emod]

lemma chain {E : ℕ} (hE64 : E ≤ 64) (b : Bool) (htab : b = true → tabOK p E = true) : ∀ k, k + 2 ≤ E →
    Good p (E - 1 - k) (p ^ k) (p ^ (k + 1)) ((step p E b)^[k + 1] [(0, 0)]) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have hg := good_step hp (E := E) (by omega) (by omega) hE64 b (hyp_root hp (E - 1 - 0)) htab
    simp only [Function.iterate_one, pow_zero, zero_add, pow_one]
    intro m hm h1 h2
    exact hg m hm (by omega) h2
  | succ k ih =>
    intro hk
    have hg := ih (by omega)
    have e1 : E - 1 - k = (E - 1 - (k + 1)) + 1 := by omega
    rw [e1] at hg
    have hh := hyp_of_good hp (Nat.one_le_pow _ _ hp.pos) hg
    rw [← pow_succ, ← pow_succ] at hh
    have hs := good_step hp (E := E) (by omega) (by omega) hE64 b hh htab
    rw [Function.iterate_succ_apply']
    exact hs

theorem level_empty {E K : ℕ} {b : Bool} (hc : check p E K b = true) :
    ∀ n ∈ harmonicNumDivisibleSet p, ¬ (p ^ K ≤ n ∧ n < p ^ (K + 1)) := by
  unfold check at hc
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, List.isEmpty_iff] at hc
  obtain ⟨⟨⟨hK, hE64⟩, hb⟩, hL⟩ := hc
  have htab : b = true → tabOK p E = true := by
    intro h; subst h; simpa using hb
  intro n hn ⟨h1, h2⟩
  obtain ⟨h, hmem, _⟩ := chain hp hE64 b htab K hK n hn h1 h2
  rw [hL] at hmem
  simp at hmem

end

end OMA.EswH1

namespace OMA.EswH1

lemma iter_nil (p E : ℕ) (b : Bool) (n : ℕ) : (step p E b)^[n] [] = [] := by
  apply Function.iterate_fixed
  simp [step]

lemma iter_append (p E : ℕ) (b : Bool) : ∀ n (L1 L2 : List (ℕ × ℤ)),
    (step p E b)^[n] (L1 ++ L2) = (step p E b)^[n] L1 ++ (step p E b)^[n] L2 := by
  intro n
  induction n with
  | zero => intro L1 L2; rfl
  | succ n ih =>
    intro L1 L2
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply]
    rw [show step p E b (L1 ++ L2) = step p E b L1 ++ step p E b L2 by simp [step, List.flatMap_append]]
    exact ih _ _

lemma iter_empty (p E : ℕ) (b : Bool) (n : ℕ) : ∀ L : List (ℕ × ℤ),
    L.all (fun x => ((step p E b)^[n] [x]).isEmpty) = true → ((step p E b)^[n] L).isEmpty = true := by
  intro L
  induction L with
  | nil => intro _; rw [iter_nil]; rfl
  | cons x L ih =>
    intro h
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [show x :: L = [x] ++ L by rfl, iter_append, List.isEmpty_iff.mp h.1,
      List.isEmpty_iff.mp (ih h.2)]
    rfl

theorem check_of_split {p E K j : ℕ} {b : Bool} {L : List (ℕ × ℤ)}
    (hpre : (decide (K + 2 ≤ E ∧ E ≤ 64) && (!b || tabOK p E)) = true) (hj : j ≤ K)
    (hL : (step p E b)^[j + 1] [(0, 0)] = L)
    (hs : L.all (fun x => ((step p E b)^[K - j] [x]).isEmpty) = true) : check p E K b = true := by
  unfold check
  rw [hpre, Bool.true_and]
  rw [show K + 1 = (K - j) + (j + 1) by omega, Function.iterate_add_apply, hL]
  exact iter_empty p E b _ L hs

end OMA.EswH1

namespace OMA.EswH1

def tb0 : List (ℕ × ℕ × Bool) := [(7, 6, false), (11, 29, false), (13, 2, false), (17, 2, false), (19, 7, false), (23, 2, false), (29, 4, false), (31, 6, false), (37, 3, false), (41, 2, false), (43, 4, false), (47, 6, false)]
def tb1 : List (ℕ × ℕ × Bool) := [(53, 5, false), (59, 6, false), (61, 3, false), (67, 2, false), (71, 7, false), (73, 2, false), (79, 2, false), (89, 3, false), (97, 10, false), (101, 9, false), (103, 13, false), (107, 2, false)]
def tb2 : List (ℕ × ℕ × Bool) := [(113, 2, false), (131, 3, false), (137, 7, false), (139, 2, false), (149, 2, false), (151, 3, false), (157, 2, false), (163, 19, false), (179, 2, false), (181, 5, false), (191, 2, false), (193, 2, false)]
def tb3 : List (ℕ × ℕ × Bool) := [(197, 10, false), (199, 4, false), (211, 11, false), (223, 2, false), (227, 5, false), (229, 16, false)]
def tb4 : List (ℕ × ℕ × Bool) := [(239, 2, false), (241, 2, false), (251, 2, false), (257, 4, false), (263, 2, false), (271, 17, false), (277, 2, false), (281, 2, false), (293, 2, false), (307, 2, false), (311, 2, false), (317, 2, false)]
def tb5 : List (ℕ × ℕ × Bool) := [(331, 2, false), (337, 2, false), (347, 9, false), (349, 2, false), (353, 5, false), (367, 7, false), (373, 3, false)]
def tb6 : List (ℕ × ℕ × Bool) := [(383, 10, false), (389, 7, false), (401, 4, false), (409, 3, false), (421, 4, false)]
def tb7 : List (ℕ × ℕ × Bool) := [(431, 2, false), (443, 2, false), (449, 2, false), (461, 2, false), (463, 3, false), (467, 2, false), (479, 2, false), (487, 2, false), (491, 2, false), (499, 2, false), (503, 2, false), (509, 3, false)]
def tb8 : List (ℕ × ℕ × Bool) := [(523, 3, false), (541, 2, false), (547, 2, false)]
def tb9 : List (ℕ × ℕ × Bool) := [(109, 46, true)]
def tb10 : List (ℕ × ℕ × Bool) := [(167, 48, true)]
def tb11 : List (ℕ × ℕ × Bool) := [(173, 32, true)]
def tb12 : List (ℕ × ℕ × Bool) := [(233, 20, true)]
def tb13 : List (ℕ × ℕ × Bool) := [(269, 19, false)]
def tb14 : List (ℕ × ℕ × Bool) := [(283, 13, false)]
def tb15 : List (ℕ × ℕ × Bool) := [(313, 10, false)]
def tb16 : List (ℕ × ℕ × Bool) := [(359, 34, true)]
def tb17 : List (ℕ × ℕ × Bool) := [(379, 12, true)]
def tb18 : List (ℕ × ℕ × Bool) := [(419, 51, true)]
def tb19 : List (ℕ × ℕ × Bool) := [(433, 29, true)]
def tb20 : List (ℕ × ℕ × Bool) := [(439, 10, true)]
def tb21 : List (ℕ × ℕ × Bool) := [(457, 35, true)]
def tb22 : List (ℕ × ℕ × Bool) := [(521, 60, true)]

def tbl : List (ℕ × ℕ × Bool) := tb0 ++ tb1 ++ tb2 ++ tb3 ++ tb4 ++ tb5 ++ tb6 ++ tb7 ++ tb8 ++ tb9 ++ tb10 ++ tb11 ++ tb12 ++ tb13 ++ tb14 ++ tb15 ++ tb16 ++ tb17 ++ tb18 ++ tb19 ++ tb20 ++ tb21 ++ tb22

def L521a : List (ℕ × ℤ) := [(208396486652509011406287723867549649, 2640862764557885668719251037931135558676893414195641504116634560776336393949535904375777212845127839031244956899272784505628891032738485758023474493487092679222037032483), (208396486652509011406287723867549482, 159644570793789454046476228517504261478992936697383702421074942324550631598994436010152242979819328539029160099350285603274808103082463224102011693394282177092962878727), (208396486652509011406287723867549462, 1867335933081920726065509371070133483330112779297095207088150546214615607824863542849029160312881714431940016566135801117809504164752675616392862764271924957491010157691), (208396486652509011406287723867549295, 1891902449185236433803925568266637060637515284191279732788003926689013218059666780358963903754941480783794255541948876411630447213486053625627193206817512547999180212607), (208396486652509011406287723832274342, 2716448999012542890300625881914141937210478276621562356477795782758485616076225608629364622802358463926824975230956519303857566577555157529279921776731137962552460990302), (208396486652509011406287723832274193, 677574255382575545031460642255231253991435515876866676557329396497554625080506781381671954344808663060585894587895528963765526881969962914423715691359966193233237097021), (208396486652509011406287723832274057, 1966664060920310053541006118866260673358063777756581794359063972856264102959776737410133734656314988077936003868091701884149462134594568197246218424615996445683521685835), (208396486652509011406287723832273908, 1517076603023595749076583897885898111456430422484429460482449732493966937194448827337592352434376406993919981661081517779752220114189063251468258950692892372573067289930), (208396486652509011406287680015122957, 2087043738013514755147747260795924470992165819466618760300243843166358896380260750053409377893924901834125970238472938965095987719534510912010275080992750555601956830511), (208396486652509011406287680015122820, 2079871604959890008324755199589460506789563859950115570223466352453945487676068893499059090906423258181149868164007097724593024280882911431256381009503821681916204501914), (208396486652509011406287680015122674, 2595079838617098481980542529730805970069816672973563963890594687356289785438201821161730951607214008239389951725954973547008218842047264555325647773483550106845075263151), (208396486652509011406287680015122537, 348073930822244392200143616169192801857445147891410844725798718074713869899147421037043506942421382723934682414210463344026091186132781931399152991326580547050051744094), (208396486652509011406287680014871879, 2302598658045508526411951618939114906688145750178332040752056985612992776596402778584141082574709974755086948367903539995133819444170887107148434139156160137471114683683), (208396486652509011406287680014871371, 800008411087444213854435522865983048224397471357497107294611788954887459966036216329272321826352765674722221515106311740554850022337785579824924776467387365074911607463), (208396485895006643221559360313353901, 955658226328386531824668914407052944355803501380238707285141908554767222427659124401971904033042545698535162175166155684477506058899041130148506252060420302909459747314), (208396485895006643221559360313353777, 1277544473661637090811930363043141236890190539674128353016657971882812293742880429543112836842128893882391495509569872642393683052367491803677823006508578476475375349569), (208396485895006643221559360313300952, 2641597232979550616897067302740661285231432850969527833833983619490780996917635138685138858703455980983816426536043806347782982573945827171885093277400184784916055166868), (208396485895006643221559360313300442, 733124995837489637794924479973128290881527007714614444371329555223901478532959407094391345405231398042702159355231686128401648566840736600456174505006952193078624703862), (208396485895006643221559318723309358, 1277311843333934657089973542237122343519461077187082042351961992649238070401691608404761559559482816086620489191341981544501959174354969606325253095323242787718859084736), (208396485895006643221559318723308998, 682875035769930271146803497181780547408451757426532642729723582713134052111731368580840853601442035995395014620190446077221301507026370163531844963954405439192163139084), (208396485895006639476884318896138603, 2132393603453188444557917876601762794300688982736355727546910849953950495688577894126462633547201549127525560698989515475058020970899068443379186341864549388748623219828), (208396485895006639476884318896138439, 2089851109035375249565972368269445604704070792085416416343487340757369738072127034464829510379585289244242665532372593113924135546182792393821555151150033607525274099660), (208396485895006639476884318896051739, 197917929657777544892088652833341357096160393135316992690637669873481778107355789995549823611765104623334994591966055744036418388497708867985418208369298657728307007652), (208396485895006639476884318896051690, 1387455790641489876717389243616039235648798229062155812723598804912795738583338871711652200150879563809203275290223481291061174788111338526808896424824293774462966211977), (208396485895006639476884318896051338, 297909092434285448823553173374026942231333163324581748266063594402384701993802712445603562765923848006461228944781843316019856544516187959453206485879363024698229567850), (208396485895006639476884318896051289, 278440854433388762592134736981230248370406309225561836138298119654469186590107068939516743145457732778196885748914570302969136810739969641599717288604112553731284489431), (208396485895006639476884318895990074, 119684192855623314040241077866251927426257309142761483883601719092790298726025763601505711856886787079829978031849609437246011214584740213612466841492650645372450924175), (208396485895006639476884318895989998, 1663995013060818869482175467780568858376258864231651097061093519787017100508315644188197917648588376011070499919842773066977059136133248838449740891190161640572237471207), (208396485895006639476884318895950024, 1204339386759535264173263940605388762040573137757575767393273540079229889203503128029716639366121076825952911116187793888143401319138030315508621258753408229983339307018), (208396485895006639476884318895949814, 1389380010941806515279751552289484983571197255766253082319218774669839310055617388106106456337189139375816758200420341060609312442639818168134734922627618695007495447456), (208395729111533391910740427612770102, 2140568693057520791280498053496614455607116298625718710706065760913413187828464522680147974627892381089959144776638055051737769303537439161738033798316558638086056477192), (208395729111533391910740427612769892, 341373246574273936842266529775058088636521616457513993323341829658340110591650577428481168162319805244424753083362421869242780443608177990966898061718439718075882690223), (208395729111533391910740427612731693, 1234995068641680590264867320626001070269095615387517584451893040954604363019659382287936541800106378533439656811135626888966191987925125546803628366693877876947052878201), (208395729111533391910740427612731193, 1706550451099650572322553472312407040381987201731273726743871173680712417033660214198312753837162427753276981914924989586435573077224872765731919928470835126644382407551), (208395729111533391910740427612613890, 2367642302391051753593034430499675950034849078643875835532469665261659721305651743252155874548068334468031862861009208892124503739392748009975799194021907058798014969779), (208395729111533391910740427612613504, 2376875611412859181704173331735823364241057373639080660961466914686284529569493570601068814727926565694555690234516455877440303301813933164029295375558377326488806669940), (208395729111533391910740427612575235, 1627324968812624930055556100655557169395751833163424749316811578856591564148946662984416590404817762440836232740919008649400800035715165305058690946491253680512156180576), (208395729111533391910740427612575051, 1904148485842826838360030545990750102118844245344295875045159505592594449818705715813950107376070966352227779583879673707837869772101315379904690300156292652964882611550), (208395729111533391907940403790766835, 1925959050641350660618750889608000493707444676688315330043983377068591226086711516709960469760548042891094123374919516074642436149212132248741831865170317010379648116035), (208395729111533391907940403790766637, 1643352250389941791182345209977990405096118860895860685335478962982811630056381660039550054675262483880222004775467444082750399135891506979728991526237737181819991697196)]

def L521b : List (ℕ × ℤ) := [(208395729111533391907940403790749054, 2304961464314648929144878231065740683183861348265002500044178787837063470064573577150758679056841558004997495320930505670610059161399656765798663834163062766962550529787), (208395729111533391907940403790748990, 122554206684942032911325948064016553260544197239730717740900671183918425641626795892773187390454860316231522120440503708063424250031430724661717831010032815640540179101), (208395729111533390675908420466753946, 2415981312905521348335577910576848182405547019681903250351572170457725553253219291116427397528490244343140133438364885512251372927705037558441387960070763721736536007634), (208395729111533390675908420466753904, 546464303620576144518829593171844901198879282139415432065086781911280869363378256590809526828386004551046449514786350948803446248517020712248416532308483201729170201804), (208395729111533390675908420466753474, 2074992447184019654363537852200775131589191984942046982397729292604365466097641086962062703175890439346127086301395848535451398638759091312293936856529305392952298014032), (208395729111533390675908420466753432, 1330766216293176577887971416207330481885280467197308429816297804179076898647226587461691870597896297118301625817031912493878520796761317695959261900498383196904371453550)]

def L521c : List (ℕ × ℤ) := [(208395729111533390675908420466572962, 1954611703843552656892606725836203330767594399952511239153751206781726415688918986600316335662001618212574705157617059460295064610762421635258882830970853666929295641388)]

def L521d : List (ℕ × ℤ) := [(208395729111533390675908420466572842, 571845136544189195424154198282957273737351948684308884625271957728247771583535171551757296522769135218254466192112331467429027713624457489982246258731964171108731801300), (208395729111533390675908420466533922, 322910662022470767421440906965428587820758070865025494390934052776101165840337075752819575777317937306536549561290846165721448134437188304650638473144758087682095158471), (208395729111533390675908420466533871, 2034238555559643012956255654295400425189163271145976908820981816738452235168545130290912652367203941915053791796171560837543467267916945265551948880098617507998379429629), (208395729111533390675908420466533783, 739761190760454928351519183622067046110289475721624975749043276164322458767952491923927511196256652702389981222102086718917559627098214649411829058601145693856459464158), (208395729111533390675908420466533732, 970426141837686726712809739907388588480401887431673551924291432264354992713298007490305955472272747235357773882678687652961631208983475762811246503365665074555112603008), (208395729111533390675908420343535775, 696628761776069353294809901095582798968555304261657018714453230271983627515756672984787729134937059738282764147984415180952433545439753631089728813085547458551554317335), (208395729111533390675908420343535750, 1928879823455793061323238057049905344523932528530447415575578600462255355396010928866247663668412348435319612911575287010197355846588919418443010077552875728684473755067), (208395729111533390675908420343535502, 1525774320723754259229843053984471011621800735093613972658055742197111054809576079865994183617949543665208872088266005746011155206680898252371617859782224461386501415829), (208395729111533390675908420343535477, 532207985423616021004671979243956215363883343350857866172351609379079579032512059714646617309683165867247225557020815582530689334266811784787464301592278776221308689898), (208395729111533390675908362070674714, 2747019925087443789149888440507591482594892612181380064738176765289864509303756766242257787990727594626744720973122223191775061560201559130858236786697014499254672235389), (208395729111533390675908362070674254, 2604951881916509373703609084800059666532067740215131314152309476071725123507759009413772777405793927785721881421592112068375886821382496747462806369388795969335290332333)]

set_option maxHeartbeats 0 in
theorem s521_pre : (decide (60 + 2 ≤ 62 ∧ 62 ≤ 64) && (!true || tabOK 521 62)) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem s521_L : (step 521 62 true)^[12 + 1] [(0, 0)] = L521a ++ L521b ++ L521c ++ L521d := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem s_L521a : L521a.all (fun x => ((step 521 62 true)^[60 - 12] [x]).isEmpty) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem s_L521b : L521b.all (fun x => ((step 521 62 true)^[60 - 12] [x]).isEmpty) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem s_L521c : L521c.all (fun x => ((step 521 62 true)^[60 - 12] [x]).isEmpty) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem s_L521d : L521d.all (fun x => ((step 521 62 true)^[60 - 12] [x]).isEmpty) = true := by
  set_option maxRecDepth 200000 in decide +kernel

theorem c521 : check 521 62 60 true = true :=
  check_of_split s521_pre (by norm_num) s521_L (by
    rw [List.all_append, List.all_append, List.all_append, s_L521a, s_L521b, s_L521c, s_L521d]; rfl)

set_option maxHeartbeats 0 in
theorem ok0 : (tb0).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok1 : (tb1).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok2 : (tb2).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok3 : (tb3).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok4 : (tb4).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok5 : (tb5).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok6 : (tb6).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok7 : (tb7).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok8 : (tb8).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok9 : (tb9).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok10 : (tb10).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok11 : (tb11).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok12 : (tb12).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok13 : (tb13).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok14 : (tb14).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok15 : (tb15).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok16 : (tb16).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok17 : (tb17).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok18 : (tb18).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok19 : (tb19).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok20 : (tb20).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

set_option maxHeartbeats 0 in
theorem ok21 : (tb21).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  set_option maxRecDepth 200000 in decide +kernel

theorem ok22 : (tb22).all (fun x => check x.1 (x.2.1 + 2) x.2.1 x.2.2) = true := by
  refine List.all_eq_true.mpr (fun x hx => ?_)
  have hx' : x ∈ [(521, 60, true)] := hx
  rw [List.mem_singleton.mp hx']
  exact c521

theorem ok_all : ∀ x ∈ tbl, check x.1 (x.2.1 + 2) x.2.1 x.2.2 = true := by
  intro x hx0
  have hx : x ∈ tb0 ++ tb1 ++ tb2 ++ tb3 ++ tb4 ++ tb5 ++ tb6 ++ tb7 ++ tb8 ++ tb9 ++ tb10 ++ tb11 ++ tb12 ++ tb13 ++ tb14 ++ tb15 ++ tb16 ++ tb17 ++ tb18 ++ tb19 ++ tb20 ++ tb21 ++ tb22 := hx0
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok22 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok21 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok20 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok19 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok18 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok17 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok16 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok15 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok14 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok13 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok12 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok11 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok10 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok9 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok8 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok7 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok6 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok5 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok4 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok3 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok2 x h
  rcases List.mem_append.mp hx with hx | h
  swap
  · exact List.all_eq_true.mp ok1 x h
  exact List.all_eq_true.mp ok0 x hx

def isPr (p : ℕ) : Bool := (List.range p).all (fun d => d < 2 || p % d != 0)

lemma isPr_of_prime {p : ℕ} (hp : p.Prime) : isPr p = true := by
  unfold isPr
  rw [List.all_eq_true]
  intro d hd
  rw [List.mem_range] at hd
  simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  by_cases h2 : d < 2
  · exact Or.inl h2
  · right
    intro hmod
    have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hmod
    rcases hp.eq_one_or_self_of_dvd d hdvd with h | h <;> omega

theorem cover : (List.range 548).all (fun p => if 7 ≤ p ∧ p ≠ 83 ∧ p ≠ 127 ∧ p ≠ 397 ∧
    isPr p = true then tbl.any (fun x => x.1 == p) else true) = true := by
  set_option maxRecDepth 200000 in decide +kernel

end OMA.EswH1

theorem OMA.solution : OMA.R_EswarathasanLevineConjecture_eswarathasan_levine_harmonic_conjecture_R2.H1 := by
  intro p hp h7 h547 h83 h127 h397
  have h := List.all_eq_true.mp OMA.EswH1.cover p (List.mem_range.mpr (by omega))
  rw [if_pos ⟨h7, h83, h127, h397, OMA.EswH1.isPr_of_prime hp⟩, List.any_eq_true] at h
  simp only [beq_iff_eq] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x.2.1, OMA.EswH1.level_empty hp (OMA.EswH1.ok_all x hx)⟩

