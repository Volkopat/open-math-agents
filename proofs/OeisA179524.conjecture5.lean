import FormalConjectures.OEIS.«179524»
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Sun's weighted congruence for A179524

Binomial reflection reduces the unweighted inner sum to a convolution. The remaining
one-dimensional sum is evaluated by the shifted Wilf–Zeilberger pair from Theorem 3 of
Wadim Zudilin, *Ramanujan-type supercongruences*, arXiv:0805.2788.
-/

open Finset

namespace OMA.A179524

private def L (a b : ℤ) (n : ℕ) : ℤ :=
  ∏ i ∈ range n, (a + b * i)

private theorem L_succ (a b : ℤ) (n : ℕ) :
    L a b (n+1) = L a b n * (a + b * n) := by
  simp [L, Finset.prod_range_succ]

private theorem L_left (a b : ℤ) (n : ℕ) :
    L a b (n+1) = a * L (a+b) b n := by
  unfold L
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_succ, Nat.cast_zero, mul_zero, add_zero]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

private theorem L_add (a b : ℤ) (n m : ℕ) :
    L a b (n+m) = L a b n * L (a + b*n) b m := by
  induction m with
  | zero => simp [L]
  | succ m ih =>
    rw [show n + (m + 1) = n + m + 1 by omega, L_succ, ih, L_succ, Nat.cast_add]
    ring

private def fac (n : ℕ) : ℤ := n.factorial

private theorem fac_succ (n : ℕ) : fac (n+1) = (n+1) * fac n := by
  simp [fac, Nat.factorial_succ]

private theorem fac_mul_L (n m : ℕ) :
    fac n * L (n+1) 1 m = fac (n+m) := by
  induction m with
  | zero => simp [L]
  | succ m ih =>
    rw [L_succ, ← mul_assoc, ih, show n + (m+1) = n+m+1 by omega, fac_succ]
    push_cast
    ring

private def tail (a b : ℕ) : ℤ := L (a+1) 1 (b-a)

private theorem tail_fac {a b : ℕ} (h : a ≤ b) :
    fac a * tail a b = fac b := by
  rw [tail, fac_mul_L, Nat.add_sub_of_le h]

private theorem tail_step {a b : ℕ} (h : a < b) :
    tail a b = (a+1) * tail (a+1) b := by
  unfold tail
  rw [show b-a = b-(a+1)+1 by omega, L_left, Nat.cast_add, Nat.cast_one]

private theorem tail_add {a b d : ℕ} (h : a+d ≤ b) :
    tail a b = L (a+1) 1 d * tail (a+d) b := by
  unfold tail
  rw [show b-a = d+(b-(a+d)) by omega, L_add, Nat.cast_add, one_mul]
  congr 2
  ring

-- Clear the variable factorial denominators using tails of the common factorials.
private def base (m j : ℕ) : ℤ :=
  (-4)^j * fac (2*j)^4 * tail (4*j+1) (4*m+1) * tail j m ^ 4

private theorem base_step {m j : ℕ} (h : j < m) :
    8*(2*(j:ℤ)+1)^3 * base m j =
      -(j+1)*(4*(j:ℤ)+3)*(4*j+5)*base m (j+1) := by
  have ht := tail_add (a := 4*j+1) (b := 4*m+1) (d := 4) (by omega)
  have hf : fac (2*(j+1)) = (2*(j:ℤ)+2)*(2*j+1)*fac (2*j) := by
    rw [show 2*(j+1) = 2*j+1+1 by omega, fac_succ, fac_succ]
    push_cast
    ring
  simp only [base, hf, ht, tail_step h, pow_succ (-4 : ℤ) j,
    show 4*j+1+4 = 4*(j+1)+1 by omega]
  rw [show ∀ a : ℤ, L a 1 4 = a*(a+1)*(a+2)*(a+3) by
    intro a
    change L a 1 (0+1+1+1+1) = _
    norm_num [L_succ, show L a 1 0 = 1 by simp [L]]]
  push_cast
  ring

private def P (j k : ℕ) : ℤ := L (4*(j:ℤ)+1) (-2) k
private def Q (j k : ℕ) : ℤ := L (2*(j:ℤ)+1) 2 k
private def O (m k : ℕ) : ℤ := L (2*(k:ℤ)+1) 2 (m-k)

private theorem O_step {m k : ℕ} (h : k < m) :
    O m k = (2*(k:ℤ)+1)*O m (k+1) := by
  unfold O
  rw [show m-k = m-(k+1)+1 by omega,L_left]
  push_cast
  congr 2

private def U (m j k : ℕ) : ℤ :=
  base m j * (-1)^k * P j k * Q j k * O m k ^ 2

-- Zudilin's pair, with his n replaced by −j−1/2 and its denominators cleared.
private def F (m j k : ℕ) : ℤ := (20*(j:ℤ)+2*k+7) * U m j k

private def G (m j k : ℕ) : ℤ :=
  16*(2*(j:ℤ)+1)^2*(2*j+2*k+1) *
    (base m j * (-1)^k * P j k * Q j k * O m (k+1)^2)

private theorem P_shift (j k : ℕ) :
    (4*(j:ℤ)+5)*(4*j+3)*P j k =
      (4*(j:ℤ)+5-2*k)*(4*j+3-2*k)*P (j+1) k := by
  unfold P
  have h1 := L_add (4*((j:ℕ)+1:ℤ)+1) (-2) 2 k
  have h2 := L_add (4*((j:ℕ)+1:ℤ)+1) (-2) k 2
  rw [Nat.add_comm 2 k] at h1
  rw [h2] at h1
  have hx : 4*((j:ℕ)+1:ℤ)+1+(-4) = 4*(j:ℤ)+1 := by ring
  push_cast at h1
  rw [hx] at h1
  simp only [show ∀ a : ℤ, L a (-2) 2 = a*(a-2) by
    intro a; change L a (-2) (0+1+1) = _;
    rw [L_left, L_left]; simp only [show ∀ b c : ℤ, L b c 0 = 1 by simp [L]]; ring] at h1
  push_cast
  linear_combination -h1

private theorem Q_shift (j k : ℕ) :
    (2*(j:ℤ)+2*k+1)*Q j k = (2*j+1)*Q (j+1) k := by
  unfold Q
  rw [show 2*(j:ℤ)+2*k+1 = (2*j+1)+2*k by ring, mul_comm, ← L_succ, L_left]
  push_cast
  congr 2

private theorem G_prev {m j k : ℕ} (h : j < m) :
    G m j k =
      -2*((j:ℤ)+1)*(4*((j:ℤ)+1)+1-2*k)*(4*((j:ℤ)+1)-1-2*k) *
        (base m (j+1) * (-1)^k * P (j+1) k * Q (j+1) k * O m (k+1)^2) := by
  apply mul_left_cancel₀ (show (2*(j:ℤ)+1) ≠ 0 by positivity)
  unfold G
  calc
    _ = 2*(8*(2*(j:ℤ)+1)^3*base m j) * (-1)^k * P j k *
          ((2*(j:ℤ)+2*k+1)*Q j k) * O m (k+1)^2 := by ring
    _ = -2*((j:ℤ)+1) * base m (j+1) * (-1)^k *
          ((4*(j:ℤ)+5)*(4*j+3)*P j k) * ((2*(j:ℤ)+1)*Q (j+1) k) *
          O m (k+1)^2 := by rw [base_step h, Q_shift]; ring
    _ = _ := by rw [P_shift]; ring

private theorem WZ_zero {m k : ℕ} (hk : k < m) :
    F m 0 (k+1) - F m 0 k = -G m 0 k := by
  simp only [F, U, G, P, Q, L_succ, O_step hk, pow_succ (-1 : ℤ) k]
  push_cast
  ring

private theorem WZ_succ {m j k : ℕ} (hj : j < m) (hk : k < m) :
    F m (j+1) (k+1) - F m (j+1) k = G m j k - G m (j+1) k := by
  rw [G_prev hj]
  simp only [F, U, G, P, Q, L_succ, O_step hk, pow_succ (-1 : ℤ) k]
  push_cast
  ring

private theorem sum_G (m k : ℕ) (hk : k < m) :
    (∑ j ∈ range (m+1), F m j (k+1)) -
        (∑ j ∈ range (m+1), F m j k) = -G m m k := by
  rw [← sum_sub_distrib]
  suffices h : ∀ n ≤ m,
      (∑ j ∈ range (n+1), (F m j (k+1) - F m j k)) = -G m n k by
    exact h m le_rfl
  intro n hn
  induction n with
  | zero => simpa using WZ_zero hk
  | succ n ih =>
    rw [sum_range_succ, ih (by omega), WZ_succ (by omega : n < m) hk]
    ring


private theorem L_reflect (a b : ℤ) (n : ℕ) :
    L a b n = L (a+b*((n:ℤ)-1)) (-b) n := by
  unfold L
  rw [← Finset.prod_range_reflect (fun i : ℕ => a+b*(i:ℤ)) n]
  apply prod_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [Nat.cast_sub (by omega : i ≤ n-1),
    Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  ring

private theorem L_neg (a b : ℤ) (n : ℕ) :
    L (-a) (-b) n = (-1)^n * L a b n := by
  induction n with
  | zero => simp [L]
  | succ n ih => rw [L_succ, L_succ, ih, pow_succ]; ring

private theorem L_fac (n : ℕ) : L 1 1 n = fac n := by
  simpa [fac] using fac_mul_L 0 n

private theorem L_dvd (a b : ℤ) {n i : ℕ} (h : i < n) : a+b*i ∣ L a b n :=
  dvd_prod_of_mem (fun i : ℕ => a+b*i) (mem_range.mpr h)

private theorem prod_mod {s : Finset ℕ} {a b : ℕ → ℤ} {d : ℤ}
    (h : ∀ i ∈ s, a i ≡ b i [ZMOD d]) :
    (∏ i ∈ s, a i) ≡ (∏ i ∈ s, b i) [ZMOD d] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi]
    exact (h i (mem_insert_self _ _)).mul (ih fun j hj => h j (mem_insert_of_mem hj))

private theorem sum_mod {s : Finset ℕ} {a b : ℕ → ℤ} {d : ℤ}
    (h : ∀ i ∈ s, a i ≡ b i [ZMOD d]) :
    (∑ i ∈ s, a i) ≡ (∑ i ∈ s, b i) [ZMOD d] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (h i (mem_insert_self _ _)).add (ih fun j hj => h j (mem_insert_of_mem hj))

private theorem L_mod {a b a' b' d : ℤ} (ha : a ≡ a' [ZMOD d])
    (hb : b ≡ b' [ZMOD d]) (n : ℕ) : L a b n ≡ L a' b' n [ZMOD d] :=
  prod_mod fun i _ => ha.add (hb.mul_right i)

private theorem cast_modSq {p : ℕ} {a b : ℤ} :
    (a : ZMod (p^2)) = (b : ZMod (p^2)) ↔ a ≡ b [ZMOD (p:ℤ)^2] := by
  rw [ZMod.intCast_eq_intCast_iff, Nat.cast_pow]

private theorem mod_mul_p {p : ℕ} {a b : ℤ} (h : a ≡ b [ZMOD (p:ℤ)]) :
    (p:ℤ)*a ≡ (p:ℤ)*b [ZMOD (p:ℤ)^2] := by
  simpa [pow_two] using h.mul_left' (c := (p:ℤ))

private theorem fac_ne (n : ℕ) : fac n ≠ 0 := by
  simpa [fac] using Nat.factorial_ne_zero n

private theorem choose_L {n k : ℕ} (hk : k ≤ n) :
    fac k * (n.choose k : ℤ) = L ((n:ℤ)-k+1) 1 k := by
  have h : fac k * (n.choose k : ℤ) * fac (n-k) = fac n := by
    simpa [fac, mul_comm (k.factorial : ℤ) (n.choose k : ℤ)] using
      (show (n.choose k : ℤ) * (k.factorial : ℤ) * ((n-k).factorial : ℤ) = (n.factorial : ℤ) by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk)
  apply mul_right_cancel₀ (fac_ne (n-k))
  rw [h, mul_comm, ← Nat.cast_sub hk, fac_mul_L, Nat.sub_add_cancel hk]

private def d (p : ℕ) : ℤ := fac (p-1) * L ((p:ℤ)+1) 1 (p-1)
private def D (p m : ℕ) : ℤ := d p * fac m ^ 4 * O m 0 ^ 2

private theorem d_fac {p : ℕ} (hp : 0 < p) :
    (p:ℤ)*d p = fac (2*p-1) := by
  unfold d
  rw [← mul_assoc, show (p:ℤ)*fac (p-1) = fac p by
    have h := fac_succ (p-1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p), Nat.cast_sub (by omega : 1 ≤ p)] at h
    linear_combination -h]
  rw [fac_mul_L]
  congr 1
  omega

private theorem P_dvd {m j : ℕ} (h : 2*j ≥ m) (hj : j < m) :
    ((2*m+1 : ℕ) : ℤ) ∣ P j m := by
  have h0 := L_dvd (4*(j:ℤ)+1) (-2) (show 2*j-m < m by omega)
  unfold P
  convert h0 using 1
  rw [Nat.cast_sub h]
  push_cast
  ring

private theorem Q_dvd {m j : ℕ} (h0 : 0 < j) (h : j ≤ m) :
    ((2*m+1 : ℕ) : ℤ) ∣ Q j m := by
  have hd := L_dvd (2*(j:ℤ)+1) 2 (show m-j < m by omega)
  simpa only [Q, Nat.cast_sub h, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    show 2*(j:ℤ)+1+2*((m:ℤ)-j) = 2*m+1 by ring] using hd

private theorem base_dvd {m j : ℕ} (h : 2*j < m) :
    ((2*m+1 : ℕ) : ℤ) ∣ base m j := by
  have h' : 4*j+1 ≤ 2*m := by omega
  have hd := L_dvd (((4*j+1:ℕ):ℤ)+1) 1
    (show 2*m-(4*j+1) < (4*m+1)-(4*j+1) by omega)
  rw [Nat.cast_sub h'] at hd
  have hcast : ((4*j+1:ℕ):ℤ)+1+1*(((2*m:ℕ):ℤ)-((4*j+1:ℕ):ℤ)) =
      ((2*m+1:ℕ):ℤ) := by push_cast; ring
  rw [hcast] at hd
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _

-- Every interior term in the last row has two factors of p.
private theorem middle_zero {p m j : ℕ} (hp : p = 2*m+1) (h0 : 0 < j) (hj : j < m) :
    F m j m ≡ 0 [ZMOD (p:ℤ)^2] := by
  rw [Int.modEq_zero_iff_dvd]
  subst p
  have hQ := Q_dvd h0 hj.le
  by_cases h : 2*j < m
  · obtain ⟨c,hc⟩ := base_dvd h
    obtain ⟨b,hb⟩ := hQ
    refine ⟨(20*(j:ℤ)+2*m+7) * c * (-1)^m * P j m * b * O m m ^ 2, ?_⟩
    rw [F, U, hc, hb]
    ring
  · obtain ⟨c,hc⟩ := P_dvd (by omega : m ≤ 2*j) hj
    obtain ⟨b,hb⟩ := hQ
    refine ⟨(20*(j:ℤ)+2*m+7) * base m j * (-1)^m * c * b * O m m ^ 2, ?_⟩
    rw [F, U, hc, hb]
    ring

private theorem shift_sum {p m : ℕ} (hp : p = 2*m+1) :
    (∑ j ∈ range (m+1), F m j m) ≡
      (∑ j ∈ range (m+1), F m j 0) [ZMOD (p:ℤ)^2] := by
  suffices h : ∀ k ≤ m, (∑ j ∈ range (m+1), F m j k) ≡
      (∑ j ∈ range (m+1), F m j 0) [ZMOD (p:ℤ)^2] by exact h m le_rfl
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hG : (p:ℤ)^2 ∣ -G m m k := by
      refine ⟨-(16*(2*(m:ℤ)+2*k+1) *
        (base m m * (-1)^k * P m k * Q m k * O m (k+1)^2)), ?_⟩
      rw [G, hp]
      push_cast
      ring
    have hd := hG.modEq_zero_int
    rw [← sum_G m k (by omega)] at hd
    have hs := hd.add (Int.ModEq.refl (∑ j ∈ range (m+1), F m j k))
    rw [sub_add_cancel, zero_add] at hs
    exact hs.trans (ih (by omega))



private theorem p_zero (p : ℕ) : (p:ℤ) ≡ 0 [ZMOD (p:ℤ)] :=
  (dvd_refl _).modEq_zero_int

private theorem paired_prod {p t : ℕ} :
    L ((p:ℤ)-t) 1 (2*t+1) ≡ (p:ℤ)*((-1)^t * fac t ^ 2) [ZMOD (p:ℤ)^2 * p] := by
  have hp : (p:ℤ)^2 ≡ 0 [ZMOD (p:ℤ)^2] := (dvd_refl _).modEq_zero_int
  have he : L ((p:ℤ)-t) 1 (2*t+1) =
      (p:ℤ) * ∏ i ∈ range t, ((p:ℤ)-1-i)*((p:ℤ)+1+i) := by
    rw [show 2*t+1 = t+(t+1) by omega, L_add,
      show (p:ℤ)-t+1*t = p by ring, L_left,
      L_reflect ((p:ℤ)-t) 1 t, show (p:ℤ)-t+1*((t:ℤ)-1) = p-1 by ring]
    simp only [L]
    rw [← mul_assoc, mul_comm (∏ i ∈ range t, ((p:ℤ)-1 + -1 * i))]
    rw [mul_assoc, ← prod_mul_distrib]
    congr 1
    apply prod_congr rfl
    intro i _
    ring
  rw [he]
  have h := prod_mod (s := range t)
    (a := fun i => ((p:ℤ)-1-i)*((p:ℤ)+1+i)) (b := fun i => -((i:ℤ)+1)^2)
    (fun i _ => by
      convert hp.add (Int.ModEq.refl (-((i:ℤ)+1)^2)) using 1 <;> ring)
  have hfac : (∏ i ∈ range t, -((i:ℤ)+1)^2) = (-1)^t * fac t ^ 2 := by
    simp only [← L_fac]
    clear he h
    induction t with
    | zero => simp [L]
    | succ t ih =>
      rw [prod_range_succ, ih, L_succ, pow_succ]
      ring
  rw [hfac] at h
  simpa only [mul_comm ((p:ℤ)^2) (p:ℤ)] using h.mul_left' (c := (p:ℤ))

private theorem pair_even (p j : ℕ) :
    L ((p:ℤ)-2*j) 1 (4*j+1) ≡ (p:ℤ)*fac (2*j)^2 [ZMOD (p:ℤ)^2 * p] := by
  simpa [show 2*(2*j)+1 = 4*j+1 by omega, pow_mul] using paired_prod (p := p) (t := 2*j)

private def C (j : ℕ) : ℤ := (-4)^j * ((2*j).choose j : ℤ)^2
private def V (p j : ℕ) : ℤ := C j * ((p+2*j).choose (4*j+1) : ℤ)

private theorem d_choose {p m j : ℕ} (hp : p = 2*m+1) (hj : j ≤ m) :
    d p * ((p+2*j).choose (4*j+1) : ℤ) ≡
      tail (4*j+1) (4*m+1) * fac (2*j)^2 [ZMOD (p:ℤ)^2] := by
  have h := choose_L (n := p+2*j) (k := 4*j+1) (by omega)
  have hh : L ((p:ℤ)-2*j) 1 (4*j+1) =
      fac (4*j+1) * ((p+2*j).choose (4*j+1) : ℤ) := by
    rw [h]
    congr 1
    push_cast
    ring
  have ht := tail_fac (a := 4*j+1) (b := 4*m+1) (by omega)
  have hd := d_fac (p := p) (by omega)
  rw [show 2*p-1 = 4*m+1 by omega] at hd
  have h1 := (pair_even p j).mul_left (tail (4*j+1) (4*m+1))
  rw [hh, ← mul_assoc, mul_comm (tail (4*j+1) (4*m+1)) (fac (4*j+1)), ht, ← hd] at h1
  apply Int.ModEq.mul_left_cancel' (show (p:ℤ) ≠ 0 by exact_mod_cast (by omega : p ≠ 0))
  rw [mul_comm (p:ℤ) ((p:ℤ)^2)] 
  convert h1 using 1 <;> ring

private theorem fac_choose_tail {m j : ℕ} (hj : j ≤ m) :
    fac m ^ 4 * ((2*j).choose j : ℤ)^2 =
      fac (2*j)^2 * tail j m ^ 4 := by
  have h0 := Nat.choose_mul_factorial_mul_factorial (n := 2*j) (k := j) (by omega)
  rw [show 2*j-j = j by omega] at h0
  have h : ((2*j).choose j : ℤ)*fac j*fac j = fac (2*j) := by
    unfold fac
    exact_mod_cast h0
  rw [← tail_fac hj, ← h]
  ring

private theorem compare_U {p m j : ℕ} (hp : p = 2*m+1) (hj : j ≤ m) :
    D p m * V p j ≡ U m j 0 [ZMOD (p:ℤ)^2] := by
  have h := (d_choose hp hj).mul_left
    ((-4:ℤ)^j * (fac m ^ 4 * ((2*j).choose j : ℤ)^2) * O m 0 ^ 2)
  convert h using 1
  · unfold D V C
    ring
  · rw [fac_choose_tail hj]
    simp [U, base, P, Q, L]
    ring

private theorem sign_sq (m : ℕ) : ((-1:ℤ)^m)^2 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

private theorem O_zero (m : ℕ) : O m 0 = L 1 2 m := by simp [O]

private theorem O_self (m : ℕ) : O m m = 1 := by simp [O, L]

private theorem P_zero_last {m : ℕ} (hm : 0 < m) :
    (-1:ℤ)^m * P 0 m = -L 1 2 (m-1) := by
  have he : P 0 m = (-1)^ (m-1) * L 1 2 (m-1) := by
    unfold P
    simp only [Nat.cast_zero, mul_zero, zero_add]
    rw [show L 1 (-2) m = L 1 (-2) ((m-1)+1) by rw [Nat.sub_add_cancel hm],
      L_left, one_mul]
    exact L_neg 1 2 (m-1)
  rw [he, ← mul_assoc, show (-1:ℤ)^m = (-1)^ (m-1) * (-1) by
    rw [← pow_succ, Nat.sub_add_cancel hm]]
  rw [show (-1:ℤ)^(m-1)*(-1)*(-1)^(m-1) = -(((-1:ℤ)^(m-1))^2) by ring,
    sign_sq, neg_one_mul]

private theorem p_cast {p m : ℕ} (hp : p = 2*m+1) :
    2*(m:ZMod p)+1=0 := by
  have h : ((2*m+1:ℕ):ZMod p) = 0 := by rw [← hp, ZMod.natCast_self]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using h

private theorem F_zero_eval {p m : ℕ} (hp : p = 2*m+1) (hm : 0 < m) :
    F m 0 m ≡ (p:ℤ)*(3*D p m) [ZMOD (p:ℤ)^2] := by
  have hbase : base m 0 = (p:ℤ) * (d p * fac m^4) := by
    have h : tail 1 (4*m+1) = fac (4*m+1) := by
      simpa [show fac 1 = 1 by rfl] using tail_fac (a := 1) (b := 4*m+1) (by omega)
    have hh : tail 0 m = fac m := by
      simpa [show fac 0 = 1 by rfl] using tail_fac (a := 0) (b := m) (by omega)
    have hd := d_fac (p := p) (by omega)
    rw [show 2*p-1 = 4*m+1 by omega] at hd
    simp only [base, pow_zero, Nat.mul_zero, Nat.zero_add, one_mul,
      show fac 0 = 1 by rfl, one_pow, hh, h, ← hd]
    ring
  have hO : L 1 2 m = L 1 2 (m-1)*(2*(m:ℤ)-1) := by
    nth_rw 1 [show m = (m-1)+1 by omega]
    rw [L_succ, Nat.cast_sub hm, Nat.cast_one]
    ring
  have hF : F m 0 m = (p:ℤ) *
      (-(2*(m:ℤ)+7) * (d p * fac m^4) * L 1 2 (m-1) * L 1 2 m) := by
    unfold F U
    rw [O_self, hbase, show Q 0 m = L 1 2 m by simp [Q]]
    calc
      _ = (p:ℤ) * ((2*(m:ℤ)+7) * (d p * fac m^4) *
          ((-1:ℤ)^m * P 0 m) * L 1 2 m) := by simp; ring
      _ = _ := by rw [P_zero_last hm]; ring
  rw [hF]
  apply mod_mul_p
  apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
  have hO' := congrArg (fun a : ℤ => (a : ZMod p)) hO
  push_cast at hO'
  unfold D
  rw [O_zero]
  push_cast
  calc
    _ = 3 * (d p : ZMod p) * (fac m : ZMod p)^4 *
        ((L 1 2 (m-1) : ZMod p)*(2*(m:ZMod p)-1)) * (L 1 2 m : ZMod p) := by
      linear_combination -(d p : ZMod p) * (fac m : ZMod p)^4 *
        (L 1 2 (m-1) : ZMod p) * (L 1 2 m : ZMod p) * 4 * p_cast hp
    _ = _ := by rw [← hO']; ring

private theorem sign_sq_zmod (p m : ℕ) : ((-1:ZMod p)^m)^2 = 1 := by
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using
    congrArg (fun a : ℤ => (a : ZMod p)) (sign_sq m)

private theorem fac_unit_p {p n : ℕ} (hp : p.Prime) (h : n < p) :
    IsUnit (fac n : ZMod p) := by
  simpa [fac, ZMod.isUnit_iff_coprime] using (hp.coprime_factorial_of_lt h).symm

private theorem fac_unit_pSq {p n : ℕ} (hp : p.Prime) (h : n < p) :
    IsUnit (fac n : ZMod (p^2)) := by
  simpa [fac, ZMod.isUnit_iff_coprime] using (hp.coprime_factorial_of_lt h).symm.pow_right 2

private theorem choose_sign {p m : ℕ} (hp : p.Prime) (he : p = 2*m+1) :
    ((2*m).choose m : ZMod p) = (-1)^m := by
  have hc := choose_L (n := 2*m) (k := m) (by omega)
  have h : ((2*m:ℕ):ℤ)-(m:ℤ)+1+1*((m:ℤ)-1) = (p:ℤ)-1 := by
    rw [he]
    push_cast
    ring
  rw [L_reflect, h] at hc
  have hl := L_mod ((p_zero p).sub_right 1) (Int.ModEq.refl (-1)) m
  rw [zero_sub, L_neg, L_fac, ← hc] at hl
  apply (fac_unit_p hp (by omega : m < p)).mul_left_cancel
  have hh := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hl
  push_cast at hh
  simpa [mul_comm] using hh

private theorem C_sign {p m : ℕ} [Fact p.Prime] (he : p = 2*m+1) :
    (C m : ZMod p) = (-1)^m := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hd
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by have := hp.two_le; omega))
      ((ZMod.natCast_eq_zero_iff 2 p).mp hd)
  have h4 : (4 : ZMod p)^m = 1 := by
    rw [show (4 : ZMod p) = 2^2 by ring, ← pow_mul, show 2*m = p-1 by omega]
    exact ZMod.pow_card_sub_one_eq_one h2
  unfold C
  push_cast
  rw [choose_sign hp he, sign_sq_zmod, mul_one, neg_pow, h4, mul_one]

private theorem E_last {p m : ℕ} (he : p = 2*m+1) (hm : 0 < m) :
    (-1:ZMod p)^m * (L (2+(p:ℤ)) 2 (m-1) : ZMod p) = -(O m 0 : ZMod p) := by
  have hl := L_mod ((p_zero p).add_left 2) (Int.ModEq.refl 2) (m-1)
  have hc := (ZMod.intCast_eq_intCast_iff _ _ p).mpr (by simpa using hl)
  rw [hc, O_zero, L_reflect 1 2 m]
  have hcast := L_mod (a := 1+2*((m:ℤ)-1)) (a' := -2) (b := -2) (b' := -2)
    (by
      have h := (p_zero p).sub_right 2
      rw [zero_sub] at h
      convert h using 1
      rw [he]
      push_cast
      ring)
    Int.ModEq.rfl m
  rw [L_neg 2 2 m] at hcast
  have hh := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hcast
  rw [hh, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  have hL : L 2 2 m = L 2 2 (m-1) * (2*(m:ℤ)) := by
    nth_rw 1 [show m = (m-1)+1 by omega]
    rw [L_succ, Nat.cast_sub hm, Nat.cast_one]
    ring
  rw [hL]
  push_cast
  linear_combination (-1:ZMod p)^m * (L 2 2 (m-1) : ZMod p) * p_cast he

private theorem F_last_eval {p m : ℕ} [Fact p.Prime] (he : p = 2*m+1) (hm : 0 < m) :
    F m m m ≡ (p:ℤ)*(4*D p m) [ZMOD (p:ℤ)^2] := by
  have hQ : Q m m = (p:ℤ)*L (2+(p:ℤ)) 2 (m-1) := by
    unfold Q
    have hh : (2*(m:ℤ)+1) = p := by rw [he]; push_cast; ring
    rw [hh, show L (p:ℤ) 2 m = L (p:ℤ) 2 ((m-1)+1) by rw [Nat.sub_add_cancel hm], L_left]
    ring_nf
  have hP : (P m m : ZMod p) = (-1)^m * (O m 0 : ZMod p) := by
    have hh : (4*(m:ℤ)+1) = 2*(p:ℤ)-1 := by rw [he]; push_cast; ring
    have h := L_mod (a := 4*(m:ℤ)+1) (a' := -1) (b := -2) (b' := -2)
      (by rw [hh]; simpa using ((p_zero p).mul_left 2).sub_right 1)
      Int.ModEq.rfl m
    rw [L_neg 1 2 m, ← O_zero] at h
    have hc := (ZMod.intCast_eq_intCast_iff _ _ p).mpr h
    simpa only [P, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using hc
  have hU := (compare_U he (j := m) le_rfl).of_dvd (dvd_pow_self (p:ℤ) (by decide : 2 ≠ 0))
  have hU' := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hU
  have hbase : (base m m : ZMod p) * (O m 0 : ZMod p)^2 =
      (D p m : ZMod p) * (-1)^m := by
    simpa only [V, he, show (2*m+1)+2*m=4*m+1 by omega, Nat.choose_self,
      Nat.cast_one, Int.cast_mul, mul_one, U, pow_zero, Int.cast_pow,
      show P m 0 = 1 by simp [P, L], show Q m 0 = 1 by simp [Q, L], Int.cast_one,
      C_sign he] using hU'.symm
  have hf : F m m m = (p:ℤ) * ((22*(m:ℤ)+7) * base m m * (-1)^m * P m m *
      L (2+(p:ℤ)) 2 (m-1)) := by
    rw [F, U, hQ, O_self]
    ring
  rw [hf]
  apply mod_mul_p
  apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
  push_cast
  rw [hP, show (22:ZMod p)*m+7 = -4 by linear_combination 11 * p_cast he]
  have hsign := sign_sq_zmod p m
  calc
    _ = (-(4:ZMod p)) * (base m m : ZMod p) * (O m 0 : ZMod p) *
        ((-1:ZMod p)^m * ((-1:ZMod p)^m * (L (2+(p:ℤ)) 2 (m-1) : ZMod p))) := by ring
    _ = _ := by
      rw [E_last he hm]
      calc
        _ = 4 * ((base m m : ZMod p)*(O m 0 : ZMod p)^2)*(-1)^m := by ring
        _ = _ := by rw [hbase]; linear_combination 4 * (D p m : ZMod p) * hsign

private theorem small_unit_sq {p n : ℕ} (hp : p.Prime) (h0 : 0 < n) (hn : n < p) :
    IsUnit (n : ZMod (p^2)) :=
  (ZMod.isUnit_iff_coprime _ _).mpr
    (((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt h0 hn)).symm).pow_right 2)

private theorem prod_unit {R : Type*} [CommMonoid R] {s : Finset ℕ} {f : ℕ → R}
    (hu : ∀ i ∈ s, IsUnit (f i)) : IsUnit (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi]
    exact (hu i (mem_insert_self _ _)).mul (ih fun j hj => hu j (mem_insert_of_mem hj))

private theorem D_unit {p m : ℕ} (hp : p.Prime) (he : p = 2*m+1) :
    IsUnit (D p m : ZMod (p^2)) := by
  have ho : IsUnit (O m 0 : ZMod (p^2)) := by
    rw [O_zero]
    simp only [L, Int.cast_prod, Int.cast_add, Int.cast_mul, Int.cast_one,
      Int.cast_ofNat, Int.cast_natCast]
    apply prod_unit
    intro i hi
    rw [mem_range] at hi
    have h := small_unit_sq hp (n := 1+2*i) (by omega) (by omega)
    push_cast at h
    exact h
  have hd : IsUnit (d p : ZMod (p^2)) := by
    unfold d
    rw [Int.cast_mul]
    apply (fac_unit_pSq hp (by have := hp.pos; omega)).mul
    simp only [L, Int.cast_prod, Int.cast_add, Int.cast_one, Int.cast_natCast, one_mul]
    apply prod_unit
    intro i hi
    rw [mem_range] at hi
    have h : Nat.Coprime (1+i) p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have hh : (p+(1+i)).Coprime p := by simpa using h
    have ht := (ZMod.isUnit_iff_coprime _ _).mpr (hh.pow_right 2)
    push_cast at ht
    simpa only [add_assoc] using ht
  unfold D
  push_cast
  exact (hd.mul ((fac_unit_pSq hp (by omega : m < p)).pow 4)).mul (ho.pow 2)

private theorem weighted_V {p m : ℕ} [Fact p.Prime] (he : p = 2*m+1) (hm : 0 < m) :
    (∑ j ∈ range (m+1), (20*(j:ℤ)+7)*V p j) ≡ 7*(p:ℤ) [ZMOD (p:ℤ)^2] := by
  have hcompare : D p m * (∑ j ∈ range (m+1), (20*(j:ℤ)+7)*V p j) ≡
      (∑ j ∈ range (m+1), F m j 0) [ZMOD (p:ℤ)^2] := by
    rw [mul_sum]
    apply sum_mod
    intro j hj
    rw [mem_range] at hj
    unfold F
    simpa only [Nat.cast_zero, mul_zero, add_zero, mul_left_comm] using
      (compare_U he (by omega : j ≤ m)).mul_left (20*(j:ℤ)+7)
  have hlast : (∑ j ∈ range (m+1), F m j m) ≡
      (p:ℤ)*(3*D p m) + (p:ℤ)*(4*D p m) [ZMOD (p:ℤ)^2] := by
    rw [sum_range_succ, ← sum_range_add_sum_Ico _ (show 1 ≤ m by omega), sum_range_one]
    have hz : (∑ j ∈ Ico 1 m, F m j m) ≡ 0 [ZMOD (p:ℤ)^2] := by
      simpa using (sum_mod (b := fun _ => 0) fun j hj => by
        rw [mem_Ico] at hj
        exact middle_zero he (by omega) hj.2)
    simpa using ((F_zero_eval he hm).add hz).add (F_last_eval he hm)
  have h := hcompare.trans ((shift_sum he).symm.trans hlast)
  apply cast_modSq.mp
  apply (D_unit Fact.out he).mul_left_cancel
  have hc := cast_modSq.mpr h
  push_cast at hc ⊢
  linear_combination hc

-- The convolution is the coefficient of a product of two negative binomial series.
private theorem conv_choose (a b n : ℕ) :
    (∑ i ∈ range (n+1), ((a+i).choose a : ℤ) * ((b+(n-i)).choose b : ℤ)) =
      ((a+b+1+n).choose (a+b+1) : ℤ) := by
  have h := congrArg (fun u : (PowerSeries ℤ)ˣ => PowerSeries.coeff n u.val)
    (PowerSeries.invOneSubPow_add ℤ (d := a+1) (b+1))
  change PowerSeries.coeff n (PowerSeries.invOneSubPow ℤ (a+1+(b+1))).val =
    PowerSeries.coeff n ((PowerSeries.invOneSubPow ℤ (a+1)).val *
      (PowerSeries.invOneSubPow ℤ (b+1)).val) at h
  rw [show a+1+(b+1) = (a+b+1)+1 by omega,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa using h.symm

private theorem choose_reflect {p t i : ℕ} (hp : p.Prime) (ht : 2*t < p)
    (hi : i < p-2*t) :
    ((2*t+i).choose (2*t) : ℤ) ≡ ((2*t+(p-2*t-1-i)).choose (2*t) : ℤ) [ZMOD (p:ℤ)] := by
  let m := 2*t
  let j := p-m-1-i
  have he : (m:ℤ)+(j:ℤ)+(i:ℤ)+1 = p := by
    dsimp [j]
    rw [Nat.cast_sub (by omega : i ≤ p-m-1),
      Nat.cast_sub (by omega : 1 ≤ p-m), Nat.cast_sub (by omega : m ≤ p), Nat.cast_one]
    ring
  change ((m+i).choose m : ℤ) ≡ ((m+j).choose m : ℤ) [ZMOD (p:ℤ)]
  have hl (k : ℕ) : fac m * ((m+k).choose m : ℤ) = L ((k:ℤ)+1) 1 m := by
    rw [choose_L (by omega)]
    congr 1
    push_cast
    ring
  have hx : (j:ℤ)+1+1*((m:ℤ)-1) = (p:ℤ)-((i:ℤ)+1) := by linarith
  have hsign : (-1:ℤ)^m = 1 := by simp [m, pow_mul]
  have hh : L ((j:ℤ)+1) 1 m ≡ L ((i:ℤ)+1) 1 m [ZMOD (p:ℤ)] := by
    rw [L_reflect ((j:ℤ)+1) 1 m, hx]
    have hh := L_mod ((p_zero p).sub_right ((i:ℤ)+1)) (Int.ModEq.refl (-1)) m
    rw [zero_sub, L_neg, hsign, one_mul] at hh
    exact hh
  rw [← hl, ← hl] at hh
  apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
  apply (fac_unit_p hp ht).mul_left_cancel
  have hcast := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hh.symm
  simpa only [Int.cast_mul] using hcast

private theorem nat_two_unit {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    IsUnit (2 : ZMod (p^2)) := by
  have ht : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
  have h : Nat.Coprime 2 p := (hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide) ht)).symm
  simpa using (ZMod.isUnit_iff_coprime 2 (p^2)).mpr (h.pow_right 2)

-- Reflection replaces the squares by the binomial convolution modulo p².
private theorem sum_choose_sq {p j : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hj : 2*j < p) :
    (∑ n ∈ range p, (n.choose (2*j) : ℤ)^2) ≡
      ((p+2*j).choose (4*j+1) : ℤ) [ZMOD (p:ℤ)^2] := by
  let m := 2*j
  let n := p-m-1
  let f : ℕ → ℤ := fun i => ((m+i).choose m : ℤ)
  have hn : n+1 = p-m := by dsimp [n]; omega
  have hm : m+m+1+n = p+2*j := by dsimp [m,n]; omega
  have hs : (∑ k ∈ range p, (k.choose (2*j) : ℤ)^2) =
      ∑ i ∈ range (n+1), (f i)^2 := by
    rw [← sum_range_add_sum_Ico _ (by omega : m ≤ p)]
    have hz : (∑ k ∈ range m, (k.choose (2*j) : ℤ)^2) = 0 := by
      apply sum_eq_zero
      intro k hk
      rw [Nat.choose_eq_zero_of_lt (mem_range.mp hk)]
      simp
    rw [hz, zero_add, sum_Ico_eq_sum_range, hn]
  have hc : (∑ i ∈ range (n+1), f i * f (n-i)) =
      ((p+2*j).choose (4*j+1) : ℤ) := by
    have hc := conv_choose m m n
    rw [hm, show m+m+1 = 4*j+1 by dsimp [m]; omega] at hc
    exact hc
  have hd : ∀ i ∈ range (n+1), (p:ℤ) ∣ f i - f (n-i) := by
    intro i hi
    have h := choose_reflect hp hj (by rw [← hn]; exact mem_range.mp hi)
    exact (Int.modEq_iff_dvd.mp h.symm)
  have hsum : (2:ℤ)*(∑ i ∈ range (n+1), (f i)^2) -
      2*(∑ i ∈ range (n+1), f i*f (n-i)) =
      ∑ i ∈ range (n+1), (f i-f (n-i))^2 := by
    have hr := sum_range_reflect (fun i => (f i)^2) (n+1)
    rw [Nat.add_sub_cancel] at hr
    have he : (∑ i ∈ range (n+1), (f i-f (n-i))^2) =
        ∑ i ∈ range (n+1), ((f i)^2 + (f (n-i))^2 - 2*(f i*f (n-i))) := by
      apply sum_congr rfl
      intro i _
      ring
    rw [he, sum_sub_distrib, sum_add_distrib, ← mul_sum]
    rw [hr]
    ring
  have hmod : (∑ i ∈ range (n+1), (f i-f (n-i))^2) ≡ 0 [ZMOD (p:ℤ)^2] := by
    simpa using (sum_mod (b := fun _ => 0)
      (fun i hi => by
        obtain ⟨d,hh⟩ := hd i hi
        rw [hh, Int.modEq_zero_iff_dvd, mul_pow]
        exact dvd_mul_right _ _))
  rw [← hsum] at hmod
  have htwice := hmod.add (Int.ModEq.refl (2*(∑ i ∈ range (n+1), f i*f (n-i))))
  rw [sub_add_cancel, zero_add, ← hs, hc] at htwice
  apply cast_modSq.mp
  apply (nat_two_unit hp h2).mul_left_cancel
  simpa only [Int.cast_mul, Int.cast_ofNat] using cast_modSq.mpr htwice

-- The factor m+1 is essential because it equals p at the exceptional index.
private theorem weighted_tel (p m : ℕ) :
    ((m:ℤ)+1)*(∑ n ∈ range p, (2*(n:ℤ)+1-m) * (n.choose m : ℤ)^2) =
      ((p:ℤ)-m)^2 * (p.choose m : ℤ)^2 := by
  let g : ℕ → ℤ := fun n => ((n:ℤ)-m)^2 * (n.choose m : ℤ)^2
  have h (n : ℕ) : (((n:ℤ)+1)-m) * ((n+1).choose m : ℤ) =
      ((n:ℤ)+1)*(n.choose m : ℤ) := by
    by_cases hn : m ≤ n+1
    · have ht : ((n.choose m : ℤ))*((n:ℤ)+1) =
          ((n+1).choose m : ℤ) * (((n:ℤ)+1)-m) := by
        exact_mod_cast (show n.choose m * (n+1) = (n+1).choose m * (n+1-m) from
          Nat.choose_mul_succ_eq n m)
      linarith only [ht]
    · rw [Nat.choose_eq_zero_of_lt (by omega : n+1 < m),
        Nat.choose_eq_zero_of_lt (by omega : n < m)]
      simp
  have hs (n : ℕ) : ((m:ℤ)+1)*((2*(n:ℤ)+1-m)*(n.choose m : ℤ)^2) = g (n+1)-g n := by
    unfold g
    push_cast
    have hn := congrArg (fun x : ℤ => x^2) (h n)
    linear_combination -hn
  rw [mul_sum, sum_congr rfl (fun n _ => hs n), sum_range_sub]
  by_cases hm : m = 0
  · subst m
    simp [g]
  · simp [g, Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hm)]


private def moment (p m : ℕ) : ℤ :=
  ∑ n ∈ range p, (2*(n:ℤ)+1-m) * (n.choose m : ℤ)^2

private theorem moment_zero {p m : ℕ} (hp : p.Prime) (hm : m+1 < p) :
    moment p m ≡ 0 [ZMOD (p:ℤ)^2] := by
  have hd : (p:ℤ)^2 ∣ ((p:ℤ)-m)^2*(p.choose m : ℤ)^2 := by
    by_cases h : m = 0
    · subst m
      simp
    · obtain ⟨d,hd⟩ := hp.dvd_choose_self h (by omega : m < p)
      refine ⟨((p:ℤ)-m)^2*(d:ℤ)^2, ?_⟩
      rw [hd]
      push_cast
      ring
  have h := hd.modEq_zero_int
  rw [← weighted_tel] at h
  apply cast_modSq.mp
  have hu : IsUnit (((m+1:ℕ):ZMod (p^2))) :=
    (ZMod.isUnit_iff_coprime _ _).mpr
      (((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hm)).symm).pow_right 2)
  apply hu.mul_left_cancel
  have hh := cast_modSq.mpr h
  simpa only [moment, Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Nat.cast_add, Nat.cast_one, Int.cast_zero, mul_zero] using hh

private theorem moment_last {p m : ℕ} (he : p = m+1) :
    moment p m = p := by
  have h := weighted_tel p m
  have hc : p.choose m = p := by
    rw [← Nat.choose_symm (by omega : m ≤ p), show p-m = 1 by omega, Nat.choose_one_right]
  have hd : (p:ℤ)-m = 1 := by rw [he]; push_cast; ring
  rw [hc, hd, one_pow, one_mul, ← moment] at h
  have he' : (m:ℤ)+1 = p := by rw [he]; push_cast; rfl
  rw [he', pow_two] at h
  exact mul_left_cancel₀ (show (p:ℤ) ≠ 0 by exact_mod_cast (by omega : p ≠ 0)) h

private theorem choose_prod (n j : ℕ) :
    n.choose j * (n-j).choose j = n.choose (2*j) * (2*j).choose j := by
  simpa only [show 2*j-j = j by omega] using
    (Nat.choose_mul (n := n) (k := 2*j) (s := j) (by omega)).symm

private theorem a_expand {p m n : ℕ} (he : p = 2*m+1) (hn : n < p) :
    OeisA179524.a n = ∑ j ∈ range (m+1), C j * (n.choose (2*j) : ℤ)^2 := by
  let f : ℕ → ℤ := fun j => C j * (n.choose (2*j) : ℤ)^2
  have ht (j : ℕ) : (-4:ℤ)^j * (n.choose j : ℤ)^2 * ((n-j).choose j : ℤ)^2 = f j := by
    have h : (n.choose j : ℤ)*((n-j).choose j : ℤ) =
        (n.choose (2*j) : ℤ)*((2*j).choose j : ℤ) := by
      exact_mod_cast choose_prod n j
    unfold f C
    rw [show (-4:ℤ)^j * (n.choose j : ℤ)^2 * ((n-j).choose j : ℤ)^2 =
      (-4:ℤ)^j * ((n.choose j : ℤ)*((n-j).choose j : ℤ))^2 by ring, h]
    ring
  have hz (j : ℕ) (hj : n < 2*j) : f j = 0 := by
    simp [f, Nat.choose_eq_zero_of_lt hj]
  unfold OeisA179524.a
  simp_rw [ht]
  calc
    (∑ j ∈ range (n+1), f j) = ∑ j ∈ range p, f j := by
      apply sum_subset (range_mono (by omega))
      intro j hj hnj
      rw [mem_range] at hj hnj
      exact hz j (by omega)
    _ = ∑ j ∈ range (m+1), f j := by
      symm
      apply sum_subset (range_mono (by omega))
      intro j hj hnj
      rw [mem_range] at hj hnj
      exact hz j (by omega)

private theorem split_sum {p m : ℕ} (he : p = 2*m+1) :
    (∑ n ∈ range p, (20*(n:ℤ)+17)*OeisA179524.a n) =
      10*(∑ j ∈ range (m+1), C j * moment p (2*j)) +
        (∑ j ∈ range (m+1), (20*(j:ℤ)+7)*C j *
          (∑ n ∈ range p, (n.choose (2*j) : ℤ)^2)) := by
  have h (j : ℕ) :
      (∑ n ∈ range p, (20*(n:ℤ)+17)*(C j * (n.choose (2*j):ℤ)^2)) =
        10*(C j * moment p (2*j)) +
          (20*(j:ℤ)+7)*C j * (∑ n ∈ range p, (n.choose (2*j):ℤ)^2) := by
    unfold moment
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    push_cast
    ring
  calc
    _ = ∑ n ∈ range p, ∑ j ∈ range (m+1),
        (20*(n:ℤ)+17)*(C j * (n.choose (2*j):ℤ)^2) := by
      apply sum_congr rfl
      intro n hn
      rw [a_expand he (mem_range.mp hn), mul_sum]
    _ = _ := by rw [sum_comm]; simp_rw [h, sum_add_distrib, ← mul_sum]

private theorem replace_squares {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : p = 2*m+1) :
    (∑ j ∈ range (m+1), (20*(j:ℤ)+7)*C j *
      (∑ n ∈ range p, (n.choose (2*j):ℤ)^2)) ≡
      (∑ j ∈ range (m+1), (20*(j:ℤ)+7)*V p j) [ZMOD (p:ℤ)^2] := by
  apply sum_mod
  intro j hj
  rw [mem_range] at hj
  unfold V
  rw [← mul_assoc]
  exact (sum_choose_sq hp hp2 (by omega : 2*j < p)).mul_left _


private theorem weighted_C {p m : ℕ} [Fact p.Prime] (he : p = 2*m+1) :
    (∑ j ∈ range (m+1), C j * moment p (2*j)) ≡
      (p:ℤ)*(-1)^m [ZMOD (p:ℤ)^2] := by
  rw [sum_range_succ, moment_last (p := p) he]
  have hz : (∑ j ∈ range m, C j * moment p (2*j)) ≡ 0 [ZMOD (p:ℤ)^2] := by
    simpa using (sum_mod (b := fun _ => 0) fun j hj => by
      rw [mem_range] at hj
      simpa only [mul_zero] using
        (moment_zero (m := 2*j) Fact.out (by omega)).mul_left (C j))
  have hc : C m ≡ (-1)^m [ZMOD (p:ℤ)] :=
    (ZMod.intCast_eq_intCast_iff _ _ p).mp (by
      simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using C_sign he)
  have hp := mod_mul_p hc
  rw [mul_comm (p:ℤ) (C m)] at hp
  simpa only [zero_add] using hz.add hp

private theorem result (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (∑ k ∈ range p, (20*(k:ℤ)+17)*OeisA179524.a k) ≡
      (p:ℤ)*(10*legendreSym p (-1)+7) [ZMOD (p:ℤ)^2] := by
  have hp : p.Prime := Fact.out
  have ho : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  let m := p / 2
  have he : p = 2*m+1 := by dsimp [m]; omega
  have hm : 0 < m := by have := hp.two_le; omega
  have hsign : legendreSym p (-1) = (-1)^m := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_eq_neg_one_pow ho]
  rw [split_sum he, hsign]
  have h := ((weighted_C he).mul_left 10).add
    ((replace_squares hp hp2 he).trans (weighted_V he hm))
  convert h using 1
  ring

end OMA.A179524

-- Credit: @MrSeizy
theorem OMA.solution : type_of% @OeisA179524.conjecture5 :=
  OMA.A179524.result
