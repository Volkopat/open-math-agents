import OMAReductions.R_oeis_a292082_R1

/-! Dyadic Pell coordinates, their prime divisors and effective primality tests.
Credit: @connoranderson. The parent reduction by @physbuzz identifies all possible
prime coordinates. The questions about prime divisors and squarefreeness, as well
as the square-product identity, are discussed by hardmath and Michael Somos:
https://math.stackexchange.com/questions/3176065/prime-divisors-of-a-babylonian-sequence
The two distribution assertions at the end remain open. -/

namespace Pell292


theorem x_zero : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) 0 = 3 := rfl

theorem x_succ (n : ℕ) : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1) = 2*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n)^2-1 := rfl

theorem x_ge (n : ℕ) : 3 ≤ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [x_succ]
    have : 9 ≤ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n)^2 := by nlinarith
    omega

theorem x_succ_add_one (n : ℕ) : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)+1 = 2*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n)^2 := by
  rw [x_succ]
  have h := x_ge n
  have : 1 ≤ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n)^2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem x_strict : StrictMono (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := x_succ_add_one n
  have h' := x_ge n
  nlinarith

theorem x_two_succ_sub_one (n : ℕ) : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2)-1 =
    4*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n)^2*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)-1) := by
  have h := x_succ_add_one (n+1)
  have h' := x_succ_add_one n
  have h1 := x_ge (n+1)
  have h2 := x_ge (n+2)
  zify [show 1 ≤ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2) by omega, show 1 ≤ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1) by omega] at *
  linear_combination (2 : ℤ)*h + (2*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1):ℤ)-2)*h' - h

theorem x_square_formula (n : ℕ) : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1) =
    (2^(n+2) * ∏ i ∈ Finset.range n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i)^2 + 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := x_two_succ_sub_one n
    have h1 := x_ge (n+2)
    rw [ih, Nat.add_sub_cancel] at h
    have e : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2) = 4*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n)^2*(2^(n+2) * ∏ i ∈ Finset.range n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i)^2 + 1 := by omega
    rw [e, Finset.prod_range_succ, show n+1+2=n+2+1 by omega, pow_succ (2:ℕ) (n+2)]
    ring

theorem x_growth (n : ℕ) : 3^(2^n) ≤ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := x_succ_add_one n
    have h' := x_ge n
    rw [pow_succ (2:ℕ) n, pow_mul]
    exact (Nat.pow_le_pow_left ih 2).trans (by nlinarith)

end Pell292

namespace Pell292


/-- The trace recurrence after choosing a square root of two. -/
theorem trace_power {p : ℕ} (t : ZMod p) (ht : t^2 = 2) (n : ℕ) :
    ((1+t)^(2^(n+1)))^2+1 = 2*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n : ZMod p)*(1+t)^(2^(n+1)) := by
  induction n with
  | zero =>
    rw [x_zero]
    norm_num
    linear_combination (t^2+4*t+2)*ht
  | succ n ih =>
    have E := congrArg (fun z : ℕ => (z : ZMod p)) (x_succ_add_one n)
    push_cast at E
    have E' : ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1) : ZMod p) = 2*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n : ZMod p)^2-1 := by
      linear_combination E
    rw [E', pow_succ 2 (n+1), pow_mul]
    linear_combination (((1+t)^(2^(n+1)))^2+1+2*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n : ZMod p)*(1+t)^(2^(n+1)))*ih

/-- Prime divisibility is equivalent to the indicated exact multiplicative order. -/
theorem prime_dvd_iff_order {p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (t : ZMod p) (ht : t^2 = 2) (n : ℕ) :
    p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n ↔ orderOf (1+t) = 2^(n+3) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (2 < p) := ⟨hp2⟩
  have htrace := trace_power t ht n
  have hhalf : (1+t)^(2^(n+2)) = ((1+t)^(2^(n+1)))^2 := by
    rw [pow_succ 2 (n+1), pow_mul]
  have hu : (1+t) ≠ 0 := by
    intro h
    have ht1 : t = -1 := by linear_combination h
    rw [ht1, neg_one_sq] at ht
    exact one_ne_zero (by linear_combination -ht : (1 : ZMod p) = 0)
  rw [← ZMod.natCast_eq_zero_iff]
  constructor
  · intro hdiv
    have hneg : (1+t)^(2^(n+2)) = -1 := by
      rw [hhalf]
      rw [hdiv, mul_zero, zero_mul] at htrace
      exact eq_neg_of_add_eq_zero_left htrace
    apply orderOf_eq_prime_pow (p := 2) (n := n+2)
    · rw [hneg]
      exact ZMod.neg_one_ne_one
    · rw [pow_succ 2 (n+2), pow_mul, hneg, neg_one_sq]
  · intro horder
    have hG : ((1+t)^(2^(n+2)))^2 = 1 := by
      rw [← pow_mul, ← pow_succ, ← horder, pow_orderOf_eq_one]
    have hnon : (1+t)^(2^(n+2)) ≠ 1 := by
      intro bad
      have smaller := orderOf_dvd_of_pow_eq_one bad
      rw [horder] at smaller
      have hh := Nat.le_of_dvd (by positivity) smaller
      rw [pow_succ 2 (n+2)] at hh
      have pos : 0 < 2^(n+2) := by positivity
      omega
    have hneg := (sq_eq_one_iff.mp hG).resolve_left hnon
    rw [hhalf] at hneg
    rw [hneg, neg_add_cancel] at htrace
    have htwo : (2 : ZMod p) ≠ 0 := by
      intro h
      have heq : (-1 : ZMod p) = 1 := by linear_combination -h
      exact ZMod.neg_one_ne_one heq
    exact (mul_eq_zero.mp ((mul_eq_zero.mp htrace.symm).resolve_right
      (pow_ne_zero _ hu))).resolve_left htwo

/-- Every positive-index prime divisor supplies a square root of two and an element
whose order is twice as large as the natural trace period. -/
theorem exact_order_of_prime_dvd {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n) : ∃ t : ZMod p, t^2 = 2 ∧ orderOf (1+t) = 2^(n+3) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hz := (ZMod.natCast_eq_zero_iff ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (k+1)) p).mpr hd
  have E := congrArg (fun z : ℕ => (z : ZMod p)) (x_succ_add_one k)
  push_cast at E
  have EE : 2 * ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) k : ZMod p)^2 = 1 := by rw [hz, zero_add] at E; exact E.symm
  have hp2 : 2 < p := by
    have pp := hp.two_le
    by_contra! h
    obtain rfl : p = 2 := by omega
    have zero : (2 : ZMod 2) = 0 := by decide
    rw [zero, zero_mul] at EE
    exact zero_ne_one EE
  let t : ZMod p := 2*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) k : ZMod p)
  have ht : t^2 = 2 := by
    dsimp only [t]
    linear_combination 2*EE
  exact ⟨t, ht, (prime_dvd_iff_order hp hp2 t ht (k+1)).mp hd⟩

theorem divisor_order_modulus {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n) : 2^(n+3) ∣ p-1 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht, horder⟩ := exact_order_of_prime_dvd hn hp hd
  have hnon : 1+t ≠ 0 := by
    intro h
    have ht1 : t = -1 := by linear_combination h
    rw [ht1, neg_one_sq] at ht
    exact one_ne_zero (by linear_combination -ht : (1 : ZMod p) = 0)
  rw [← horder]
  exact ZMod.orderOf_dvd_card_sub_one hnon

theorem divisor_modEq_one {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n) : p ≡ 1 [MOD 2^(n+3)] :=
  ((Nat.modEq_iff_dvd' hp.one_le).mpr (divisor_order_modulus hn hp hd)).symm

end Pell292

namespace Pell292

theorem earlier_square_dvd (i n : ℕ) (hi : i < n) : ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i)^2 ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)-1 := by
  rw [x_square_formula, Nat.add_sub_cancel]
  exact pow_dvd_pow_of_dvd ((Finset.dvd_prod_of_mem (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (Finset.mem_range.mpr hi)).trans
    (dvd_mul_left _ _)) 2

theorem pairwise_coprime : Pairwise (fun i j : ℕ => ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i).Coprime ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) j)) := by
  suffices h : ∀ i j, i < j → ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i).Coprime ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) j) by
    intro i j hne
    rcases lt_or_gt_of_ne hne with lt | gt
    · exact h i j lt
    · exact (h j i gt).symm
  intro i j hij
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
  apply Nat.coprime_of_dvd'
  intro p hp hpi hpj
  by_cases last : i=n
  · subst i
    have d : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)+1 := by
      rw [x_succ_add_one]
      exact (hpi.trans (dvd_pow_self _ (by decide : 2 ≠ 0))).trans (dvd_mul_left _ _)
    exact (Nat.dvd_add_right hpj).mp d
  · have d := (hpi.trans (dvd_pow_self _ (by decide : 2 ≠ 0))).trans
      (earlier_square_dvd i n (by omega))
    have ge := x_ge (n+1)
    have dd : p ∣ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)-1)+1 := by simpa [Nat.sub_add_cancel (by omega : 1 ≤ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1))] using hpj
    exact (Nat.dvd_add_right d).mp dd

theorem fixed_modulus_coprime {n d : ℕ} (hn : 1 ≤ n) (hd : 0 < d)
    (hsize : d ≤ 2^(n+3)) : d.Coprime ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n) := by
  apply Nat.coprime_of_dvd
  intro p hp hpd hpx
  have m := divisor_order_modulus hn hp hpx
  have hl := Nat.le_of_dvd (show 0 < p-1 by have := hp.two_le; omega) m
  have := Nat.le_of_dvd hd hpd
  omega

theorem composite_iff_small_order (n : ℕ) (hn : 1 ≤ n) :
    ¬ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n).Prime ↔ ∃ p : ℕ, p.Prime ∧ 2 < p ∧ p^2 ≤ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n ∧
      ∃ t : ZMod p, t^2=2 ∧ orderOf (1+t)=2^(n+3) := by
  have h := x_ge n
  constructor
  · intro hc
    let p := ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n).minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n := Nat.minFac_dvd _
    have hmod := divisor_order_modulus hn hp hd
    have hl := Nat.le_of_dvd (show 0 < p-1 by have := hp.two_le; omega) hmod
    have hh : 2 ≤ 2^(n+3) := Nat.le_self_pow (by omega) 2
    exact ⟨p,hp,by omega, Nat.minFac_sq_le_self (by omega) hc,
      exact_order_of_prime_dvd hn hp hd⟩
  · rintro ⟨p,hp,hp2,b,t,ht,ho⟩ hx
    have hd := (prime_dvd_iff_order hp hp2 t ht n).mpr ho
    have := (Nat.dvd_prime hx).mp hd
    rcases this with small | big
    · omega
    · rw [←big] at b
      nlinarith

end Pell292

namespace Pell292

theorem x_mod_five (n : ℕ) : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1) % 5 = 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := congrArg (fun t : ℕ => t % 5) (x_succ_add_one (n+1))
    change ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2)+1)%5 = (2*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1))^2)%5 at h
    rw [Nat.mul_mod, Nat.pow_mod ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)) 2 5, ih] at h
    change ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2)+1)%5=3 at h
    change (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2)%5=2
    omega

theorem euler_five_of_prime (n : ℕ) (hp : ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)).Prime) :
    (5 : ZMod ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)))^((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)/2) = -1 := by
  let : Fact ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)).Prime := ⟨hp⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ne : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1) ≠ 2 := by have := x_ge (n+1); omega
  have e := legendreSym.quadratic_reciprocity_one_mod_four (p:=5) (q:=(Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)) (by decide) ne
  have r : legendreSym 5 ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)) = -1 := by
    have h : (((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1) : ℕ) : ZMod 5) = 2 := by
      rw [← ZMod.natCast_mod ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)) 5, x_mod_five]
      rfl
    change quadraticChar (ZMod 5) (((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1) : ℕ) : ZMod 5) = -1
    rw [h]
    decide
  have s := legendreSym.eq_pow ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)) 5
  rw [show legendreSym ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)) 5 = -1 from e.trans r] at s
  simpa using s.symm

/-- A successful base-five Euler test doubles the generic 2-adic exponent,
up to the small shift in the order bound. -/
theorem euler_divisor_modulus (n : ℕ) {p : ℕ} (hp : p.Prime) (hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1))
    (pass : (5 : ZMod ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)))^((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)/2) = -1) :
    2^(2*(n+2)) ∣ p-1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hmod := divisor_order_modulus (n:=n+1) (by omega) hp hd
  have pp := hp.two_le
  have hbig := Nat.le_of_dvd (show 0 < p-1 by omega) hmod
  have blo : 2 ≤ 2^(n+1+3) := Nat.le_self_pow (by omega) 2
  let : Fact (2 < p) := ⟨by omega⟩
  let P := ∏ i ∈ Finset.range n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i
  change 2^(2*(n+2)) ∣ p-1
  have hs : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1) = 2^(2*(n+2))*P^2+1 := by
    rw [x_square_formula]
    dsimp [P]
    ring
  have eh : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)/2 = 2^(2*(n+2)-1)*P^2 := by
    have ex : 2*(n+2) = (2*(n+2)-1)+1 := by omega
    conv at hs => rhs; rw [ex, pow_succ]
    rw [show 2 ^ (2*(n+2)-1)*2*P^2 = 2*(2^(2*(n+2)-1)*P^2) by ring] at hs
    omega
  have e := congrArg (ZMod.castHom hd (ZMod p)) pass
  simp only [map_pow, map_ofNat, map_neg, map_one] at e
  have neg : ((5 : ZMod p)^P^2)^(2^(2*(n+2)-1)) = -1 := by
    rw [←pow_mul, Nat.mul_comm, ←eh]
    simpa using e
  have o : orderOf ((5 : ZMod p)^P^2) = 2^(2*(n+2)-1+1) := by
    apply orderOf_eq_prime_pow (p:=2)
    · rw [neg]
      exact ZMod.neg_one_ne_one
    · rw [pow_succ (2:ℕ) (2*(n+2)-1), pow_mul, neg, neg_one_sq]
  rw [show 2*(n+2)=2*(n+2)-1+1 by omega, ←o]
  apply ZMod.orderOf_dvd_card_sub_one
  intro hz
  rw [hz, zero_pow (by positivity)] at neg
  exact one_ne_zero (by linear_combination neg : (1 : ZMod p) = 0)

end Pell292

/-! The squarefreeness question for this Babylonian sequence was raised by hardmath:
https://math.stackexchange.com/questions/3176065/prime-divisors-of-a-babylonian-sequence .
The lemmas below characterize repeated prime divisors. -/

namespace Pell292


theorem one_sub_pow_sq_zero {R : Type*} [CommRing R] (s : R) (h : s^2 = 0) (k : ℕ) :
    (1-s)^k = 1-(k : R)*s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Nat.cast_add_one]
    linear_combination (k:R)*h

theorem square_root_lift {p k : ℕ} (hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (k+1)) :
    let t : ZMod (p^2) := ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) k : ZMod (p^2)) * (2-((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (k+1) : ZMod (p^2)))
    t^2 = 2 ∧ ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p) t =
       2*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) k : ZMod p) := by
  dsimp only
  have hnil : ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (k+1) : ZMod (p^2))^2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow_of_dvd hd _
  have E := congrArg (fun z : ℕ => (z : ZMod (p^2))) (x_succ_add_one k)
  push_cast at E
  constructor
  · linear_combination (2-2*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (k+1) : ZMod (p^2)))*E.symm +
      (((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) k : ZMod (p^2))^2-2)*hnil
  · rw [map_mul, map_sub, map_natCast, map_natCast, map_ofNat,
        (ZMod.natCast_eq_zero_iff _ _).mpr hd]
    ring

/-- The trace identity modulo p² controls every multiple of the dyadic order whose
cofactor is coprime to p. The result holds for both square roots of two. -/
theorem square_dvd_iff_order_multiple {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n) (t : ZMod (p^2)) (ht : t^2 = 2) (k : ℕ) (hk : ¬ p ∣ k) :
    p^2 ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n ↔ (1+t)^(2^(n+3)*k) = 1 := by
  let v : ZMod (p^2) := (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n
  let z := (1+t)^(2^(n+1))
  have hnil : v^2=0 := by
    dsimp only [v]
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow_of_dvd hd _
  have htrace : z^2+1=2*v*z := trace_power t ht n
  have H : z^4=1-4*v*z := by
    linear_combination (z^2-1+2*v*z)*htrace + 4*z^2*hnil
  have Hpow : (1+t)^(2^(n+3)) = 1-4*v*z := by
    rw [show (2 : ℕ)^(n+3)=2^(n+1)*4 by rw [show n+3=(n+1)+2 by omega, pow_add]; norm_num, pow_mul]
    exact H
  have hs : (4*v*z)^2=0 := by linear_combination 16*z^2*hnil
  rw [pow_mul, Hpow, one_sub_pow_sq_zero _ hs, ← ZMod.natCast_eq_zero_iff]
  change v = 0 ↔ 1 - (k : ZMod (p^2))*(4*v*z) = 1
  constructor
  · rintro hv
    rw [hv]
    ring
  · intro eqn
    have hkU := (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 2)).mpr hk
    have four_le : 4 ≤ 2^(n+3) := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 2 ≤ n+3 by omega)
    have bound := Nat.le_of_dvd (by have := hp.one_lt; omega) (divisor_order_modulus hn hp hd)
    have h4U : IsUnit (4 : ZMod (p^2)) := by
      exact (ZMod.isUnit_natCast_iff_not_dvd_pow (a := 4) hp (by decide : 0 < 2)).mpr
        (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
    have hu : IsUnit (1+t) := isUnit_iff_exists_inv.mpr
      ⟨t-1, by linear_combination ht⟩
    have Hunit : IsUnit ((k : ZMod (p^2))*4*z) := (hkU.mul h4U).mul (hu.pow _)
    apply Hunit.mul_left_cancel
    rw [mul_zero]
    linear_combination -eqn

theorem exists_order_cofactor {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n) :
    ∃ k : ℕ, p-1 = 2^(n+3)*k ∧ ¬ p ∣ k := by
  obtain ⟨k, hk⟩ := divisor_order_modulus hn hp hd
  have hpos : 0 < k := by
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz, mul_zero] at hk
    have := hp.one_lt
    omega
  have hlt : k < p := by
    have h := Nat.le_mul_of_pos_left k (by positivity : 0 < 2^(n+3))
    omega
  exact ⟨k, hk, Nat.not_dvd_of_pos_of_lt hpos hlt⟩

/-- The Pell–Wieferich condition for an arbitrary square root of two modulo p². -/
theorem square_dvd_iff_wieferich {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n) (t : ZMod (p^2)) (ht : t^2 = 2) :
    p^2 ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n ↔ (1+t)^(p-1) = 1 := by
  obtain ⟨k,hk,hcop⟩ := exists_order_cofactor hn hp hd
  rw [hk]
  exact square_dvd_iff_order_multiple hn hp hd t ht k hcop

theorem square_dvd_iff_explicit_wieferich {k p : ℕ} (hp : p.Prime) (hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (k+1)) :
    p^2 ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (k+1) ↔
      (1 + ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) k : ZMod (p^2))*(2-((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (k+1) : ZMod (p^2))))^(p-1) = 1 :=
  square_dvd_iff_wieferich (n := k+1) (by omega) hp hd _ (square_root_lift hd).1

/-- The imaginary coefficient of (1+√2)^m is the m-th Pell number. This
integer criterion dispenses with the choice of a modular square root. -/
theorem square_dvd_iff_pell_number {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n) :
    p^2 ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n ↔ ((p^2 : ℕ) : ℤ) ∣ ((⟨1,1⟩ : Zsqrtd 2)^(p-1)).im := by
  obtain ⟨k,hk,hcop⟩ := exists_order_cofactor hn hp hd
  have hp2 : 2 < p := by
    have h := Nat.le_of_dvd (by have := hp.one_lt; omega) (divisor_order_modulus hn hp hd)
    have h' := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ n+3 by omega)
    change 2^1 ≤ 2^(n+3) at h'
    omega
  have hu2 : IsUnit (2 : ZMod (p^2)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow (a := 2) hp (by decide : 0 < 2)).mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) hp2)
  obtain ⟨t, ht⟩ : ∃ t : ZMod (p^2), t^2 = 2 := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    exact ⟨_, (square_root_lift hd).1⟩
  let α : Zsqrtd 2 := ⟨1,1⟩
  let A : ZMod (p^2) := (α^(p-1)).re
  let B : ZMod (p^2) := (α^(p-1)).im
  have eval (s : ZMod (p^2)) (hs : s^2 = 2) : A+B*s = (1+s)^(p-1) := by
    let F := Zsqrtd.lift (d := 2) ⟨s, by simpa only [pow_two, Int.cast_ofNat] using hs⟩
    change F (α^(p-1)) = _
    rw [map_pow]
    have hα : F α = 1+s := by simp [F, α, Zsqrtd.lift_apply_apply]
    rw [hα]
  have ht' : (-t)^2 = 2 := by simpa only [neg_sq] using ht
  have ep := eval t ht
  have em := eval (-t) ht'
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  change p^2 ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n ↔ B=0
  constructor
  · intro h2
    rw [(square_dvd_iff_wieferich hn hp hd t ht).mp h2] at ep
    rw [(square_dvd_iff_wieferich hn hp hd (-t) ht').mp h2] at em
    have hut : IsUnit t := isUnit_of_mul_isUnit_left (y := t) (by rwa [← pow_two, ht])
    apply (hu2.mul hut).mul_left_cancel
    rw [mul_zero]
    linear_combination ep-em
  · intro hB
    have same : (1+t)^(p-1) = (1+ -t)^(p-1) := by rw [← ep, ← em, hB, zero_mul, zero_mul]
    have evenP := hp.even_sub_one (by omega : p ≠ 2)
    have norm : (1+t) * (1+ -t) = -1 := by linear_combination -ht
    have hex : (1+t)^((p-1)*2) = 1 := by
      rw [pow_mul, pow_two ((1+t)^(p-1))]
      calc
        _ = (1+t)^(p-1)*(1+ -t)^(p-1) := by rw [same]
        _ = _ := by rw [← mul_pow, norm, evenP.neg_one_pow]
    have hk2 : ¬ p ∣ k*2 := fun H => (hp.dvd_mul.mp H).elim hcop
      (Nat.not_dvd_of_pos_of_lt (by decide) hp2)
    apply (square_dvd_iff_order_multiple hn hp hd t ht (k*2) hk2).mpr
    simpa only [hk, mul_assoc] using hex

theorem squarefree_iff_pell_numbers {n : ℕ} (hn : 1 ≤ n) :
    Squarefree ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n) ↔ ∀ p : ℕ, p.Prime → p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n →
      ¬ ((p^2 : ℕ) : ℤ) ∣ ((⟨1,1⟩ : Zsqrtd 2)^(p-1)).im := by
  rw [Nat.squarefree_iff_prime_squarefree]
  constructor
  · intro h p hp hd hB
    exact h p hp (by simpa only [pow_two] using (square_dvd_iff_pell_number hn hp hd).mpr hB)
  · intro h p hp h2
    have hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n := (dvd_mul_right p p).trans h2
    exact h p hp hd ((square_dvd_iff_pell_number hn hp hd).mp (by simpa only [pow_two] using h2))

end Pell292

namespace Pell292


/-- The quotient of the imaginary coefficient by the original imaginary coefficient
reduces to the derivative of the power map at the real coefficient. -/
theorem pell_companion_quotient {p : ℕ} (w : Zsqrtd 2) (hb : (w.im : ZMod p) = 0) (k : ℕ) :
    ((w^k).re : ZMod p) = (w.re : ZMod p)^k ∧
    ∃ c : ℤ, (w^k).im = w.im*c ∧
      (w.re : ZMod p)*(c : ZMod p) = (k : ZMod p)*(w.re : ZMod p)^k := by
  induction k with
  | zero => exact ⟨by simp, 0, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨hr,c,hc,hred⟩ := ih
    have hre : ((w^(k+1)).re : ZMod p) = (w.re : ZMod p)^(k+1) := by
      rw [pow_succ w, Zsqrtd.re_mul]
      push_cast
      rw [hb, hr]
      ring
    refine ⟨hre,(w^k).re+c*w.re,?_,?_⟩
    · rw [pow_succ w, Zsqrtd.im_mul, hc]
      ring
    · push_cast
      rw [hr, pow_succ]
      linear_combination (w.re : ZMod p)*hred

theorem pell_power_coordinates (n : ℕ) :
    let u := (⟨1,1⟩ : Zsqrtd 2)^(2^(n+1))
    u.re = ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n : ℤ) ∧ u.re^2 - 2*u.im^2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    let u := (⟨1,1⟩ : Zsqrtd 2)^(2^(n+1))
    change u.re = ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n : ℤ) ∧ u.re^2-2*u.im^2=1 at ih
    obtain ⟨hX,hN⟩ := ih
    have Es := congrArg (fun z : ℕ => (z : ℤ)) (x_succ_add_one n)
    push_cast at Es
    dsimp only
    rw [pow_succ 2 (n+1), pow_mul]
    change (u^2).re = _ ∧ (u^2).re^2-2*(u^2).im^2=1
    rw [pow_two u, Zsqrtd.re_mul, Zsqrtd.im_mul]
    constructor
    · rw [← hX] at Es
      linear_combination -hN-Es
    · linear_combination (u.re^2-2*u.im^2+1)*hN

/-- The Pell number with index p-1 is X_n times an integer prime to p. -/
theorem pell_number_coprime_quotient {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n) :
    ∃ c : ℤ, ((⟨1,1⟩ : Zsqrtd 2)^(p-1)).im = ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n : ℤ)*c ∧ ¬(p : ℤ) ∣ c := by
  let : Fact p.Prime := ⟨hp⟩
  let α : Zsqrtd 2 := ⟨1,1⟩
  let u := α^(2^(n+1))
  let w := u^2
  obtain ⟨hx,hnorm⟩ := pell_power_coordinates n
  change u.re = ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n : ℤ) at hx
  change u.re^2-2*u.im^2=1 at hnorm
  have hx0 : (u.re : ZMod p)=0 := by rw [hx]; exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hnR := congrArg (fun z : ℤ => (z : ZMod p)) hnorm
  push_cast at hnR
  rw [hx0] at hnR
  have hy : (u.im : ZMod p) ≠ 0 := by
    intro bad
    rw [bad] at hnR
    norm_num at hnR
  have hB : w.im = ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n : ℤ)*(2*u.im) := by
    dsimp only [w]
    rw [pow_two u,Zsqrtd.im_mul, hx]
    ring
  have hB0 : (w.im : ZMod p)=0 := by
    rw [hB, ←hx, Int.cast_mul, hx0, zero_mul]
  have hA : (w.re : ZMod p) = -1 := by
    dsimp only [w]
    rw [pow_two u,Zsqrtd.re_mul]
    push_cast
    rw [hx0]
    linear_combination -hnR
  have hA0 : (w.re : ZMod p) ≠ 0 := by rw [hA]; exact neg_ne_zero.mpr one_ne_zero
  obtain ⟨k,hk,hcop⟩ := exists_order_cofactor hn hp hd
  have hp2 : 2 < p := by
    have hbound := Nat.le_of_dvd (by have := hp.one_lt; omega) (divisor_order_modulus hn hp hd)
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ n+3 by omega)
    change 2^1 ≤ 2^(n+3) at h
    omega
  have twoNZ : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hp2)
  have kNZ : (k : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr hcop
  obtain ⟨_,c,hc,cred⟩ := pell_companion_quotient w hB0 (2*k)
  have cNZ : (c : ZMod p) ≠ 0 := by
    intro bad
    rw [bad, mul_zero, Nat.cast_mul, Nat.cast_ofNat] at cred
    exact (mul_ne_zero (mul_ne_zero twoNZ kNZ) (pow_ne_zero _ hA0)) cred.symm
  refine ⟨(2*u.im)*c,?_,?_⟩
  · have hex : p-1 = (2^(n+1)*2)*(2*k) := by
      rw [hk, show n+3=(n+1)+2 by omega, pow_add]
      ring
    rw [hex, pow_mul α (2^(n+1)*2) (2*k), pow_mul α (2^(n+1)) 2]
    change (w^(2*k)).im = _
    rw [hc,hB]
    ring
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact mul_ne_zero (mul_ne_zero twoNZ hy) cNZ

/-- The same prime powers divide X_n and the (p-1)-st Pell number. -/
theorem prime_power_dvd_iff_pell_number {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n) (e : ℕ) :
    p^e ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n ↔ ((p^e : ℕ) : ℤ) ∣ ((⟨1,1⟩ : Zsqrtd 2)^(p-1)).im := by
  obtain ⟨c,hc,hcop⟩ := pell_number_coprime_quotient hn hp hd
  have primeZ : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have cop := (primeZ.irreducible.coprime_pow_of_not_dvd e hcop).symm
  rw [← Int.natCast_dvd_natCast, Nat.cast_pow, hc]
  exact ⟨fun h => h.trans (dvd_mul_right _ _), cop.dvd_of_dvd_mul_right⟩

theorem padic_valuation_pell_number {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n) :
    padicValInt p (((⟨1,1⟩ : Zsqrtd 2)^(p-1)).im) = padicValNat p ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨c,hc,hcop⟩ := pell_number_coprime_quotient hn hp hd
  have hX : ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n : ℤ) ≠ 0 := by
    exact_mod_cast (show (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n ≠ 0 by have := x_ge n; omega)
  have hc0 : c ≠ 0 := by rintro rfl; exact hcop (dvd_zero _)
  rw [hc, padicValInt.mul hX hc0, padicValInt.eq_zero_of_not_dvd hcop, add_zero,
    padicValInt.of_nat]

end Pell292

namespace Pell292


/-- A Pocklington certificate with a known factor of every divisor's
multiplicative-group order. The witness need only certify the coprime complement. -/
theorem lucas_with_known_factor {F K N : ℕ} (hF : 0 < F) (hN : 1 < N)
    (hdiv : F ∣ N-1) (cop : K.Coprime F) (size : N < (K*F+1)^2)
    (known : ∀ r : ℕ, r.Prime → r ∣ N → K ∣ r-1) :
    N.Prime ↔ ∃ b : ZMod N, b ^ F = 1 ∧
      ∀ q : ℕ, q.Prime → q ∣ F → IsUnit (b ^ (F / q) - 1) := by
  constructor
  · intro hp
    let : Fact N.Prime := ⟨hp⟩
    obtain ⟨a, ha, hd⟩ := reverse_lucas_primality N hp
    have horder : orderOf a = N - 1 :=
      orderOf_eq_of_pow_and_pow_div_prime (by omega) ha hd
    have hb : orderOf (a ^ (orderOf a / F)) = F :=
      orderOf_pow_orderOf_div (by rw [horder]; omega) (horder ▸ hdiv)
    obtain ⟨hb1, hb2⟩ := (orderOf_eq_iff hF).mp hb
    refine ⟨_, hb1, fun q hq hqd => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ?_)⟩
    exact hb2 _ (Nat.div_lt_self hF hq.one_lt)
      (Nat.div_pos (Nat.le_of_dvd hF hqd) hq.pos)
  · rintro ⟨b, hb, hunit⟩
    by_contra hn
    let r := N.minFac
    have hr : r.Prime := Nat.minFac_prime (by omega : N ≠ 1)
    let : Fact r.Prime := ⟨hr⟩
    let f : ZMod N →+* ZMod r := ZMod.castHom (Nat.minFac_dvd N) (ZMod r)
    have hpow : f b ^ F = 1 := by rw [← map_pow, hb, map_one]
    have htest (q : ℕ) (hq : q.Prime) (hqd : q ∣ F) : f b ^ (F/q) ≠ 1 := by
      have hu := (hunit q hq hqd).map f
      simp only [map_sub, map_pow, map_one] at hu
      exact sub_ne_zero.mp hu.ne_zero
    have horder := orderOf_eq_of_pow_and_pow_div_prime hF hpow htest
    have hz : f b ≠ 0 := by
      rintro hh
      rw [hh, zero_pow (by omega : F ≠ 0)] at hpow
      exact zero_ne_one hpow
    have hd := ZMod.orderOf_dvd_card_sub_one hz
    rw [horder] at hd
    have hle : K*F ≤ r - 1 := Nat.le_of_dvd (by have := hr.two_le; omega)
      (cop.mul_dvd_of_dvd_of_dvd (known r hr (Nat.minFac_dvd N)) hd)
    have hs : r^2 ≤ N := Nat.minFac_sq_le_self (by omega) hn
    have hkr : K*F + 1 ≤ r := by have := hr.two_le; omega
    exact (Nat.not_lt_of_ge ((Nat.pow_le_pow_left hkr 2).trans hs)) size

/-- A single unit of square-root order at every prime divisor certifies primality. -/
theorem square_lucas_iff {D N : ℕ} (hD : 0 < D) (eqN : N = D^2 + 1) :
    N.Prime ↔ ∃ b : ZMod N, b ^ D = 1 ∧
      ∀ q : ℕ, q.Prime → q ∣ D → IsUnit (b ^ (D / q) - 1) := by
  apply lucas_with_known_factor (K:=1) hD (by nlinarith) _ (by simp)
      (by rw [one_mul]; nlinarith) (fun _ _ _ => one_dvd _)
  rw [eqN, Nat.add_sub_cancel, pow_two]
  exact dvd_mul_right _ _

/-- The Lucas tests for (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1))(n+1) require only 2 and the prime factors of
(Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1))(0), ..., (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1))(n-1), and use exponents at most sqrt((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1))(n+1)-1). -/
theorem pell_lucas_iff (n : ℕ) :
    let D := 2^(n+2) * ∏ i ∈ Finset.range n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i
    ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)).Prime ↔ ∃ b : ZMod ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)), b^D = 1 ∧
      ∀ q : ℕ, q.Prime → (q = 2 ∨ ∃ i < n, q ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i) →
        IsUnit (b^(D/q) - 1) := by
  dsimp only
  let D := 2^(n+2) * ∏ i ∈ Finset.range n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i
  have posProd : 0 < ∏ i ∈ Finset.range n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i := Finset.prod_pos fun i _ =>
    lt_of_lt_of_le (by decide : 0 < 3) (x_ge i)
  have pos : 0 < D := Nat.mul_pos (by positivity) posProd
  have ds (q : ℕ) (hq : q.Prime) : q ∣ D ↔ q = 2 ∨ ∃ i < n, q ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i := by
    change q ∣ 2^(n+2) * ∏ i ∈ Finset.range n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i ↔ _
    rw [hq.dvd_mul, hq.prime.dvd_finsetProd_iff]
    constructor
    · rintro (h | ⟨i,hi,hd⟩)
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
      · exact Or.inr ⟨i, Finset.mem_range.mp hi, hd⟩
    · rintro (rfl | ⟨i,hi,hd⟩)
      · exact Or.inl (dvd_pow_self _ (by omega))
      · exact Or.inr ⟨i, Finset.mem_range.mpr hi, hd⟩
  rw [square_lucas_iff pos (x_square_formula n)]
  exact exists_congr fun b => and_congr_right fun _ =>
    forall_congr' fun q => forall_congr' fun hq => imp_congr_left (ds q hq)

/-- The divisors of (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1))(n+2) have enough two-adic order to skip both 2 and
(Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1))(0)=3. Only the prime factors of (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1))(1), ..., (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1))(n) are tested. -/
theorem pell_odd_lucas_iff (n : ℕ) :
    let F := ∏ i ∈ Finset.range n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (i+1)
    ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2)).Prime ↔ ∃ b : ZMod ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2)), b^F = 1 ∧
      ∀ q : ℕ, q.Prime → (∃ i < n, q ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (i+1)) → IsUnit (b^(F/q)-1) := by
  let F := ∏ i ∈ Finset.range n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (i+1)
  let K := 2^(n+5)
  have hF : 0 < F := Finset.prod_pos fun i _ =>
    lt_of_lt_of_le (by decide : 0 < 3) (x_ge (i+1))
  have eqN : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2) = (2^(n+3) * (F*3))^2+1 := by
    rw [x_square_formula (n+1), Finset.prod_range_succ' (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1))]
    rfl
  have hd : F ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2)-1 := by
    rw [eqN, Nat.add_sub_cancel]
    exact dvd_pow ((dvd_mul_right F 3).trans (dvd_mul_left _ _)) (by decide)
  have hcop : K.Coprime F := by
    apply Nat.Coprime.pow_left
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    change ¬ 2 ∣ ∏ i ∈ Finset.range n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (i+1)
    rw [Nat.prime_two.prime.dvd_finsetProd_iff]
    rintro ⟨i,_,hi⟩
    have := x_succ_add_one i
    omega
  have size : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2) < (K*F+1)^2 := by
    change (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2) < (2^(n+5)*F+1)^2
    rw [eqN, show n+5=(n+3)+2 by omega, pow_add (2:ℕ) (n+3) 2]
    have he : 0 < 2^(n+3)*F := Nat.mul_pos (by positivity) hF
    nlinarith
  have kw (r : ℕ) (hr : r.Prime) (hrd : r ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2)) : K ∣ r-1 :=
    divisor_order_modulus (by omega : 1 ≤ n+2) hr hrd
  dsimp only
  rw [lucas_with_known_factor hF (lt_of_lt_of_le (by decide : 1 < 3) (x_ge (n+2))) hd hcop size kw]
  refine exists_congr fun b => and_congr_right fun _ =>
    forall_congr' fun q => forall_congr' fun hq => imp_congr_left ?_
  change q ∣ ∏ i ∈ Finset.range n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (i+1) ↔ _
  simp only [hq.prime.dvd_finsetProd_iff, Finset.mem_range]

end Pell292

namespace Pell292

/-- An Euler pass supplies enough two-power order to omit any prefix of product at most
2^(n+2). The order witness needs the prime factors of the remaining suffix only. -/
theorem pell_adaptive_lucas_iff (n t : ℕ) (ht : t ≤ n)
    (hprefix : ∏ i ∈ Finset.range t, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i ≤ 2^(n+2)) :
    let F := ∏ i ∈ Finset.Ico t n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i
    ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)).Prime ↔ (5 : ZMod ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)))^((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)/2) = -1 ∧
      ∃ b : ZMod ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)), b^F = 1 ∧ ∀ q : ℕ, q.Prime →
        (∃ i ∈ Finset.Ico t n, q ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i) → IsUnit (b^(F/q)-1) := by
  let P := ∏ i ∈ Finset.range t, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i
  let F := ∏ i ∈ Finset.Ico t n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i
  have hF : 0 < F := Finset.prod_pos fun i _ => lt_of_lt_of_le (by decide : 0<3) (x_ge i)
  have hPF : P*F = ∏ i ∈ Finset.range n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i := Finset.prod_range_mul_prod_Ico (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) ht
  have eqN : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1) = ((2^(n+2)*P)*F)^2 + 1 := by
    rw [mul_assoc, hPF]
    exact x_square_formula n
  have hd : F ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)-1 := by
    rw [eqN, Nat.add_sub_cancel]
    exact dvd_pow (dvd_mul_left _ _) (by decide)
  have hcop : (2^(2*(n+2))).Coprime F := by
    apply Nat.Coprime.pow_left
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    change ¬ 2 ∣ ∏ i ∈ Finset.Ico t n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i
    rw [Nat.prime_two.prime.dvd_finsetProd_iff]
    rintro ⟨i,_,hi⟩
    cases i with
    | zero => exact (by decide : ¬ 2 ∣ 3) hi
    | succ i => have := x_succ_add_one i; omega
  have size : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1) < (2^(2*(n+2))*F+1)^2 := by
    rw [eqN, mul_comm 2 (n+2), pow_mul, pow_two (2^(n+2):ℕ)]
    have hle : (2^(n+2)*P)*F ≤ (2^(n+2)*2^(n+2))*F :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hprefix)
    have hpos : 0 < (2^(n+2)*2^(n+2))*F := Nat.mul_pos (by positivity) hF
    have hsq := Nat.pow_le_pow_left hle 2
    nlinarith
  have hN := lt_of_lt_of_le (by decide : 1<3) (x_ge (n+1))
  have aux (pass : (5 : ZMod ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)))^((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)/2) = -1) :
      ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)).Prime ↔ ∃ b : ZMod ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)), b^F = 1 ∧
        ∀ q : ℕ, q.Prime → (∃ i ∈ Finset.Ico t n, q ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i) → IsUnit (b^(F/q)-1) := by
    rw [lucas_with_known_factor hF hN hd hcop size (fun r hr hrd => euler_divisor_modulus n hr hrd pass)]
    refine exists_congr fun b => and_congr_right fun _ =>
      forall_congr' fun q => forall_congr' fun hq => imp_congr_left ?_
    exact hq.prime.dvd_finsetProd_iff (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1))
  constructor
  · intro hp
    have pass := euler_five_of_prime n hp
    exact ⟨pass, (aux pass).mp hp⟩
  · rintro ⟨pass, hb⟩
    exact (aux pass).mpr hb

end Pell292

namespace Pell292

/-- If F² divides N−1, every composite N whose prime divisors are 1 mod F is
at least F³+1. The least prime divisor and its cofactor are 1+Fu and 1+Fv,
and square divisibility forces F to divide the positive sum u+v. -/
theorem prime_of_cube_order {N F : ℕ} (hN : 1 < N) (hF : 0 < F)
    (hd : F^2 ∣ N-1) (sz : N ≤ F^3)
    (known : ∀ r : ℕ, r.Prime → r ∣ N → F ∣ r-1) : N.Prime := by
  by_contra hn
  let p := N.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpf : p ∣ N := Nat.minFac_dvd N
  obtain ⟨t,ht⟩ := hpf
  have hp2 := hp.two_le
  have ht2 : 1 < t := by
    by_contra!
    interval_cases t <;> simp_all
  have hpd := known p hp ⟨t,ht⟩
  have hmN : 1 ≡ N [MOD F] := (Nat.modEq_iff_dvd' (by omega)).mpr
    ((dvd_pow_self F (by decide : 2 ≠ 0)).trans hd)
  have hmp : 1 ≡ p [MOD F] := (Nat.modEq_iff_dvd' (by omega)).mpr hpd
  have hmt : t ≡ N [MOD F] := by simpa only [one_mul,←ht] using hmp.mul_right t
  obtain ⟨v,hv⟩ := (Nat.modEq_iff_dvd' (by omega)).mp (hmN.trans hmt.symm)
  obtain ⟨u,hu⟩ := hpd
  obtain ⟨c,hc⟩ := hd
  have pp : p = F*u+1 := by omega
  have tt : t = F*v+1 := by omega
  have nn : N = F^2*c+1 := by omega
  have hpt : N = (F*u+1)*(F*v+1) := by rw [ht,pp,tt]
  have hh : F*(F*c) = F*(F*u*v+(u+v)) := by nlinarith only [nn,hpt]
  have hh' := Nat.eq_of_mul_eq_mul_left hF hh
  have hsum : F ∣ u+v := by
    apply (Nat.dvd_add_right ((dvd_mul_right F u).trans (dvd_mul_right _ v))).mp
    rw [←hh']
    exact dvd_mul_right _ _
  have up : 0 < u := by by_contra! hz; simp_all
  have vp : 0 < v := by by_contra! hz; simp_all
  have le : F ≤ u+v := Nat.le_of_dvd (by omega) hsum
  have uv : u+v ≤ u*v+1 := by
    obtain ⟨u',rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
    obtain ⟨v',rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : v ≠ 0)
    nlinarith
  have low := Nat.mul_le_mul_left (F^2) (le.trans uv)
  have low' := Nat.mul_le_mul_left F le
  nlinarith only [low, low', hpt, sz]

/-- The square-divisibility cube-root variant of Lucas' order test. -/
theorem cube_lucas_iff {N F : ℕ} (hN : 1 < N) (hF : 0 < F)
    (hd : F^2 ∣ N-1) (sz : N ≤ F^3) :
    N.Prime ↔ ∃ b : ZMod N, b^F=1 ∧ ∀ q : ℕ, q.Prime → q∣F →
        IsUnit (b^(F/q)-1) := by
  constructor
  · intro hp
    let : Fact N.Prime := ⟨hp⟩
    obtain ⟨a, ha, ht⟩ := reverse_lucas_primality N hp
    have ho : orderOf a = N-1 := orderOf_eq_of_pow_and_pow_div_prime (by omega) ha ht
    have hf : F ∣ orderOf a := ho ▸ (dvd_pow_self F (by decide : 2≠0)).trans hd
    have hw := orderOf_pow_orderOf_div (show orderOf a ≠ 0 by rw [ho]; omega) hf
    obtain ⟨h1,h2⟩ := (orderOf_eq_iff hF).mp hw
    refine ⟨_, h1, fun q hq hqf => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ?_)⟩
    exact h2 _ (Nat.div_lt_self hF hq.one_lt) (Nat.div_pos (Nat.le_of_dvd hF hqf) hq.pos)
  · rintro ⟨b,hb,hu⟩
    apply prime_of_cube_order hN hF hd sz
    intro r hr hrN
    let : Fact r.Prime := ⟨hr⟩
    let f : ZMod N →+* ZMod r := ZMod.castHom hrN (ZMod r)
    have hpow : f b ^ F = 1 := by rw [← map_pow, hb, map_one]
    have htest (q : ℕ) (hq : q.Prime) (hqd : q ∣ F) : f b ^ (F/q) ≠ 1 := by
      have ok := (hu q hq hqd).map f
      simp only [map_sub, map_pow, map_one] at ok
      exact sub_ne_zero.mp ok.ne_zero
    have horder := orderOf_eq_of_pow_and_pow_div_prime hF hpow htest
    have hz : f b ≠ 0 := by
      rintro hh
      rw [hh, zero_pow (by omega : F ≠ 0)] at hpow
      exact zero_ne_one hpow
    simpa only [horder] using ZMod.orderOf_dvd_card_sub_one hz

/-- For any k≥4, checking primes dividing (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1))(k−2) or (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1))(k−3) suffices. -/
theorem pell_two_lucas_iff (n : ℕ) (hn : 1 ≤ n) :
    let F := (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n * (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)
    ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+3)).Prime ↔ ∃ b : ZMod ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+3)), b^F = 1 ∧
      ∀ q : ℕ, q.Prime → (q ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n ∨ q ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)) → IsUnit (b^(F/q)-1) := by
  let F := (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n * (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1)
  have hF : 0 < F := Nat.mul_pos (by have := x_ge n; omega) (by have := x_ge (n+1); omega)
  have hd : F^2 ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+3)-1 := by
    rw [x_square_formula (n+2), Nat.add_sub_cancel]
    apply pow_dvd_pow_of_dvd _ 2
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    refine ⟨2^(n+2+2) * ∏ i ∈ Finset.range n, (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i, ?_⟩
    dsimp [F]
    ring
  have hN : 1 < (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+3) := by have := x_ge (n+3); omega
  have a : 16 ≤ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n := by
    have h := x_strict.monotone hn
    exact le_trans (by decide : 16 ≤ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) 1) h
  have b := x_succ_add_one n
  have c := x_succ_add_one (n+1)
  have d := x_succ_add_one (n+2)
  have h8 : 8*(Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1) ≤ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n)^3 := by
    have h := Nat.mul_le_mul_right (((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n)^2) a
    nlinarith only [b,h]
  have hsq : ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2))^2 ≤ (2*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1))^2)^2 :=
    Nat.pow_le_pow_left ((Nat.le_succ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2))).trans_eq c) 2
  have sz : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+3) ≤ F^3 := by
    have h := Nat.mul_le_mul_right (((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1))^3) h8
    dsimp [F]
    nlinarith only [hsq,d,h]
  dsimp only
  rw [cube_lucas_iff hN hF hd sz]
  exact exists_congr fun b => and_congr_right fun _ =>
    forall_congr' fun q => forall_congr' fun hq => imp_congr_left hq.dvd_mul

end Pell292

namespace Pell292


set_option maxRecDepth 4096 in
theorem first_four_prime (n : ℕ) (hn : n < 4) : ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n).Prime := by
  interval_cases n
  · change Nat.Prime 3; norm_num
  · change Nat.Prime 17; norm_num
  · change Nat.Prime 577; norm_num
  · change Nat.Prime 665857; norm_num

/-- Reduce at every iteration, also when the previous residue is zero. -/
theorem x_mod_recurrence (n d : ℕ) :
    ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n : ℤ) % d = Nat.rec (3 % (d : ℤ))
      (fun _ r => (2*r^2-1) % (d : ℤ)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := x_succ_add_one n
    have e : ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+1) : ℤ) = 2*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n : ℤ)^2-1 := by
      exact eq_sub_of_add_eq (by exact_mod_cast h)
    rw [e]
    change _ = (2*(_ : ℤ)^2-1) % d
    rw [← ih]
    have he : ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n : ℤ) ≡ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n : ℤ) % d [ZMOD d] := (Int.mod_modEq _ _).symm
    exact ((Int.ModEq.refl 2).mul (he.pow 2) |>.sub (Int.ModEq.refl 1))

/-- The modulus need not itself be prime. Its size is checked by a short power bound. -/
theorem not_prime_of_mod_certificate (n d e : ℕ) (hd : 1 < d)
    (hs : d < 3^e) (he : e ≤ 2^n)
    (h : (Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ)) (fun _ r => (2*r^2-1) % (d : ℤ)) n) = 0) :
    ¬ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n).Prime := by
  have hi : (d : ℤ) ∣ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n : ℤ) :=
    Int.dvd_of_emod_eq_zero ((x_mod_recurrence n d).trans h)
  have hn : d ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n := by exact_mod_cast hi
  have hlt : d < (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n := hs.trans_le ((Nat.pow_le_pow_right (by decide) he).trans (x_growth n))
  intro hp
  exact ((Nat.dvd_prime hp).mp hn).elim (by omega) (by omega)

/- Entries 4 through 8 use the factorizations recorded by hardmath and Ken
    (math.stackexchange.com/q/3176065, kenta.blogspot.com/2020/08/ywpmmgro-factoring-numerators-of-sqrt-2.html).
    FactorDB supplied divisors of entries 11, 12 and 16 (records 1100000000416750355,
    1100000000422816452 and 1100000000841194592). The other witnesses were found by
    testing moduli in the progressions 1 + k * 2^(n+3). Every witness is checked below. -/
set_option maxRecDepth 32000 in
set_option maxHeartbeats 8000000 in
theorem not_prime_at_certified_indices {n : ℕ}
    (hn : n ∈ [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 22, 24, 26, 32, 33, 42, 44, 52, 63, 71, 72, 101, 123, 125, 140, 174, 184, 186, 205, 264, 268, 272, 313, 328, 363, 394, 410, 441, 472, 473, 482, 499, 598, 611, 852, 862, 872] ) : ¬ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n).Prime := by
  let table : List (ℕ × ℕ) := [
    (4, 257),
    (5, 11777),
    (6, 7681),
    (7, 7460967982148609),
    (8, 79873),
    (9, 12289),
    (10, 65537),
    (11, 596595073965490177),
    (12, 2057988243457),
    (13, 1819410433),
    (14, 6684673),
    (16, 213470634367254529),
    (17, 383778817),
    (18, 11700011009),
    (19, 912718299137),
    (22, 167772161),
    (24, 14676574339073),
    (26, 3221225473),
    (32, 4123168604161),
    (33, 62259845922817),
    (42, 10520127254560769),
    (44, 3799912185593857),
    (52, 180143985094819841),
    (63, 3*2^66+1),
    (71, 3433*2^74+1),
    (72, 29*2^75+1),
    (101, 1413*2^104+1),
    (123, 11*2^127+1),
    (125, 21*2^129+1),
    (140, 1499*2^149+1),
    (174, 1613*2^177+1),
    (184, 13*2^188+1),
    (186, 99*2^189+1),
    (205, 11*2^209+1),
    (264, 25*2^268+1),
    (268, 145*2^276+1),
    (272, 27*2^275+1),
    (313, 13*2^316+1),
    (328, 125*2^331+1),
    (363, 19*2^366+1),
    (394, 21*2^397+1),
    (410, 105*2^413+1),
    (441, 25*2^448+1),
    (472, 191*2^475+1),
    (473, 123*2^476+1),
    (482, 53*2^485+1),
    (499, 57*2^502+1),
    (598, 245*2^601+1),
    (611, 7*2^616+1),
    (852, 53*2^857+1),
    (862, 39*2^865+1),
    (872, 137*2^875+1)]
  have covered : n ∈ table.map Prod.fst := hn
  obtain ⟨⟨_, d⟩, mem, rfl⟩ := List.mem_map.mp covered
  have checks : table.all (fun p => decide (1 < p.2 ∧
      p.2 < 3^(p.2.log2+1) ∧ p.2.log2+1 ≤ 2^p.1 ∧
      Nat.rec (motive := fun _ => ℤ) (3 % (p.2 : ℤ))
        (fun _ r => (2*r^2-1) % (p.2 : ℤ)) p.1 = 0)) := by decide +kernel
  obtain ⟨a,b,c,e⟩ := of_decide_eq_true (List.all_eq_true.mp checks _ mem)
  exact not_prime_of_mod_certificate _ d _ a b c e

end Pell292

namespace Pell292

set_option maxRecDepth 32000 in
set_option maxHeartbeats 8000000 in
theorem not_prime_at_high_indices {n : ℕ}
    (hn : n ∈ [1437, 1489, 1944, 2035] ) : ¬ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n).Prime := by
  let table : List (ℕ × ℕ) := [
    (1437, 63*2^1441+1),
    (1489, 9*2^1494+1),
    (1944, 5*2^1947+1),
    (2035, 19*2^2038+1)]
  have covered : n ∈ table.map Prod.fst := hn
  obtain ⟨⟨_, d⟩, mem, rfl⟩ := List.mem_map.mp covered
  have checks : table.all (fun p => decide (1 < p.2 ∧
      p.2 < 3^(p.2.log2+1) ∧ p.2.log2+1 ≤ 2^p.1 ∧
      Nat.rec (motive := fun _ => ℤ) (3 % (p.2 : ℤ))
        (fun _ r => (2*r^2-1) % (p.2 : ℤ)) p.1 = 0)) := by decide +kernel
  obtain ⟨a,b,c,e⟩ := of_decide_eq_true (List.all_eq_true.mp checks _ mem)
  exact not_prime_of_mod_certificate _ d _ a b c e

end Pell292

namespace Pell292

theorem x_ge_square_iterate (i j : ℕ) : ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i)^(2^j) ≤ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (i+j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ (2:ℕ), pow_mul]
    have e := x_succ_add_one (i+j)
    have h := x_ge (i+j)
    exact (Nat.pow_le_pow_left ih 2).trans (by change ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (i+j))^2 ≤ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) ((i+j)+1); nlinarith)

theorem x15_bound : 10^25000 < (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) 15 := by decide +kernel

theorem x20_bound : 10^800000 < (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) 20 := by
  rw [← (show 25000*(2:ℕ)^5 = 800000 by decide), pow_mul]
  exact (Nat.pow_lt_pow_left x15_bound (by decide : 2^5 ≠ 0)).trans_le (x_ge_square_iterate 15 5)

theorem classified_below {L p k : ℕ}
    (range : ∀ n : ℕ, 4 ≤ n → n < L → ¬((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n).Prime)
    (hp : p.Prime) (e : p^2-1=2*k^2) (small : p < (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) L) :
    p=3 ∨ p=17 ∨ p=577 ∨ p=665857 := by
  obtain ⟨n,rfl⟩ := OMA.R_oeis_a292082_R1.classify p hp k e
  have lo := x_strict.lt_iff_lt.mp small
  by_cases h : 4 ≤ n
  · exact (range n h lo hp).elim
  · have h' : n ≤ 3 := by omega
    interval_cases n <;> decide

theorem original_below_25000 {p k : ℕ} (hp : p.Prime) (e : p^2-1=2*k^2)
    (small : p ≤ 10^25000) : p=3 ∨ p=17 ∨ p=577 ∨ p=665857 := by
  apply classified_below (L:=15) _ hp e (small.trans_lt x15_bound)
  intro n hn hN
  apply not_prime_at_certified_indices
  interval_cases n <;> decide

/-- Through the larger bound the single residual candidate is (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1))(15). -/
theorem candidate_through_800000 {p k : ℕ} (hp : p.Prime) (e : p^2-1=2*k^2)
    (small : p ≤ 10^800000) : p=3 ∨ p=17 ∨ p=577 ∨ p=665857 ∨ p=(Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) 15 := by
  obtain ⟨n,rfl⟩ := OMA.R_oeis_a292082_R1.classify p hp k e
  have lx : (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n < (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) 20 := small.trans_lt x20_bound
  have lo : n < 20 := x_strict.lt_iff_lt.mp lx
  by_cases h15 : n=15
  · exact Or.inr (Or.inr (Or.inr (Or.inr (congrArg (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) h15))))
  by_cases h : 4 ≤ n
  · exfalso
    apply not_prime_at_certified_indices _ hp
    interval_cases n <;> first | decide | omega
  · have h' : n ≤ 3 := by omega
    interval_cases n <;> decide

end Pell292

namespace Pell292

theorem num_prime_factors (n : ℕ) : ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n).primeFactors.card ≤ 3*2^n := by
  have upper : 2*((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n) ≤ 2^(3*2^n) := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [pow_succ (2:ℕ) n, ← Nat.mul_assoc, pow_mul]
      have h := Nat.pow_le_pow_left ih 2
      have e := x_succ_add_one n
      nlinarith
  have pr := Finset.prod_le_prod' (s := ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n).primeFactors) (f:=fun _ => (2:ℕ)) (g:=id)
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  simp only [Finset.prod_const, id_eq] at pr
  have h1 := Nat.le_of_dvd (show 0 < (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n by have := x_ge n; omega) (Nat.prod_primeFactors_dvd ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n))
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (pr.trans (h1.trans (by omega)))

/-- Split the prime factors by the quotient (p−1)/M, with M=2^(n+3).
There is at most one prime at each quotient. -/
theorem reciprocal_bound (n T : ℕ) (hn : 1 ≤ n) (hT : 0 < T) :
    (∑ p ∈ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n).primeFactors, (1:ℝ)/p) ≤
    T/(2:ℝ)^(n+3)+(3*(2:ℝ)^n)/((2:ℝ)^(n+3)*T) := by
  classical
  let M := 2^(n+3)
  let S := ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n).primeFactors
  let A := S.filter (fun p => p ≤ M*T)
  let B := S.filter (fun p => ¬p ≤ M*T)
  have hm : 0 < M := by dsimp [M]; positivity
  have form : ∀ p ∈ S, ∃ k, p = 1+M*k := by
    intro p hp
    have h := divisor_order_modulus hn (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
    obtain ⟨k,hk⟩ := h
    exact ⟨k, by have := (Nat.prime_of_mem_primeFactors hp).two_le; dsimp [M]; omega⟩
  have hcard : A.card ≤ T := by
    have cover : A ⊆ (Finset.Icc 1 T).image (fun k => 1+M*k) := by
      intro p hp
      obtain ⟨hS,le⟩ := Finset.mem_filter.mp hp
      obtain ⟨k,rfl⟩ := form p hS
      have hp' := (Nat.prime_of_mem_primeFactors hS).two_le
      have cut : k ≤ T := Nat.le_of_mul_le_mul_left (show M*k ≤ M*T by omega) hm
      exact Finset.mem_image.mpr ⟨k,Finset.mem_Icc.mpr ⟨by by_contra! h; interval_cases k; simp at hp',cut⟩,rfl⟩
    simpa using (Finset.card_le_card cover).trans Finset.card_image_le
  have hA : (∑ p ∈ A, (1:ℝ)/p) ≤ A.card * ((1:ℝ)/M) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨k,e⟩ := form p (Finset.mem_filter.mp hp).1
    have hp' := (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
    have hk : 1 ≤ k := by by_contra! h; interval_cases k; simp at e; omega
    apply one_div_le_one_div_of_le (by exact_mod_cast hm)
    exact_mod_cast (show M ≤ p by nlinarith [Nat.mul_le_mul_left M hk])
  have hB : (∑ p ∈ B, (1:ℝ)/p) ≤ B.card * ((1:ℝ)/(M*T:ℕ)) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    apply one_div_le_one_div_of_le (by exact_mod_cast (Nat.mul_pos hm hT))
    exact_mod_cast (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hp).2))
  have hbcard : B.card ≤ 3*2^n := (Finset.card_le_card (Finset.filter_subset _ _)).trans (num_prime_factors n)
  have part : (∑ p ∈ A, (1:ℝ)/p) + (∑ p ∈ B, (1:ℝ)/p) = _ :=
    Finset.sum_filter_add_sum_filter_not S _ _
  rw [←part]
  have a : (A.card:ℝ) ≤ T := by exact_mod_cast hcard
  have b : (B.card:ℝ) ≤ 3*2^n := by exact_mod_cast hbcard
  have g := add_le_add (hA.trans (mul_le_mul_of_nonneg_right a (by positivity)))
    (hB.trans (mul_le_mul_of_nonneg_right b (by positivity)))
  simpa [M, div_eq_mul_inv] using g

/-- In particular the series of reciprocals of all prime divisors of the entire
sequence converges. Multiplicative order gives the spacing within each row. -/
theorem sum_reciprocal_rows :
    Summable (fun n : ℕ => ∑ p ∈ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n).primeFactors, (1:ℝ)/p) := by
  let f := fun n : ℕ => ∑ p ∈ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n).primeFactors, (1:ℝ)/p
  change Summable f
  apply (summable_nat_add_iff 1).mp
  apply Summable.even_add_odd
  all_goals
    refine Summable.of_nonneg_of_le (f:=fun k : ℕ => (1/2:ℝ)^k) (fun _ => by dsimp [f]; positivity) ?_ summable_geometric_two
    intro k
  · have h := reciprocal_bound (2*k+1) (2^k) (by omega) (by positivity)
    apply h.trans
    push_cast
    rw [show 2*k+1+3=k*2+4 by omega, show 2*k+1=k*2+1 by omega,
      pow_add (2:ℝ) (k*2) 4, pow_succ (2:ℝ) (k*2), pow_mul (2:ℝ) k 2]
    rw [div_pow, one_pow]
    field_simp
    nlinarith [sq_nonneg ((2:ℝ)^k)]
  · have h := reciprocal_bound (2*k+1+1) (2^k) (by omega) (by positivity)
    apply h.trans
    push_cast
    rw [show 2*k+1+1+3=k*2+5 by omega, show 2*k+1+1=k*2+2 by omega,
      pow_add (2:ℝ) (k*2) 5, pow_add (2:ℝ) (k*2) 2, pow_mul (2:ℝ) k 2]
    rw [div_pow, one_pow]
    field_simp
    nlinarith [sq_nonneg ((2:ℝ)^k)]

set_option maxHeartbeats 1000000 in
theorem summable_sequence_prime_reciprocals :
    Summable (fun p : {p : ℕ // p.Prime ∧ ∃ n : ℕ, p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n} => (1:ℝ)/p.val) := by
  classical
  let J := (Σ n : ℕ, {p // p ∈ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n).primeFactors})
  let f : J → ℝ := fun u => 1/u.2.val
  have hall : Summable f := by
    apply (summable_sigma_of_nonneg (fun _ => by dsimp [f]; positivity)).mpr
    constructor
    · exact fun n => Summable.of_finite
    · apply sum_reciprocal_rows.congr
      intro n
      rw [tsum_fintype]
      exact (Finset.sum_coe_sort (s:=((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n).primeFactors) (f:=fun p : ℕ => (1:ℝ)/p)).symm
  let g (p : {p : ℕ // p.Prime ∧ ∃ n : ℕ, p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n}) : J :=
    ⟨p.prop.2.choose,p.val,Nat.mem_primeFactors.mpr ⟨p.prop.1,p.prop.2.choose_spec,
      by have := x_ge p.prop.2.choose; omega⟩⟩
  have gi : Function.Injective g := by
    intro p q eq
    exact Subtype.ext (congrArg (fun j : J => j.2.val) eq)
  change Summable (f ∘ g)
  exact hall.comp_injective gi

end Pell292

namespace Pell292



/- A blocked scan of the integers from one through m. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_grid_sound (F G : ℕ → Bool) (j m : ℕ) (hlo : 1 ≤ j) (hhi : j ≤ m)
    (found : F j = true) (check : (List.range (m/4096+1)).all (fun b =>
      ((List.range' (4096*b+1) (min 4096 (m-4096*b))).filter F).all G) = true) :
    G j = true := by
  let b := (j-1)/4096
  have mem : b ∈ List.range (m/4096+1) := by rw [List.mem_range]; dsimp [b]; omega
  have here := List.all_eq_true.mp check b mem
  apply List.all_eq_true.mp here
  apply List.mem_filter.mpr
  refine ⟨List.mem_range'_1.mpr ⟨?_,?_⟩, found⟩ <;> dsimp [b] <;> omega


set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_1 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_2 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_3 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_4 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_5 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_6 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_7 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_8 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_9 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_10 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_11 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_12 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_13 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_14 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_15 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_16 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_17 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 17 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_18 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 18 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_19 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 19 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_20 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 20 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_21 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 21 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_22 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 22 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_23 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 23 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_24 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 24 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_25 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 25 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_26 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 26 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_27 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 27 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_28 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 28 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_29 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 29 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_30 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 30 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_31 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 31 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_32 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 32 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_33 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 33 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_34 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 34 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_35 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 35 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_36 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 36 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_37 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 37 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_38 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 38 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_39 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 39 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_40 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 40 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_41 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 41 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_42 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 42 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_43 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 43 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_44 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 44 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_45 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 45 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_46 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 46 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_47 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 47 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_48 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 48 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_49 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 49 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_50 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 50 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_51 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 51 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_52 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 52 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_53 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 53 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_54 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 54 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_55 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 55 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_56 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 56 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_57 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 57 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_58 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 58 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_59 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 59 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_60 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 60 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_61 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 61 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_62 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 62 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_63 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 63 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_64 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 64 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_65 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 65 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_66 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 66 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_67 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 67 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_68 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 68 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_69 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 69 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_70 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 70 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_71 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 71 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_72 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 72 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_73 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 73 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_74 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 74 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_75 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 75 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_76 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 76 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_77 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 77 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_78 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 78 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_79 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 79 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_80 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 80 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_81 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 81 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_82 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 82 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_83 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 83 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_84 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 84 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_85 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 85 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_86 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 86 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_87 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 87 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_88 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 88 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_89 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 89 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_90 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 90 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_91 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 91 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_92 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 92 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_93 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 93 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_94 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 94 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_5_95 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 95 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_5 (b : ℕ) (hb : b < 96) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 5 b = true := by
  interval_cases b
  · exact catalog_block_5_0
  · exact catalog_block_5_1
  · exact catalog_block_5_2
  · exact catalog_block_5_3
  · exact catalog_block_5_4
  · exact catalog_block_5_5
  · exact catalog_block_5_6
  · exact catalog_block_5_7
  · exact catalog_block_5_8
  · exact catalog_block_5_9
  · exact catalog_block_5_10
  · exact catalog_block_5_11
  · exact catalog_block_5_12
  · exact catalog_block_5_13
  · exact catalog_block_5_14
  · exact catalog_block_5_15
  · exact catalog_block_5_16
  · exact catalog_block_5_17
  · exact catalog_block_5_18
  · exact catalog_block_5_19
  · exact catalog_block_5_20
  · exact catalog_block_5_21
  · exact catalog_block_5_22
  · exact catalog_block_5_23
  · exact catalog_block_5_24
  · exact catalog_block_5_25
  · exact catalog_block_5_26
  · exact catalog_block_5_27
  · exact catalog_block_5_28
  · exact catalog_block_5_29
  · exact catalog_block_5_30
  · exact catalog_block_5_31
  · exact catalog_block_5_32
  · exact catalog_block_5_33
  · exact catalog_block_5_34
  · exact catalog_block_5_35
  · exact catalog_block_5_36
  · exact catalog_block_5_37
  · exact catalog_block_5_38
  · exact catalog_block_5_39
  · exact catalog_block_5_40
  · exact catalog_block_5_41
  · exact catalog_block_5_42
  · exact catalog_block_5_43
  · exact catalog_block_5_44
  · exact catalog_block_5_45
  · exact catalog_block_5_46
  · exact catalog_block_5_47
  · exact catalog_block_5_48
  · exact catalog_block_5_49
  · exact catalog_block_5_50
  · exact catalog_block_5_51
  · exact catalog_block_5_52
  · exact catalog_block_5_53
  · exact catalog_block_5_54
  · exact catalog_block_5_55
  · exact catalog_block_5_56
  · exact catalog_block_5_57
  · exact catalog_block_5_58
  · exact catalog_block_5_59
  · exact catalog_block_5_60
  · exact catalog_block_5_61
  · exact catalog_block_5_62
  · exact catalog_block_5_63
  · exact catalog_block_5_64
  · exact catalog_block_5_65
  · exact catalog_block_5_66
  · exact catalog_block_5_67
  · exact catalog_block_5_68
  · exact catalog_block_5_69
  · exact catalog_block_5_70
  · exact catalog_block_5_71
  · exact catalog_block_5_72
  · exact catalog_block_5_73
  · exact catalog_block_5_74
  · exact catalog_block_5_75
  · exact catalog_block_5_76
  · exact catalog_block_5_77
  · exact catalog_block_5_78
  · exact catalog_block_5_79
  · exact catalog_block_5_80
  · exact catalog_block_5_81
  · exact catalog_block_5_82
  · exact catalog_block_5_83
  · exact catalog_block_5_84
  · exact catalog_block_5_85
  · exact catalog_block_5_86
  · exact catalog_block_5_87
  · exact catalog_block_5_88
  · exact catalog_block_5_89
  · exact catalog_block_5_90
  · exact catalog_block_5_91
  · exact catalog_block_5_92
  · exact catalog_block_5_93
  · exact catalog_block_5_94
  · exact catalog_block_5_95

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_1 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_2 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_3 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_4 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_5 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_6 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_7 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_8 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_9 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_10 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_11 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_12 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_13 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_14 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_15 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_16 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_17 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 17 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_18 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 18 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_19 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 19 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_20 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 20 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_21 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 21 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_22 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 22 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_23 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 23 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_24 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 24 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_25 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 25 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_26 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 26 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_27 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 27 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_28 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 28 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_29 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 29 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_30 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 30 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_31 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 31 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_32 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 32 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_33 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 33 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_34 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 34 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_35 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 35 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_36 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 36 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_37 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 37 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_38 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 38 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_39 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 39 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_40 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 40 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_41 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 41 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_42 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 42 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_43 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 43 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_44 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 44 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_45 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 45 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_46 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 46 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_6_47 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 47 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_6 (b : ℕ) (hb : b < 48) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 6 b = true := by
  interval_cases b
  · exact catalog_block_6_0
  · exact catalog_block_6_1
  · exact catalog_block_6_2
  · exact catalog_block_6_3
  · exact catalog_block_6_4
  · exact catalog_block_6_5
  · exact catalog_block_6_6
  · exact catalog_block_6_7
  · exact catalog_block_6_8
  · exact catalog_block_6_9
  · exact catalog_block_6_10
  · exact catalog_block_6_11
  · exact catalog_block_6_12
  · exact catalog_block_6_13
  · exact catalog_block_6_14
  · exact catalog_block_6_15
  · exact catalog_block_6_16
  · exact catalog_block_6_17
  · exact catalog_block_6_18
  · exact catalog_block_6_19
  · exact catalog_block_6_20
  · exact catalog_block_6_21
  · exact catalog_block_6_22
  · exact catalog_block_6_23
  · exact catalog_block_6_24
  · exact catalog_block_6_25
  · exact catalog_block_6_26
  · exact catalog_block_6_27
  · exact catalog_block_6_28
  · exact catalog_block_6_29
  · exact catalog_block_6_30
  · exact catalog_block_6_31
  · exact catalog_block_6_32
  · exact catalog_block_6_33
  · exact catalog_block_6_34
  · exact catalog_block_6_35
  · exact catalog_block_6_36
  · exact catalog_block_6_37
  · exact catalog_block_6_38
  · exact catalog_block_6_39
  · exact catalog_block_6_40
  · exact catalog_block_6_41
  · exact catalog_block_6_42
  · exact catalog_block_6_43
  · exact catalog_block_6_44
  · exact catalog_block_6_45
  · exact catalog_block_6_46
  · exact catalog_block_6_47

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_1 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_2 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_3 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_4 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_5 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_6 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_7 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_8 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_9 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_10 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_11 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_12 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_13 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_14 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_15 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_16 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_17 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 17 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_18 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 18 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_19 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 19 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_20 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 20 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_21 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 21 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_22 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 22 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_7_23 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 23 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_7 (b : ℕ) (hb : b < 24) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 7 b = true := by
  interval_cases b
  · exact catalog_block_7_0
  · exact catalog_block_7_1
  · exact catalog_block_7_2
  · exact catalog_block_7_3
  · exact catalog_block_7_4
  · exact catalog_block_7_5
  · exact catalog_block_7_6
  · exact catalog_block_7_7
  · exact catalog_block_7_8
  · exact catalog_block_7_9
  · exact catalog_block_7_10
  · exact catalog_block_7_11
  · exact catalog_block_7_12
  · exact catalog_block_7_13
  · exact catalog_block_7_14
  · exact catalog_block_7_15
  · exact catalog_block_7_16
  · exact catalog_block_7_17
  · exact catalog_block_7_18
  · exact catalog_block_7_19
  · exact catalog_block_7_20
  · exact catalog_block_7_21
  · exact catalog_block_7_22
  · exact catalog_block_7_23

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_8_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 8 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_8_1 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 8 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_8_2 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 8 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_8_3 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 8 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_8_4 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 8 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_8_5 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 8 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_8_6 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 8 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_8_7 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 8 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_8_8 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 8 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_8_9 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 8 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_8_10 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 8 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_8_11 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 8 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_8 (b : ℕ) (hb : b < 12) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 8 b = true := by
  interval_cases b
  · exact catalog_block_8_0
  · exact catalog_block_8_1
  · exact catalog_block_8_2
  · exact catalog_block_8_3
  · exact catalog_block_8_4
  · exact catalog_block_8_5
  · exact catalog_block_8_6
  · exact catalog_block_8_7
  · exact catalog_block_8_8
  · exact catalog_block_8_9
  · exact catalog_block_8_10
  · exact catalog_block_8_11

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_9_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 9 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_9_1 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 9 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_9_2 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 9 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_9_3 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 9 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_9_4 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 9 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_9_5 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 9 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_9 (b : ℕ) (hb : b < 6) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 9 b = true := by
  interval_cases b
  · exact catalog_block_9_0
  · exact catalog_block_9_1
  · exact catalog_block_9_2
  · exact catalog_block_9_3
  · exact catalog_block_9_4
  · exact catalog_block_9_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_10_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 10 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_10_1 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 10 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_10_2 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 10 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_10 (b : ℕ) (hb : b < 3) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 10 b = true := by
  interval_cases b
  · exact catalog_block_10_0
  · exact catalog_block_10_1
  · exact catalog_block_10_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_11_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 11 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_11_1 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 11 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_11 (b : ℕ) (hb : b < 2) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 11 b = true := by
  interval_cases b
  · exact catalog_block_11_0
  · exact catalog_block_11_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_12_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 12 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_12 (b : ℕ) (hb : b < 1) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 12 b = true := by
  have : b = 0 := by omega
  exact this ▸ catalog_block_12_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_13_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 13 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_13 (b : ℕ) (hb : b < 1) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 13 b = true := by
  have : b = 0 := by omega
  exact this ▸ catalog_block_13_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_14_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 14 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_14 (b : ℕ) (hb : b < 1) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 14 b = true := by
  have : b = 0 := by omega
  exact this ▸ catalog_block_14_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_15_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 15 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_15 (b : ℕ) (hb : b < 1) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 15 b = true := by
  have : b = 0 := by omega
  exact this ▸ catalog_block_15_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_16_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 16 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_16 (b : ℕ) (hb : b < 1) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 16 b = true := by
  have : b = 0 := by omega
  exact this ▸ catalog_block_16_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_17_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 17 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_17 (b : ℕ) (hb : b < 1) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 17 b = true := by
  have : b = 0 := by omega
  exact this ▸ catalog_block_17_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_18_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 18 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_18 (b : ℕ) (hb : b < 1) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 18 b = true := by
  have : b = 0 := by omega
  exact this ▸ catalog_block_18_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_19_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 19 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_19 (b : ℕ) (hb : b < 1) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 19 b = true := by
  have : b = 0 := by omega
  exact this ▸ catalog_block_19_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_20_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 20 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_20 (b : ℕ) (hb : b < 1) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 20 b = true := by
  have : b = 0 := by omega
  exact this ▸ catalog_block_20_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_21_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 21 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_21 (b : ℕ) (hb : b < 1) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 21 b = true := by
  have : b = 0 := by omega
  exact this ▸ catalog_block_21_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_22_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 22 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_22 (b : ℕ) (hb : b < 1) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 22 b = true := by
  have : b = 0 := by omega
  exact this ▸ catalog_block_22_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_block_23_0 : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 23 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks_23 (b : ℕ) (hb : b < 1) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) 23 b = true := by
  have : b = 0 := by omega
  exact this ▸ catalog_block_23_0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem catalog_blocks (i b : ℕ) (lo : 5 ≤ i) (hi : i ≤ 23)
    (hb : b < 99999999/2^(i+3)/4096+1) : (fun (i b : ℕ) =>
  List.all (List.filter (fun j => (fun (i d : ℕ) => ite (i ≤ 12) ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0) (
  Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
    (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ))) i (2^(i+3)*j+1))
    (List.range' (4096*b+1) (min 4096 (99999999/2^(i+3)-4096*b))))
    (fun j => List.contains ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) (i,2^(i+3)*j+1))) i b = true := by
  have casesI : i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 := by omega
  rcases casesI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact catalog_blocks_5 b hb
  · exact catalog_blocks_6 b hb
  · exact catalog_blocks_7 b hb
  · exact catalog_blocks_8 b hb
  · exact catalog_blocks_9 b hb
  · exact catalog_blocks_10 b hb
  · exact catalog_blocks_11 b hb
  · exact catalog_blocks_12 b hb
  · exact catalog_blocks_13 b hb
  · exact catalog_blocks_14 b hb
  · exact catalog_blocks_15 b hb
  · exact catalog_blocks_16 b hb
  · exact catalog_blocks_17 b hb
  · exact catalog_blocks_18 b hb
  · exact catalog_blocks_19 b hb
  · exact catalog_blocks_20 b hb
  · exact catalog_blocks_21 b hb
  · exact catalog_blocks_22 b hb
  · exact catalog_blocks_23 b hb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem small_prime_catalog_sound {n p : ℕ} (h : (n,p) ∈ ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ))) :
    p.Prime ∧ p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n ∧ ¬p^2 ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n := by
  let rows : List (ℕ×ℕ) := [(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)]
  have check : rows.all (fun e => decide (e.2 ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) e.1 ∧ ¬e.2^2 ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) e.1)) = true := by
    decide +kernel
  have hpList : p ∈ rows.map Prod.snd := List.mem_map.mpr ⟨(n,p),h,rfl⟩
  change p ∈ ([3, 17, 577, 665857, 257, 1409, 2448769, 11777, 2393857, 7681, 1492993, 79873, 12289, 65537, 18964481, 31113217, 6684673, 8519681] : List ℕ) at hpList
  constructor
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpList
    rcases hpList with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · exact of_decide_eq_true (List.all_eq_true.mp check (n,p) h)

/- Exhaust all possible prime divisors below the cutoff, using p=1+2^(n+3)j.
For indices 5 through 12 direct remainders are smaller. Later rows reduce at each step. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem small_prime_catalog_complete {n p : ℕ} (hp : p.Prime) (bound : p ≤ 100000000)
    (hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n) : (n,p) ∈ ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) := by
  by_cases early : n < 4
  · have E := (Nat.prime_dvd_prime_iff_eq hp (first_four_prime n early)).mp hd
    subst p
    interval_cases n <;> decide +kernel
  by_cases four : n = 4
  · subst n
    change p ∣ 257*1409*2448769 at hd
    rcases hp.dvd_mul.mp hd with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 257)).mp h
        decide +kernel
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1409)).mp h
        decide +kernel
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2448769)).mp h
      decide +kernel
  have pos : 0 < p-1 := by have := hp.two_le; omega
  have dv := divisor_order_modulus (n := n) (by omega) hp hd
  have hi : n ≤ 23 := by
    by_contra! large
    have E := Nat.le_of_dvd pos dv
    have rise := Nat.pow_le_pow_right (by decide : 0 < 2) (show 27 ≤ n+3 by omega)
    change 134217728 ≤ 2^(n+3) at rise
    omega
  let rows : List (ℕ×ℕ) := [(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)]
  let modtest (i d : ℕ) := if i ≤ 12 then (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) i % d == 0 else
    Nat.rec (motive := fun _ => ℤ) (3 % (d : ℤ))
      (fun (_ : ℕ) (r : ℤ) => (2*r^2-1) % (d : ℤ)) i == (0:ℤ)
  let row := fun i : ℕ =>
    let step := 2^(i+3)
    let m := 99999999/step
    (List.range (m/4096+1)).all fun b =>
      ((List.range' (4096*b+1) (min 4096 (m-4096*b))).filter
        (fun j => modtest i (step*j+1))).all (fun j => rows.contains (i,step*j+1))
  have checked : (List.range' 5 19).all row = true := by
    refine List.all_eq_true.mpr fun i hi' => List.all_eq_true.mpr fun b hb => ?_
    obtain ⟨il,iu⟩ := List.mem_range'_1.mp hi'
    exact catalog_blocks i b il (by omega) (List.mem_range.mp hb)
  have memo : n ∈ List.range' 5 19 := List.mem_range'_1.mpr (by omega)
  have checkedN := List.all_eq_true.mp checked n memo
  obtain ⟨j,he⟩ := dv
  have jpos : 1 ≤ j := by
    by_contra! h
    rw [show j=0 by omega, mul_zero] at he
    omega
  have p_eq : p = 2^(n+3)*j+1 := by omega
  have jtop : j ≤ 99999999 / 2^(n+3) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    rw [mul_comm]
    omega
  have T : modtest n (2^(n+3)*j+1) = true := by
    rw [← p_eq]
    dsimp [modtest]
    split_ifs
    · exact beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd hd)
    · exact beq_iff_eq.mpr ((x_mod_recurrence n p).symm.trans
        (Int.emod_eq_zero_of_dvd (by exact_mod_cast hd)))
  rw [p_eq]
  exact List.contains_iff_mem.mp
    (catalog_grid_sound (fun k => modtest n (2^(n+3)*k+1))
      (fun k => rows.contains (n,2^(n+3)*k+1)) j _ jpos jtop T checkedN)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem small_prime_catalog_iff {n p : ℕ} (hp : p.Prime) (bound : p ≤ 100000000) :
    p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n ↔ (n,p) ∈ ([(0,3), (1,17), (2,577), (3,665857), (4,257), (4,1409), (4,2448769), (5,11777), (5,2393857), (6,7681), (6,1492993), (8,79873), (9,12289), (10,65537), (10,18964481), (10,31113217), (14,6684673), (14,8519681)] : List (ℕ×ℕ)) :=
  ⟨small_prime_catalog_complete hp bound, fun h => (small_prime_catalog_sound h).2.1⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem no_small_prime_square {n p : ℕ} (hp : p.Prime) (bound : p ≤ 100000000) : ¬ p^2 ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n := by
  intro h
  have hd : p ∣ (Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans h
  exact (small_prime_catalog_sound (small_prime_catalog_complete hp bound hd)).2.2 h

end Pell292

namespace OMA.R_oeis_a292082_R1_H2_R1
open Pell292

/-- Arbitrarily high dyadic orders have a prime witness below the square root
of the corresponding Pell coordinate. One witness suffices at each selected index. -/
def H1 : Prop :=
  let x : ℕ → ℕ := Nat.rec 3 (fun _ k => 2*k^2-1)
  ∀ B : ℕ, ∃ n p : ℕ, B ≤ n ∧ p.Prime ∧ 2 < p ∧ p^2 ≤ x (n+2) ∧
    ∃ t : ZMod p, t^2=2 ∧ orderOf (1+t)=2^(n+5)

/-- After such a witness, a successful base-five Euler test at the next term
eventually always encounters a failed unit check in every two-term Lucas certificate. -/
def H2 : Prop :=
  let x : ℕ → ℕ := Nat.rec 3 (fun _ k => 2*k^2-1)
  ∃ B : ℕ, ∀ n : ℕ, B ≤ n → 1 ≤ n →
    (∃ p : ℕ, p.Prime ∧ 2 < p ∧ p^2 ≤ x (n+2) ∧
      ∃ t : ZMod p, t^2=2 ∧ orderOf (1+t)=2^(n+5)) →
    (5 : ZMod (x (n+3)))^(x (n+3)/2) = -1 →
    let F := x n * x (n+1)
    ∀ b : ZMod (x (n+3)), b^F=1 → ∃ q : ℕ, q.Prime ∧
      (q ∣ x n ∨ q ∣ x (n+1)) ∧ ¬ IsUnit (b^(F/q)-1)

theorem main : H1 → H2 → OMA.R_oeis_a292082_R1.H2 := by
  intro seeds transitions
  obtain ⟨B, hb⟩ := transitions
  obtain ⟨n,p,hn,hp,hp2,hs,hh⟩ := seeds (max B 1)
  have hnB : B ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have init : ¬ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+2)).Prime := (composite_iff_small_order (n+2) (by omega)).mpr
    ⟨p,hp,hp2,hs,hh⟩
  have tail : ∀ j : ℕ, ¬ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) (n+j+2)).Prime := by
    intro j
    induction j with
    | zero => exact init
    | succ j ih =>
      intro pr
      have hit := (composite_iff_small_order (n+j+2) (by omega)).mp ih
      have eu := euler_five_of_prime (n+j+2) pr
      obtain ⟨b,hbF,unit⟩ := (pell_two_lucas_iff (n+j) (by omega)).mp pr
      obtain ⟨q,hq,hd,fail⟩ := hb (n+j) (by omega) (by omega) hit eu b hbF
      exact fail (unit q hq hd)
  refine ⟨n+2,fun k hk => ?_⟩
  exact Eq.mp (congrArg (fun t : ℕ => ¬ ((Nat.rec (motive := fun _ => ℕ) 3 (fun _ k => 2*k^2-1)) t).Prime) (show n+(k-(n+2))+2=k by omega)) (tail (k-(n+2)))

/-- Both tasks are necessary as well as sufficient. -/
theorem converse (hall : OMA.R_oeis_a292082_R1.H2) : H1 ∧ H2 := by
  obtain ⟨N,hN⟩ := hall
  constructor
  · intro B
    let n := max B N
    have hn : N ≤ n+2 := (le_max_right _ _).trans (Nat.le_add_right _ _)
    obtain ⟨p,hp,hp2,hs,hh⟩ := (composite_iff_small_order (n+2) (by omega)).mp (hN _ hn)
    exact ⟨n,p,le_max_left _ _,hp,hp2,hs,hh⟩
  · refine ⟨N,?_⟩
    intro n hn hpos _ _
    dsimp only
    intro b hb
    by_contra! all_units
    apply hN (n+3) (by omega)
    apply (pell_two_lucas_iff n hpos).mpr
    exact ⟨b,hb,fun q hq hd => all_units q hq hd⟩

end OMA.R_oeis_a292082_R1_H2_R1
