import OMAStatements.S_oeis_a173195
import Mathlib

open OMA.S_oeis_a173195

private theorem choose_parity (n k : ℕ) :
    n.choose k % 2 = 1 ↔ k%2 ≤ n%2 ∧ (n/2).choose (k/2) % 2 = 1 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := 2)
  change n.choose k % 2 = ((n%2).choose (k%2) * (n/2).choose (k/2)) % 2 at h
  rw [h]
  have hn : n%2 = 0 ∨ n%2 = 1 := by omega
  have hk : k%2 = 0 ∨ k%2 = 1 := by omega
  rcases hn with hn | hn <;> rcases hk with hk | hk <;> simp [hn,hk]

private theorem no_shift_choose (u : ℕ) (hu : 0 < u) :
    (4*u).choose u % 2 ≠ 1 := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro hh
    obtain ⟨hodd,hsub⟩ := (choose_parity (4*u) u).mp hh
    have he : u = 2*(u/2) := by omega
    have h1 : (4*u)/2 = 4*(u/2) := by omega
    rw [h1] at hsub
    exact ih (u/2) (by omega) (by omega) hsub

private theorem binomial_double (u : ℕ) (hu : 0 < u) :
    binomialOdd (2*u) ↔ binomialOdd u := by
  unfold binomialOdd
  rw [choose_parity]
  have h₁ : (4*(2*u)-1)%2 = 1 := by omega
  have h₂ : (4*(2*u)-1)/2 = 4*u-1 := by omega
  have h₃ : (2*u)/2 = u := by omega
  simp [h₁,h₂,h₃]

private theorem binomial_four_one (u : ℕ) :
    binomialOdd (4*u+1) ↔ u=0 := by
  unfold binomialOdd
  rw [choose_parity]
  have h₁ : (4*(4*u+1)-1)%2 = 1 := by omega
  have h₂ : (4*(4*u+1)-1)/2 = 8*u+1 := by omega
  have h₃ : (4*u+1)/2 = 2*u := by omega
  rw [h₁,h₂,h₃]
  have h₄ : (4*u+1)%2 = 1 := by omega
  rw [h₄]
  simp only [le_refl, true_and, choose_parity (8*u+1) (2*u)]
  have h₅ : (8*u+1)%2 = 1 := by omega
  have h₆ : (8*u+1)/2 = 4*u := by omega
  have h₇ : (2*u)/2 = u := by omega
  simp only [h₅,h₆,h₇, Nat.mul_mod_right, Nat.zero_le, true_and]
  constructor
  · intro h
    by_contra hh
    exact no_shift_choose u (by omega) h
  · rintro rfl
    decide

private theorem binomial_four_three (u : ℕ) :
    binomialOdd (4*u+3) ↔ u%2 = 0 ∧ binomialOdd (u+1) := by
  unfold binomialOdd
  rw [choose_parity]
  have h₁ : (4*(4*u+3)-1)%2 = 1 := by omega
  have h₂ : (4*(4*u+3)-1)/2 = 8*u+5 := by omega
  have h₃ : (4*u+3)/2 = 2*u+1 := by omega
  have h₄ : (4*u+3)%2 = 1 := by omega
  rw [h₁,h₂,h₃,h₄]
  simp only [le_refl, true_and, choose_parity (8*u+5) (2*u+1)]
  have h₅ : (8*u+5)%2 = 1 := by omega
  have h₆ : (8*u+5)/2 = 4*u+2 := by omega
  have h₇ : (2*u+1)/2 = u := by omega
  have h₈ : (2*u+1)%2 = 1 := by omega
  rw [h₅,h₆,h₇,h₈]
  simp only [le_refl, true_and, choose_parity (4*u+2) u]
  have h₉ : (4*u+2)%2 = 0 := by omega
  have h₁₀ : (4*u+2)/2 = 2*u+1 := by omega
  rw [h₉,h₁₀]
  simp only [Nat.le_zero]
  constructor
  · rintro ⟨he,h⟩
    refine ⟨he, ?_⟩
    rw [choose_parity]
    have h1 : (u+1)%2 = 1 := by omega
    have h2 : (4*(u+1)-1)%2 = 1 := by omega
    have h3 : (4*(u+1)-1)/2 = 2*u+1 := by omega
    have h4 : (u+1)/2 = u/2 := by omega
    simpa [h1,h2,h3,h4]
  · rintro ⟨he,h⟩
    refine ⟨he, ?_⟩
    rw [choose_parity] at h
    have h3 : (4*(u+1)-1)/2 = 2*u+1 := by omega
    have h4 : (u+1)/2 = u/2 := by omega
    simpa [h3,h4] using h.2

private theorem binomial_odd_shape (m : ℕ) (hm : m%2 = 1) :
    binomialOdd m ↔ ∃ j : ℕ, 3*m = 2^(2*j+1)+1 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hm4 : m = 4*(m/4)+1 ∨ m = 4*(m/4)+3 := by omega
    rcases hm4 with h1 | h3
    · have hb : binomialOdd m ↔ m=1 := by
        conv_lhs => rw [h1, binomial_four_one]
        omega
      rw [hb]
      constructor
      · rintro rfl
        exact ⟨0,by decide⟩
      · rintro ⟨j,hj⟩
        cases j with
        | zero => norm_num at hj; omega
        | succ j =>
          rw [show 2*(j+1)+1 = (2*j+1)+2 by omega, pow_add] at hj
          norm_num at hj
          omega
    · have hu : m/4+1 < m := by omega
      constructor
      · intro hb
        have hh : binomialOdd (4*(m/4)+3) := h3 ▸ hb
        obtain ⟨he,hb'⟩ := (binomial_four_three _).mp hh
        obtain ⟨j,hj⟩ := (ih (m/4+1) hu (by omega)).mp hb'
        refine ⟨j+1, ?_⟩
        rw [show 2*(j+1)+1 = (2*j+1)+2 by omega, pow_add]
        norm_num
        omega
      · rintro ⟨j,hj⟩
        cases j with
        | zero => norm_num at hj; omega
        | succ j =>
          rw [show 2*(j+1)+1 = (2*j+1)+2 by omega, pow_add] at hj
          norm_num at hj
          have hnew : 3*(m/4+1) = 2^(2*j+1)+1 := by omega
          have hpow : (2^(2*j+1):ℕ)%2 = 0 := by
            rw [pow_succ]
            omega
          have he : (m/4)%2 = 0 := by omega
          have hb' := (ih (m/4+1) hu (by omega)).mpr ⟨j,hnew⟩
          have hh := (binomial_four_three (m/4)).mpr ⟨he,hb'⟩
          rw [← h3] at hh
          exact hh

private theorem binomial_shape (m : ℕ) (hm : 0 < m) :
    binomialOdd m ↔ ∃ t j : ℕ, 3*m = 2^t*(2^(2*j+1)+1) := by
  constructor
  · intro hb
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases he : m%2 = 0
      · have hp : 0 < m/2 := by omega
        have hm2 : m = 2*(m/2) := by omega
        have hb2 : binomialOdd (2*(m/2)) := hm2 ▸ hb
        obtain ⟨t,j,hh⟩ := ih (m/2) (by omega) hp ((binomial_double _ hp).mp hb2)
        refine ⟨t+1,j,?_⟩
        rw [pow_succ, mul_assoc, mul_comm 2, ← mul_assoc]
        omega
      · obtain ⟨j,hj⟩ := (binomial_odd_shape m (by omega)).mp hb
        exact ⟨0,j,by simpa using hj⟩
  · rintro ⟨t,j,hj⟩
    induction t generalizing m with
    | zero =>
      simp only [pow_zero, one_mul] at hj
      have hpow : (2^(2*j+1):ℕ)%2 = 0 := by rw [pow_succ]; omega
      exact (binomial_odd_shape m (by omega)).mpr ⟨j,hj⟩
    | succ t ih =>
      have hh : 3*m = 2*(2^t*(2^(2*j+1)+1)) := by
        rw [pow_succ] at hj
        nlinarith only [hj]
      have hm2 : m = 2*(m/2) := by omega
      have hp : 0 < m/2 := by omega
      have hb := (binomial_double (m/2) hp).mpr (ih (m/2) hp (by omega))
      simpa only [← hm2] using hb

private theorem four_pow_mod {n : ℕ} (hn : 0 < n) : (4^n : ℕ)%4 = 0 :=
  Nat.mod_eq_zero_of_dvd (dvd_pow_self _ hn.ne')

private theorem sum_pow_mod (a b : ℕ) (hab : a ≤ b) :
    (1+4^a+4^b : ℕ)%4 ≠ 0 := by
  by_cases ha : a=0
  · by_cases hb : b=0
    · subst a; subst b; decide
    · have h := four_pow_mod (n := b) (by omega)
      subst a
      simp only [pow_zero]
      omega
  · have h₁ := four_pow_mod (n := a) (by omega)
    have h₂ := four_pow_mod (n := b) (by omega)
    omega

private theorem square_scale {s k : ℕ} (x : ℕ) (hk : k^2 = 4^x*s) :
    ∃ r : ℕ, k=2^x*r ∧ r^2=s := by
  induction x generalizing k with
  | zero => exact ⟨k, by simp, by simpa using hk⟩
  | succ x ih =>
    have hmod : (k*k)%2=0 := by
      rw [← pow_two, hk, pow_succ 4 x]
      exact Nat.mod_eq_zero_of_dvd ⟨2*(4^x*s), by ring⟩
    have hke : k%2=0 := by
      by_contra h
      have he : k%2=1 := by omega
      rw [Nat.mul_mod, he] at hmod
      contradiction
    have he : k=2*(k/2) := by omega
    have hh : (k/2)^2=4^x*s := by
      have ht : k^2 = (2*(k/2))^2 := congrArg (·^2) he
      rw [pow_succ 4 x] at hk
      nlinarith only [ht,hk]
    obtain ⟨r,hr,hrs⟩ := ih hh
    refine ⟨r, ?_, hrs⟩
    calc
      k = 2*(k/2) := he
      _ = 2^(x+1)*r := by rw [hr,pow_succ]; ring

private theorem reduce_scale {s k : ℕ} (hs : s%4 ≠ 0) (x h : ℕ)
    (he : 4^x*s=4^h*k^2) : ∃ t r : ℕ, k=2^t*r ∧ r^2=s := by
  induction h generalizing x with
  | zero =>
    obtain ⟨r,hr,he⟩ := square_scale x (by simpa using he.symm)
    exact ⟨x,r,hr,he⟩
  | succ h ih =>
    cases x with
    | zero =>
      rw [pow_zero, one_mul, pow_succ 4 h] at he
      exact False.elim (hs (Nat.mod_eq_zero_of_dvd ⟨4^h*k^2, by nlinarith only [he]⟩))
    | succ x =>
      apply ih x
      rw [pow_succ 4 x, pow_succ 4 h] at he
      nlinarith only [he]

private theorem sq_power {a b r : ℕ} (hab : a ≤ b)
    (he : r^2 = 1+4^a+4^b) : b+1 = 2*a ∧ r=2^b+1 := by
  have ha : 0 < a := by
    by_contra hh
    have haz : a=0 := by omega
    have hr : r^2%4=0 ∨ r^2%4=1 := by
      rw [pow_two, Nat.mul_mod]
      have ht : r%4 = 0 ∨ r%4 = 1 ∨ r%4 = 2 ∨ r%4 = 3 := by omega
      rcases ht with h | h | h | h <;> norm_num [h]
    by_cases hb : b=0
    · rw [he,haz,hb] at hr
      norm_num at hr
    · have hbm := four_pow_mod (n := b) (by omega)
      rw [he,haz,pow_zero] at hr
      omega
  have hbb : 0 < b := by omega
  have hf : (4^b : ℕ) = (2^b)^2 := by rw [← pow_mul, mul_comm b 2,pow_mul]; norm_num
  have hPa : (4^a : ℕ) = 2^(2*a) := by rw [pow_mul]; norm_num
  let P : ℕ := 2^b
  have hP : 0 < P := by positivity
  have hpf : (4^b : ℕ) = P^2 := hf
  rw [hpf] at he
  have hrlo : P < r := by
    by_contra h
    have h1 : r^2 ≤ P^2 := Nat.pow_le_pow_left (by omega) _
    exact (not_lt_of_ge h1) (by rw [he]; exact Nat.lt_add_of_pos_left (by positivity))
  have hlarge : b < 2*a := by
    by_contra! h
    have h1 : (4^a : ℕ) ≤ P := by
      rw [hPa]
      exact Nat.pow_le_pow_right (by decide) h
    have h2 : (P+1)^2 ≤ r^2 := Nat.pow_le_pow_left (by omega) _
    nlinarith only [he,h1,h2,hP]
  have hsmall : 2*a ≤ b+1 := by
    by_contra! hs
    have ha2 : 2 ≤ a := by omega
    have hp4 : 4 ≤ P := by
      simpa [P] using Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ b by omega)
    have heo : r%2=1 := by
      have hm : (r*r)%2=1 := by
        rw [← pow_two, he, ← hpf]
        have ha4 := four_pow_mod ha
        have hb4 := four_pow_mod hbb
        omega
      by_contra h0
      have hr0 : r%2=0 := by omega
      rw [Nat.mul_mod, hr0] at hm
      contradiction
    let u := (r-1)/2
    have hu : 0 < u := by dsimp [u]; omega
    have hru : r = 2*u+1 := by dsimp [u]; omega
    let A : ℕ := 4^(a-1)
    have hAs : IsPrimePow A := by
      unfold A
      rw [isPrimePow_nat_iff]
      refine ⟨2,2*(a-1),Nat.prime_two,by omega,?_⟩
      rw [pow_mul]
      norm_num
    have h4a : (4^a : ℕ) = 4*A := by
      dsimp [A]
      conv_lhs => rw [show a = (a-1)+1 by omega,pow_succ,mul_comm]
    have hbpow : (4^b : ℕ) = 4^a*4^(b-a) := by rw [← pow_add, show a+(b-a)=b by omega]
    have hAeq : u*(u+1) = A*(1+4^(b-a)) := by
      rw [hru, ← hpf, hbpow, h4a] at he
      nlinarith only [he]
    have hdiv : A ∣ u*(u+1) := ⟨_,hAeq⟩
    have hcop : Nat.Coprime u (u+1) := by simp
    have huA : u+1 < A := by
      have ha_le : (4^a : ℕ) ≤ 4^b := Nat.pow_le_pow_right (by decide) hab
      rw [hpf] at ha_le
      have hr2 : r ≤ 2*P := by
        by_contra h
        have hs2 : (2*P)^2 ≤ r^2 := Nat.pow_le_pow_left (by omega) _
        nlinarith only [hs2, he, ha_le, hp4, sq_nonneg ((P : ℤ)-4)]
      have hrhi : r+1 < 2*P := by
        by_contra h
        have hh : (2*P)^2 ≤ (r+1)^2 := Nat.pow_le_pow_left (by omega) _
        nlinarith only [hh, he, ha_le, hr2, hp4, sq_nonneg ((P : ℤ)-4)]
      have hcap : 2*P ≤ 2*A := by
        have hab' : b ≤ 2*(a-1) := by omega
        have h := Nat.pow_le_pow_right (by decide : 0 < 2) hab'
        rw [pow_mul] at h
        exact Nat.mul_le_mul_left _ (by simpa [P,A] using h)
      omega
    rcases (hcop.isPrimePow_dvd_mul hAs).mp hdiv with h | h
    · have hh := Nat.le_of_dvd hu h
      omega
    · have hh := Nat.le_of_dvd (Nat.succ_pos _) h
      omega
  have heq : b+1=2*a := by omega
  have hs : (4^a : ℕ) = 2*P := by
    rw [hPa, ← heq, pow_succ]
    dsimp [P]
    omega
  have hr : r = P+1 := by
    rw [hs] at he
    by_contra h
    have ht : P+2 ≤ r := by omega
    have hsq : (P+2)^2 ≤ r^2 := Nat.pow_le_pow_left ht _
    nlinarith only [he,hsq,hP]
  exact ⟨heq,hr⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a173195.main := by
  intro k hk
  constructor
  · rintro ⟨h,x,a,b,hab,he⟩
    obtain ⟨t,r,hr,hs⟩ := reduce_scale (sum_pow_mod a b hab) x h he
    obtain ⟨heq,hroot⟩ := sq_power hab hs
    have ha : 0 < a := by omega
    have hb : b = 2*(a-1)+1 := by omega
    have ht : (2^(2*(a-1)+1)+1 : ℕ) % 3 = 0 := by
      have heven : (4:ℕ)^(a-1) % 3 = 1 := by
        induction (a-1) with
        | zero => decide
        | succ n ih => rw [pow_succ 4 n, Nat.mul_mod, ih]
      rw [pow_succ, pow_mul]
      norm_num only [show (2:ℕ)^2=4 by decide]
      omega
    let m := k/3
    have hm : k = 3*m := by
      have e : r % 3 = 0 := by simpa [hroot,hb] using ht
      have hd : 3 ∣ r := Nat.dvd_of_mod_eq_zero e
      have hdk : 3 ∣ k := by rw [hr]; exact dvd_mul_of_dvd_right hd _
      have hk3 := Nat.mod_eq_zero_of_dvd hdk
      dsimp [m]
      omega
    have hmpos : 0 < m := by omega
    refine ⟨m, hmpos, (binomial_shape m hmpos).mpr ⟨t,a-1,?_⟩, hm⟩
    rw [← hm, hr, hroot, hb]
  · rintro ⟨m,hm,hb,he⟩
    obtain ⟨t,j,hs⟩ := (binomial_shape m hm).mp hb
    refine ⟨0,t,j+1,2*j+1,by omega,?_⟩
    have heq : (4^(j+1) : ℕ) = 2*2^(2*j+1) := by
      rw [← show (2:ℕ)^2=4 by decide, ← pow_mul, show 2*(j+1)=2*j+1+1 by omega,pow_succ,mul_comm]
    have hp : (4^(2*j+1) : ℕ) = (2^(2*j+1))^2 := by rw [← pow_mul,mul_comm (2*j+1) 2,pow_mul]; norm_num
    have ht : (4^t : ℕ) = (2^t)^2 := by rw [← pow_mul,mul_comm t 2,pow_mul]; norm_num
    rw [he,hs,heq,hp,ht,pow_zero,one_mul]
    ring