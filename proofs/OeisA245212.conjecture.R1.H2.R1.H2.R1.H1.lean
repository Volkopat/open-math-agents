import OMAReductions.R_OeisA245212_conjecture_R1_H2_R1_H2_R1

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

open private OMA.R_OeisA245212_conjecture_R1_H2_R1.moment_mul
  OMA.R_OeisA245212_conjecture_R1_H2_R1.moment_at_power
  from OMAReductions.R_OeisA245212_conjecture_R1_H2_R1

private def W (b : ℕ) := ∑ d ∈ b.divisors, d*d.divisors.card
private def S (b : ℕ) := σ 1 b
private def T (b : ℕ) := b*b.divisors.card
private def N (b : ℕ) := W b+S b
private def D (b : ℕ) := 4*b*b.divisors.card-(2*W b+S b)
private def C (u : ℕ) := W u+(W u-S u)
private def K (u : ℕ) := W u*S u+2*T u*(W u-S u)

private theorem power_moments (k : ℕ) :
    (∑ j ∈ range (k+1), (2:ℕ)^j*(j+1))=k*2^(k+1)+1 ∧
    (∑ j ∈ range (k+1), (2:ℕ)^j)+1=2^(k+1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [sum_range_succ (fun j => 2^j*(j+1)) (k+1),sum_range_succ (fun j => 2^j) (k+1),
      ih.1,pow_succ (2:ℕ) (k+1)]
    constructor <;> nlinarith only [ih.2]

private theorem moment_le (u : ℕ) : S u ≤ W u := by
  unfold S W
  rw [sigma_one_apply]
  refine sum_le_sum fun d hd => ?_
  have dp := Nat.pos_of_mem_divisors hd
  have c := card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr dp.ne'⟩
  simpa using Nat.mul_le_mul_left d (show 1≤d.divisors.card from c)

private theorem log_bound {n A : ℕ} (hn : 0<n) (h : 2^n≤n*A) :
    n/2 ≤ Nat.log 2 A := by
  have twice (j : ℕ) : 2*j ≤ 2^j := by
    induction j with
    | zero => decide
    | succ j ih =>
      cases j with
      | zero => decide
      | succ j =>
        rw [pow_succ]
        have pos : 1<2^(j+1) := Nat.one_lt_pow (by omega) (by decide)
        omega
  have half : n ≤ 2^(n-n/2) := (show n≤2*(n-n/2) by omega).trans (twice _)
  have hh := Nat.mul_le_mul_left (2^(n/2)) half
  rw [←pow_add,show n/2+(n-n/2)=n by omega] at hh
  exact Nat.le_log_of_pow_le (by decide) ((mul_le_mul_iff_left₀ hn).mp
    ((hh.trans h).trans_eq (Nat.mul_comm _ _)))

theorem OMA.solution : OMA.R_OeisA245212_conjecture_R1_H2_R1_H2_R1.H1 := by
  intro k u odd
  change 0<D (2^k*u) → D (2^k*u)∣N (2^k*u) → D (2^k*u)∣(k+1)*K u ∧ (k+1)/2≤Nat.log 2 (C u+K u) ∧ N (2^k*u)/D (2^k*u)≤k*W u+S u+(k+1)*K u
  intro hd dvd
  let b := 2^k*u
  have cp := (Nat.coprime_two_left.mpr odd).pow_left k
  have geom := power_moments k
  have w : W b=(k*2^(k+1)+1)*W u := by
    unfold b W
    rw [OMA.R_OeisA245212_conjecture_R1_H2_R1.moment_mul _ _ cp,
      OMA.R_OeisA245212_conjecture_R1_H2_R1.moment_at_power _ _ Nat.prime_two,geom.1]
  have s : S b+S u=2^(k+1)*S u := by
    unfold b S
    rw [isMultiplicative_sigma.map_mul_of_coprime cp,sigma_apply_prime_pow Nat.prime_two]
    simpa only [mul_one,add_mul,one_mul] using congrArg (fun z : ℕ => z*(σ 1 u)) geom.2
  have t : T b=2^k*(k+1)*T u := by
    unfold b T
    rw [cp.card_divisors_mul,Nat.divisors_prime_pow Nat.prime_two,card_map,card_range]
    ring
  have da : D b + (2*W b+S b) = 4*T b := by
    have p : 2*W b+S b≤4*b*b.divisors.card := Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hd)
    exact (Nat.sub_add_cancel p).trans (by unfold T; ring)
  let z : ℤ := 2^(k+1)
  let l : ℤ := 2*((k:ℤ)+1)*T u-2*k*W u-S u
  let g : ℤ := k* (W u : ℤ)+S u
  have cd := Nat.sub_add_cancel (moment_le u)
  have c : (C u:ℤ)=2*(W u:ℤ)-S u := by unfold C; push_cast; omega
  have coeff : (K u:ℤ)=(W u:ℤ)*S u+2*T u*((W u:ℤ)-S u) := by
    unfold K; push_cast [Nat.cast_sub (moment_le u)]; ring
  have dn : (D b:ℤ)=z*l-C u := by
    zify at w s t da
    dsimp only [z,l]; rw [c]
    rw [pow_succ (2:ℤ) k] at w s ⊢
    linear_combination da - 2*w - s + 4*t
  have nn : (N b:ℤ)=z*g+((W u:ℤ)-S u) := by
    zify at w s
    unfold N; push_cast; dsimp only [z,g]
    linear_combination w+s
  have iden : l*(N b:ℤ)-g*D b=((k:ℤ)+1)*K u := by
    rw [nn,dn,c,coeff]; dsimp only [l,g]; ring
  obtain ⟨p,hp⟩ := dvd
  change N b=D b*p at hp
  have dz : (D b:ℤ)∣((k:ℤ)+1)*K u := by
    refine ⟨l*p-g,?_⟩
    rw [←iden,hp]; push_cast; ring
  have natdvd : D b∣(k+1)*K u := by exact_mod_cast dz
  have sup : 0<S u := by
    rw [S,sigma_one_apply]
    exact sum_pos' (fun _ _ => Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr odd.pos.ne',by decide⟩
  have wup : 0<W u := sup.trans_le (moment_le u)
  have kp : 0<K u := Nat.add_pos_left (Nat.mul_pos wup sup) _
  have bound := Nat.le_of_dvd (Nat.mul_pos (Nat.succ_pos k) kp) natdvd
  have posz : 0<z := by dsimp only [z]; positivity
  have dd : (0:ℤ)<D b := by exact_mod_cast hd
  have cc : (0:ℤ)≤C u := by positivity
  have lp : 1≤l := by
    by_contra! small
    have non := mul_nonpos_of_nonneg_of_nonpos posz.le (show l≤0 by omega)
    omega
  have eqle : z≤(D b:ℤ)+C u := by
    have up := mul_le_mul_of_nonneg_left lp posz.le
    rw [mul_one] at up; omega
  have cap : 2^(k+1) ≤ D b+C u := by dsimp only [z] at eqle; exact_mod_cast eqle
  have large : 2^(k+1)≤(k+1)*(C u+K u) := by
    have := Nat.mul_le_mul_right (C u) (show 1≤k+1 by omega)
    nlinarith only [cap,bound,this]
  have ident : (l*p-g)*(D b:ℤ)=((k:ℤ)+1)*K u := by
    rw [←iden,hp]; push_cast; ring
  have ng : 0≤l*p-g := by
    by_contra! neg
    have bad := mul_neg_of_neg_of_pos neg dd
    rw [ident] at bad
    have good : (0:ℤ)≤((k:ℤ)+1)*K u := by positivity
    omega
  have dif := mul_le_mul_of_nonneg_left (show (1:ℤ)≤D b by omega) ng
  rw [mul_one,ident] at dif
  have pl := mul_le_mul_of_nonneg_right lp (Nat.cast_nonneg p : (0:ℤ)≤p)
  rw [one_mul] at pl
  have pb : (p:ℤ)≤g+((k:ℤ)+1)*K u := by omega
  have hquot : N b/D b=p := by rw [hp,Nat.mul_comm (D b) p,Nat.mul_div_cancel _ hd]
  refine ⟨natdvd,log_bound (Nat.succ_pos _) large,?_⟩
  change N b/D b≤_
  rw [hquot]; dsimp only [g] at pb; exact_mod_cast pb
