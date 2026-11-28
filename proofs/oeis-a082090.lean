import OMAStatements.S_oeis_a082090
import Mathlib




lemma nth_prime_bound (i : ℕ) : Nat.nth Nat.Prime i ≤ 2 ^ (i + 1) := by
  induction i with
  | zero => simp [Nat.nth_prime_zero_eq_two]
  | succ i ih =>
    let p := Nat.nth Nat.Prime i
    have hp : p.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i
    obtain ⟨r, hr, hpr, hrbound⟩ := Nat.exists_prime_lt_and_le_two_mul p hp.ne_zero
    have hnext : Nat.nth Nat.Prime (i+1) ≤ r := by
      by_contra hh
      have := Nat.le_nth_of_lt_nth_succ (p := Nat.Prime) (k := i) (a := r) (by omega) hr
      omega
    rw [pow_succ]
    calc
      Nat.nth Nat.Prime (i+1) ≤ r := hnext
      _ ≤ 2*p := hrbound
      _ ≤ 2*2^(i+1) := Nat.mul_le_mul_left _ ih
      _ = 2^(i+1)*2 := by omega

lemma prime_le_two_pow_count {p : ℕ} (hp : p.Prime) : p ≤ 2 ^ Nat.primeCounting p := by
  have h := nth_prime_bound (Nat.count Nat.Prime p)
  rw [Nat.nth_count hp] at h
  simpa [Nat.primeCounting, Nat.primeCounting', Nat.count_succ, hp] using h

lemma list_prod_bound (L : List ℕ) (h : ∀ p ∈ L, p.Prime) :
    L.prod ≤ 2 ^ (L.map Nat.primeCounting).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha : a.Prime := h a (by simp)
    have ht : ∀ p ∈ L, p.Prime := fun p hp => h p (by simp [hp])
    simp only [List.prod_cons, List.map_cons, List.sum_cons, pow_add]
    exact Nat.mul_le_mul (prime_le_two_pow_count ha) (ih ht)

lemma pseudo_log_bound (n : ℕ) : n ≤ 2 ^ (n.primeFactorsList.map Nat.primeCounting).sum := by
  by_cases h : n = 0
  · simp [h]
  · have hh := list_prod_bound n.primeFactorsList (fun _ hp => Nat.prime_of_mem_primeFactorsList hp)
    simpa only [Nat.prod_primeFactorsList h] using hh

lemma prime_count_lt {p : ℕ} (hp : p.Prime) : Nat.primeCounting p < p := by
  have h := Nat.add_two_le_nth_prime (Nat.count Nat.Prime p)
  rw [Nat.nth_count hp] at h
  simp [Nat.primeCounting, Nat.primeCounting', Nat.count_succ, hp]
  omega

lemma list_sum_lt_prod (L : List ℕ) (h : ∀ p ∈ L, p.Prime) :
    (L.map Nat.primeCounting).sum < L.prod := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp : p.Prime := h p (by simp)
    have hL : ∀ q ∈ L, q.Prime := fun q hq => h q (by simp [hq])
    have hprev := ih hL
    have hcount := prime_count_lt hp
    have hp2 := hp.two_le
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    by_cases hprod : L.prod = 1
    · have hz : (L.map Nat.primeCounting).sum = 0 := by omega
      simpa [hprod, hz] using hcount
    · have htwo : 2 ≤ L.prod := by omega
      have h1 := Nat.mul_le_mul_left p htwo
      have h2 := Nat.mul_le_mul_right L.prod hp2
      nlinarith

lemma pseudo_log_lt {n : ℕ} (hn : n ≠ 0) : (n.primeFactorsList.map Nat.primeCounting).sum < n := by
  have h := list_sum_lt_prod n.primeFactorsList (fun _ hp => Nat.prime_of_mem_primeFactorsList hp)
  simpa only [Nat.prod_primeFactorsList hn] using h

lemma pseudo_log_pow_two (n : ℕ) :
    (((2 : ℕ) ^ n).primeFactorsList.map Nat.primeCounting).sum = n := by
  have hp : Nat.primeCounting 2 = 1 := by decide
  rw [Nat.prime_two.primeFactorsList_pow]
  simp [hp]

def f (n : ℕ) : ℕ := (n.primeFactorsList.map Nat.primeCounting).sum

def lenFuel : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, m => if m = 0 then 1 else 1 + lenFuel fuel (f m)

def depth (n : ℕ) : ℕ := lenFuel (n+1) n

def tower : ℕ → ℕ
  | 0 => 1
  | j+1 => 2^tower j

lemma f_lt {n : ℕ} (h : n ≠ 0) : f n < n := pseudo_log_lt h
lemma f_pow (n : ℕ) : f (2^n) = n := pseudo_log_pow_two n
lemma f_lower {n : ℕ} (hn : 1 < n) : 0 < f n := by
  by_contra h
  have hz : f n = 0 := by omega
  have hb := pseudo_log_bound n
  change n ≤ 2 ^ f n at hb
  rw [hz] at hb
  simp at hb
  omega

lemma fuel_eq (n fuel : ℕ) (h : n < fuel) : lenFuel fuel n = depth n := by
  induction n using Nat.strong_induction_on generalizing fuel with
  | h n ih =>
    rcases fuel with _ | fuel
    · omega
    by_cases hn : n = 0
    · subst n; simp [depth, lenFuel]
    · have hl := f_lt hn
      have h1 := ih (f n) hl fuel (by omega)
      have h2 := ih (f n) hl n (by omega)
      simp only [depth, lenFuel, if_neg hn] at h1 h2 ⊢
      rw [h1, h2]

lemma depth_zero : depth 0 = 1 := by simp [depth, lenFuel]
lemma depth_step {n : ℕ} (hn : n ≠ 0) : depth n = 1 + depth (f n) := by
  change lenFuel (n + 1) n = 1 + depth (f n)
  simp only [lenFuel, if_neg hn]
  rw [fuel_eq (f n) n (f_lt hn)]

lemma depth_one : depth 1 = 2 := by
  have hf : f 1 = 0 := by simp [f]
  rw [depth_step (by decide), hf, depth_zero]

lemma tower_pos (k : ℕ) : 0 < tower k := by
  cases k with
  | zero => simp [tower]
  | succ k => simp [tower]

lemma tower_depth (k : ℕ) : depth (tower k) = k + 2 := by
  induction k with
  | zero => simp [tower, depth_one]
  | succ k ih =>
    rw [tower, depth_step (by simp), f_pow, ih]
    omega

lemma depth_pos (n : ℕ) : 0 < depth n := by
  cases n with
  | zero => simp [depth_zero]
  | succ n => simp [depth, lenFuel]

lemma depth_ge_two {n : ℕ} (hn : 0 < n) : 2 ≤ depth n := by
  rw [depth_step (by omega)]
  have := depth_pos (f n)
  omega

lemma depth_bound {n : ℕ} (hn : 0 < n) : n ≤ tower (depth n - 2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · simp [h1, depth_one, tower]
    · have hgt : 1 < n := by omega
      have hflt := f_lt (by omega : n ≠ 0)
      have hfpos := f_lower hgt
      have hrec := ih (f n) hflt hfpos
      have hdepth := depth_step (by omega : n ≠ 0)
      have hfdepth := depth_ge_two hfpos
      have heq : depth n - 2 = (depth (f n) - 2) + 1 := by omega
      have hn_bound := pseudo_log_bound n
      change n ≤ 2 ^ f n at hn_bound
      calc
        n ≤ 2 ^ f n := hn_bound
        _ ≤ 2 ^ tower (depth (f n) - 2) := Nat.pow_le_pow_right (by decide) hrec
        _ = tower (depth n - 2) := by rw [heq, tower]

lemma main82 : ∀ k : ℕ, 2 ≤ k →
    depth (tower (k - 2)) = k ∧ ∀ n : ℕ, 1 ≤ n → depth n = k → n ≤ tower (k - 2) := by
  intro k hk
  constructor
  · rw [tower_depth]; omega
  · intro n hn heq
    simpa [heq] using depth_bound hn


theorem OMA.solution : type_of% @OMA.S_oeis_a082090.main := by
  have hfuel : ∀ i n, OMA.S_oeis_a082090.lenFuel i n = lenFuel i n := by
    intro i
    induction i with
    | zero => intro n; rfl
    | succ i ih =>
      intro n
      simp only [OMA.S_oeis_a082090.lenFuel, lenFuel, OMA.S_oeis_a082090.A056239, f, ih]
  have htower : ∀ i, OMA.S_oeis_a082090.tower i = tower i := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => simp [OMA.S_oeis_a082090.tower, tower, ih]
  simpa only [OMA.S_oeis_a082090.A082090, hfuel, htower, depth] using main82

