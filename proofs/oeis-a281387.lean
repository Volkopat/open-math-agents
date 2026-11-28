import OMAStatements.S_oeis_a281387

-- Problem: A281387: Pairs (x, y) of relatively prime positive integers such that (x^2 - 5)/y and (y^2 - 5)/x are both positive integers.
-- Upstream: formal-conjectures statements/oeis-a281387.lean:0 (declaration OMA.S_oeis_a281387.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let c be 1, 4, 11, 29, ... with c(m+2) = 3 c(m+1) - c(m). Then
-- c(m+1)^2 + c(m)^2 = 3 c(m) c(m+1) + 5 and c(m+1)^2 - 5 = c(m) c(m+2), so every pair
-- (c(m+1), c(m+2)) is a solution (coprime, since a common divisor divides 5 and c(m) mod 5 is 1 or 4).
-- Conversely, for a solution (x, y) with x < y, coprimality gives xy | x^2 + y^2 - 5, so
-- x^2 + y^2 = k x y + 5, and Vieta jumping (x, y) -> ((x^2 - 5)/y, x) descends to (1, 4), which
-- forces k = 3 and (x, y) = (c(m+1), c(m+2)). So xs m = c(m+1), ys m = c(m+2),
-- a(n) = c(n/2 + 1), and the recurrence and the g.f. follow.

/-- `Nat.nth` of a predicate whose set is the range of a strictly monotone function. -/
theorem a281387_nth (p : ℕ → Prop) (f : ℕ → ℕ) (hf : StrictMono f)
    (hp : ∀ k, p k ↔ ∃ i, f i = k) (n : ℕ) : Nat.nth p n = f n := by
  have hinf : (Set.ofPred p).Infinite :=
    Set.infinite_of_injective_forall_mem hf.injective (fun i => (hp (f i)).2 ⟨i, rfl⟩)
  have h := Nat.nth_comp_of_strictMono (p := p) (n := n) hf (fun k hk => (hp k).1 hk)
    (fun hfi => absurd hfi hinf)
  have h3 : Nat.nth (fun i => p (f i)) n = n :=
    Nat.nth_of_forall (fun i _ => (hp (f i)).2 ⟨i, rfl⟩)
  rw [h3] at h
  exact h.symm

/-- Vieta jumping: the solutions of x^2 + y^2 = k x y + 5 with 0 < x < y and k > 0 are
k = 3 and consecutive terms of c. -/
theorem a281387_desc (c : ℕ → ℕ) (hc0 : c 0 = 1) (hc1 : c 1 = 4)
    (hcr : ∀ n, c (n + 2) + c n = 3 * c (n + 1)) :
    ∀ x y k : ℕ, 0 < x → x < y → 0 < k → x ^ 2 + y ^ 2 = k * x * y + 5 →
      k = 3 ∧ ∃ m, x = c m ∧ y = c (m + 1) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro y k hx hxy hk h
    rcases (show x = 1 ∨ x = 2 ∨ 3 ≤ x by omega) with rfl | rfl | hx3
    · have e : y * y = k * y + 4 := by linarith
      have hky : k < y := by
        by_contra hc
        have p1 : y * y ≤ k * y := Nat.mul_le_mul_right y (not_lt.mp hc)
        omega
      have hy4 : y ≤ 4 := by
        have p1 : (k + 1) * y ≤ y * y := Nat.mul_le_mul_right y (show k + 1 ≤ y by omega)
        linarith
      interval_cases y
      · exfalso
        omega
      · exfalso
        omega
      · exact ⟨by omega, 0, hc0.symm, hc1.symm⟩
    · exfalso
      have e : y * y = 2 * k * y + 1 := by linarith
      have hky : 2 * k < y := by
        by_contra hc
        have p1 : y * y ≤ 2 * k * y := Nat.mul_le_mul_right y (not_lt.mp hc)
        omega
      have p2 : (2 * k + 1) * y ≤ y * y := Nat.mul_le_mul_right y (show 2 * k + 1 ≤ y by omega)
      linarith
    · have h1 : y < k * x := by
        by_contra hc
        have hc' : k * x ≤ y := not_lt.mp hc
        have p1 : k * x * y ≤ y * y := Nat.mul_le_mul_right y hc'
        have p2 : 3 * 3 ≤ x * x := Nat.mul_le_mul hx3 hx3
        linarith
      obtain ⟨z, hz⟩ : ∃ z, z + y = k * x := ⟨k * x - y, by omega⟩
      have e1 : (z + y) * y = k * x * y := by rw [hz]
      have hzy : z * y + 5 = x ^ 2 := by linarith
      have p3 : 3 * 3 ≤ x * x := Nat.mul_le_mul hx3 hx3
      have hz0 : 0 < z := by
        rcases Nat.eq_zero_or_pos z with h0 | h0
        · rw [h0, Nat.zero_mul] at hzy
          linarith
        · exact h0
      have hzx : z < x := by
        by_contra hc
        have hle : x ≤ z := not_lt.mp hc
        have p1 : x * y ≤ z * y := Nat.mul_le_mul_right y hle
        have p2 : x * x ≤ x * y := Nat.mul_le_mul_left x hxy.le
        linarith
      have e2 : (z + y) * z = k * x * z := by rw [hz]
      have hnew : z ^ 2 + x ^ 2 = k * z * x + 5 := by linarith
      obtain ⟨hk3, m, hzm, hxm⟩ := ih z hzx x k hz0 hzx hk hnew
      refine ⟨hk3, m + 1, hxm, ?_⟩
      have hr := hcr m
      rw [hk3, hzm, hxm] at hz
      show y = c (m + 2)
      omega

set_option maxHeartbeats 400000 in
open OMA.S_oeis_a281387 in
theorem OMA.solution : type_of% @OMA.S_oeis_a281387.main := by
  obtain ⟨c, d, hc0, hd0, hcs, hds⟩ : ∃ c d : ℕ → ℕ, c 0 = 1 ∧ d 0 = 3 ∧
      (∀ n, c (n + 1) = c n + d n) ∧ (∀ n, d (n + 1) = c n + 2 * d n) :=
    ⟨fun n => (Nat.rec (motive := fun _ => ℕ × ℕ) ((1, 3) : ℕ × ℕ)
        (fun _ p => (p.1 + p.2, p.1 + 2 * p.2)) n).1,
      fun n => (Nat.rec (motive := fun _ => ℕ × ℕ) ((1, 3) : ℕ × ℕ)
        (fun _ p => (p.1 + p.2, p.1 + 2 * p.2)) n).2,
      rfl, rfl, fun _ => rfl, fun _ => rfl⟩
  have hc1 : c 1 = 4 := by
    have h : c 1 = c 0 + d 0 := hcs 0
    rw [h, hc0, hd0]
  have hcr : ∀ n, c (n + 2) + c n = 3 * c (n + 1) := by
    intro n
    show c (n + 1 + 1) + c n = 3 * c (n + 1)
    rw [hcs (n + 1), hds n, hcs n]
    ring
  have hc2 : c 2 = 11 := by
    have h : c 2 + c 0 = 3 * c 1 := hcr 0
    omega
  have hc3 : c 3 = 29 := by
    have h : c 3 + c 1 = 3 * c 2 := hcr 1
    omega
  have hdpos : ∀ n, 0 < d n := by
    intro n
    induction n with
    | zero => rw [hd0]; norm_num
    | succ k ih => rw [hds k]; omega
  have hcm : StrictMono c := strictMono_nat_of_lt_succ (fun n => by
    rw [hcs n]
    have := hdpos n
    omega)
  have hx4 : ∀ m, 4 ≤ c (m + 1) := by
    intro m
    have h := hcm.monotone (show 1 ≤ m + 1 by omega)
    rw [hc1] at h
    exact h
  have hH3 : ∀ n, (c (n + 1) : ℤ) ^ 2 + (c n : ℤ) ^ 2 = 3 * (c n : ℤ) * (c (n + 1) : ℤ) + 5 := by
    intro n
    induction n with
    | zero =>
      show (c 1 : ℤ) ^ 2 + (c 0 : ℤ) ^ 2 = 3 * (c 0 : ℤ) * (c 1 : ℤ) + 5
      rw [hc0, hc1]
      norm_num
    | succ k ih =>
      have h2 : (c (k + 2) : ℤ) + (c k : ℤ) = 3 * (c (k + 1) : ℤ) := by exact_mod_cast hcr k
      show (c (k + 2) : ℤ) ^ 2 + (c (k + 1) : ℤ) ^ 2 =
        3 * (c (k + 1) : ℤ) * (c (k + 2) : ℤ) + 5
      linear_combination ih + ((c (k + 2) : ℤ) - (c k : ℤ)) * h2
  have hH3N : ∀ n, c (n + 1) ^ 2 + c n ^ 2 = 3 * c n * c (n + 1) + 5 := by
    intro n
    exact_mod_cast hH3 n
  have hsq : ∀ n, c (n + 1) ^ 2 = c n * c (n + 2) + 5 := by
    intro n
    have h1 := hH3 n
    have h2 : (c (n + 2) : ℤ) + (c n : ℤ) = 3 * (c (n + 1) : ℤ) := by exact_mod_cast hcr n
    have hz : (c (n + 1) : ℤ) ^ 2 = (c n : ℤ) * (c (n + 2) : ℤ) + 5 := by
      linear_combination h1 - (c n : ℤ) * h2
    exact_mod_cast hz
  have hmod2 : ∀ n, (c n % 5 = 1 ∧ c (n + 1) % 5 = 4) ∨ (c n % 5 = 4 ∧ c (n + 1) % 5 = 1) := by
    intro n
    induction n with
    | zero =>
      show (c 0 % 5 = 1 ∧ c 1 % 5 = 4) ∨ (c 0 % 5 = 4 ∧ c 1 % 5 = 1)
      rw [hc0, hc1]
      decide
    | succ k ih =>
      have h := hcr k
      show (c (k + 1) % 5 = 1 ∧ c (k + 2) % 5 = 4) ∨ (c (k + 1) % 5 = 4 ∧ c (k + 2) % 5 = 1)
      omega
  have hSol : ∀ x y, Sol x y ↔ (0 < x ∧ 0 < y ∧ Nat.Coprime x y ∧ 5 < x ^ 2 ∧ y ∣ x ^ 2 - 5 ∧
      5 < y ^ 2 ∧ x ∣ y ^ 2 - 5) := fun _ _ => Iff.rfl
  -- every pair (c (m+1), c (m+2)) is a solution
  have hfwd : ∀ m, c (m + 1) < c (m + 2) ∧ Sol (c (m + 1)) (c (m + 2)) := by
    intro m
    have hxy : c (m + 1) < c (m + 2) := hcm (by omega)
    have h4 := hx4 m
    have hcop : Nat.Coprime (c (m + 1)) (c (m + 2)) := by
      have hxy2 : c (m + 2) ^ 2 + c (m + 1) ^ 2 = 3 * c (m + 1) * c (m + 2) + 5 := hH3N (m + 1)
      have hg1 : Nat.gcd (c (m + 1)) (c (m + 2)) ∣ c (m + 2) ^ 2 + c (m + 1) ^ 2 :=
        dvd_add (dvd_pow (Nat.gcd_dvd_right _ _) two_ne_zero)
          (dvd_pow (Nat.gcd_dvd_left _ _) two_ne_zero)
      have hg2 : Nat.gcd (c (m + 1)) (c (m + 2)) ∣ 3 * c (m + 1) * c (m + 2) :=
        Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) _
      rw [hxy2] at hg1
      have hg5 : Nat.gcd (c (m + 1)) (c (m + 2)) ∣ 5 := (Nat.dvd_add_right hg2).mp hg1
      rcases (Nat.dvd_prime Nat.prime_five).mp hg5 with h | h
      · exact h
      · exfalso
        have h5 : 5 ∣ c (m + 1) := by
          rw [← h]
          exact Nat.gcd_dvd_left _ _
        have hm := hmod2 (m + 1)
        omega
    have hdy : c (m + 2) ∣ c (m + 1) ^ 2 - 5 := by
      rw [hsq m, Nat.add_sub_cancel]
      exact dvd_mul_left _ _
    have hdx : c (m + 1) ∣ c (m + 2) ^ 2 - 5 := by
      have hs2 : c (m + 2) ^ 2 = c (m + 1) * c (m + 3) + 5 := hsq (m + 1)
      rw [hs2, Nat.add_sub_cancel]
      exact dvd_mul_right _ _
    have q1 : 4 * 4 ≤ c (m + 1) * c (m + 1) := Nat.mul_le_mul h4 h4
    have q2 : 5 * 5 ≤ c (m + 2) * c (m + 2) :=
      Nat.mul_le_mul (show 5 ≤ c (m + 2) by omega) (show 5 ≤ c (m + 2) by omega)
    have hx5 : 5 < c (m + 1) ^ 2 := by
      rw [pow_two]
      omega
    have hy5 : 5 < c (m + 2) ^ 2 := by
      rw [pow_two]
      omega
    exact ⟨hxy, (hSol _ _).2 ⟨by omega, by omega, hcop, hx5, hdy, hy5, hdx⟩⟩
  -- every solution pair with x < y is a pair (c (m+1), c (m+2))
  have hbwd : ∀ x y, x < y → Sol x y → ∃ m, x = c (m + 1) ∧ y = c (m + 2) := by
    intro x y hxy hS
    obtain ⟨hx0, -, hcop, hx5, hdy, hy5, hdx⟩ := (hSol x y).1 hS
    obtain ⟨u, hu⟩ := hdy
    obtain ⟨v, hv⟩ := hdx
    have hu' : x ^ 2 = y * u + 5 := by omega
    have hv' : y ^ 2 = x * v + 5 := by omega
    have hM : x * (x + v) = y * (u + y) := by
      have h1 : (x : ℤ) ^ 2 = (y : ℤ) * (u : ℤ) + 5 := by exact_mod_cast hu'
      have h2 : (y : ℤ) ^ 2 = (x : ℤ) * (v : ℤ) + 5 := by exact_mod_cast hv'
      have h3 : (x : ℤ) * ((x : ℤ) + (v : ℤ)) = (y : ℤ) * ((u : ℤ) + (y : ℤ)) := by
        linear_combination h1 - h2
      exact_mod_cast h3
    have hd : x * y ∣ x * (x + v) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (dvd_mul_right x (x + v))
        (by rw [hM]; exact dvd_mul_right y (u + y))
    obtain ⟨k, hk⟩ := hd
    have hkey : x ^ 2 + y ^ 2 = k * x * y + 5 := by
      have h1 : (x : ℤ) * ((x : ℤ) + (v : ℤ)) = (x : ℤ) * (y : ℤ) * (k : ℤ) := by exact_mod_cast hk
      have h2 : (y : ℤ) ^ 2 = (x : ℤ) * (v : ℤ) + 5 := by exact_mod_cast hv'
      have h3 : (x : ℤ) ^ 2 + (y : ℤ) ^ 2 = (k : ℤ) * (x : ℤ) * (y : ℤ) + 5 := by
        linear_combination h1 + h2
      exact_mod_cast h3
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, Nat.zero_mul, Nat.zero_mul] at hkey
        omega
      · exact h0
    obtain ⟨-, m, hxm, hym⟩ := a281387_desc c hc0 hc1 hcr x y k hx0 hxy hk0 hkey
    rcases m with _ | m
    · exfalso
      rw [hc0] at hxm
      subst hxm
      norm_num at hx5
    · exact ⟨m, hxm, hym⟩
  have hxs : ∀ m, xs m = c (m + 1) := by
    intro m
    show Nat.nth (fun x => ∃ y, x < y ∧ Sol x y) m = c (m + 1)
    have hp : ∀ k, (∃ y, k < y ∧ Sol k y) ↔ ∃ i, c (i + 1) = k := by
      intro k
      constructor
      · rintro ⟨y, hky, hS⟩
        obtain ⟨j, hj, -⟩ := hbwd k y hky hS
        exact ⟨j, hj.symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨c (i + 2), (hfwd i).1, (hfwd i).2⟩
    exact a281387_nth (fun x => ∃ y, x < y ∧ Sol x y) (fun i => c (i + 1))
      (fun i j hij => hcm (show i + 1 < j + 1 by omega)) hp m
  have hys : ∀ m, ys m = c (m + 2) := by
    intro m
    have hS : ys m = sInf {y | xs m < y ∧ Sol (xs m) y} := rfl
    rw [hS, hxs m]
    have hmem : c (m + 2) ∈ {y | c (m + 1) < y ∧ Sol (c (m + 1)) y} := hfwd m
    have huniq : ∀ y ∈ {y | c (m + 1) < y ∧ Sol (c (m + 1)) y}, y = c (m + 2) := by
      intro y hy
      have hy' : c (m + 1) < y ∧ Sol (c (m + 1)) y := hy
      obtain ⟨j, hj1, hj2⟩ := hbwd (c (m + 1)) y hy'.1 hy'.2
      have hjm : m + 1 = j + 1 := hcm.injective hj1
      obtain rfl : j = m := by omega
      exact hj2
    exact huniq _ (Nat.sInf_mem ⟨_, hmem⟩)
  have ha : ∀ n, 1 ≤ n → a n = c (n / 2 + 1) := by
    intro n hn
    have hdef : a n = if n % 2 = 1 then xs (n / 2) else ys (n / 2 - 1) := rfl
    rw [hdef]
    split_ifs with h
    · rw [hxs]
    · rw [hys]
      congr 1
      omega
  have hrec : ∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ) := by
    intro n hn
    rw [ha n (by omega), ha (n - 2) (by omega), ha (n - 4) (by omega)]
    have e1 : n / 2 + 1 = (n - 4) / 2 + 1 + 2 := by omega
    have e2 : (n - 2) / 2 + 1 = (n - 4) / 2 + 1 + 1 := by omega
    rw [e1, e2]
    have h := hcr ((n - 4) / 2 + 1)
    omega
  refine ⟨hrec, ?_⟩
  have a1 : a 1 = 4 := by
    rw [ha 1 (by norm_num)]
    norm_num [hc1]
  have a2 : a 2 = 11 := by
    rw [ha 2 (by norm_num)]
    norm_num [hc2]
  have a3 : a 3 = 11 := by
    rw [ha 3 (by norm_num)]
    norm_num [hc2]
  have a4 : a 4 = 29 := by
    rw [ha 4 (by norm_num)]
    norm_num [hc3]
  have hrecQ : ∀ k, (a (k + 5) : ℚ) = 3 * (a (k + 3) : ℚ) - (a (k + 1) : ℚ) := by
    intro k
    have h := hrec (k + 5) (by omega)
    rw [show k + 5 - 2 = k + 3 by omega, show k + 5 - 4 = k + 1 by omega] at h
    have h' : ((a (k + 5) : ℤ) : ℚ) = ((3 * (a (k + 3) : ℤ) - (a (k + 1) : ℤ) : ℤ) : ℚ) := by
      rw [h]
    push_cast at h'
    exact h'
  have e : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (PowerSeries.X ^ 4 - 3 * PowerSeries.X ^ 2 + 1) =
      PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * PowerSeries.X ^ 4
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 *
          (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * PowerSeries.X ^ 2)
        + PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3]
    ring
  have e2 : (PowerSeries.X *
      (-4 * PowerSeries.X ^ 3 - PowerSeries.X ^ 2 + 11 * PowerSeries.X + 4) : PowerSeries ℚ) =
      PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 11
        + PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4
        - PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 - PowerSeries.X ^ 3 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 11,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
    ring
  rw [e, e2]
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m
    · norm_num
    · norm_num [a1]
    · norm_num [a2]
    · norm_num [a1, a3]
    · norm_num [a2, a4]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
    rw [if_pos (show 4 ≤ k + 5 by omega), if_pos (show 2 ≤ k + 5 by omega),
      show k + 5 - 4 = k + 1 by omega, show k + 5 - 2 = k + 3 by omega,
      if_neg (show ¬ (k + 1 = 0) by omega), if_neg (show ¬ (k + 3 = 0) by omega),
      if_neg (show ¬ (k + 5 = 0) by omega), if_neg (show ¬ (k + 5 = 2) by omega),
      if_neg (show ¬ (k + 5 = 1) by omega), if_neg (show ¬ (k + 5 = 4) by omega),
      if_neg (show ¬ (k + 5 = 3) by omega), hrecQ k]
    ring
