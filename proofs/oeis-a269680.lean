import OMAStatements.S_oeis_a269680

-- Problem: A269680: Number of length-5 0..n arrays with no repeated value differing from the previous repeated value by other than plus or minus one modulo n+1.
-- Upstream: formal-conjectures statements/oeis-a269680.lean:0 (declaration OMA.S_oeis_a269680.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: on 0..n, R n u v says v = u + 1, u = v + 1, or {u, v} = {0, n}; for n >= 2 no u
-- is related to itself and every u to exactly two v. Summing out x5, x4, x1, x3, x2 in turn
-- (the count over x5 depends only on whether x5 = x4) gives, for n >= 2, the counts
-- D = n^2 + 2n (x1 /= x2 /= x3), n^2 + 2 + (n - 1)[R x2 x3] (x1 = x2 /= x3), n^2 + 2
-- (x1 /= x2 = x3), 0 (x1 = x2 = x3), then K(x2) = n^4 + 4n^3 + 6n - 2 and
-- a(n) = n^5 + 5n^4 + 4n^3 + 6n^2 + 4n - 2; a(1) = 14 by evaluation. The recurrence for n > 7
-- and the g.f. follow from these values.

set_option maxHeartbeats 2000000 in
open OMA.S_oeis_a269680 in
theorem OMA.solution : type_of% @OMA.S_oeis_a269680.main := by
  have Lc : ∀ n c : ℕ, ∑ _x ∈ Finset.range (n + 1), c = (n + 1) * c := by
    intro n c
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have Leq : ∀ n e c : ℕ, e ≤ n →
      ∑ x ∈ Finset.range (n + 1), (if x = e then c else 0) = c := by
    intro n e c he
    rw [Finset.sum_ite_eq']
    exact if_pos (Finset.mem_range.mpr (by omega))
  -- R on 0..n in linear form
  have Rl : ∀ n u v : ℕ, u ≤ n → v ≤ n →
      (R n u v ↔ (v = u + 1 ∨ u = v + 1 ∨ (u = 0 ∧ v = n) ∨ (u = n ∧ v = 0))) := by
    intro n u v hu hv
    have e1 : v % (n + 1) = v := Nat.mod_eq_of_lt (by omega)
    have e2 : u % (n + 1) = u := Nat.mod_eq_of_lt (by omega)
    have e3 : (u + 1) % (n + 1) = if u = n then 0 else u + 1 := by
      split_ifs with h
      · rw [h, Nat.mod_self]
      · exact Nat.mod_eq_of_lt (by omega)
    have e4 : (v + 1) % (n + 1) = if v = n then 0 else v + 1 := by
      split_ifs with h
      · rw [h, Nat.mod_self]
      · exact Nat.mod_eq_of_lt (by omega)
    unfold R Nat.ModEq
    rw [e1, e2, e3, e4]
    split_ifs <;> omega
  -- for n >= 2 every u in 0..n is related to exactly two v in 0..n
  have CR : ∀ n u : ℕ, 2 ≤ n → u ≤ n →
      ∑ v ∈ Finset.range (n + 1), (if R n u v then 1 else 0) = 2 := by
    intro n u hn hu
    obtain ⟨p, hp⟩ : ∃ p, (u = 0 → p = n) ∧ (u ≠ 0 → p + 1 = u) := by
      by_cases h : u = 0
      · exact ⟨n, fun _ => rfl, fun h' => absurd h h'⟩
      · exact ⟨u - 1, fun h' => absurd h' h, fun _ => by omega⟩
    obtain ⟨q, hq⟩ : ∃ q, (u = n → q = 0) ∧ (u ≠ n → q = u + 1) := by
      by_cases h : u = n
      · exact ⟨0, fun _ => rfl, fun h' => absurd h h'⟩
      · exact ⟨u + 1, fun h' => absurd h' h, fun _ => rfl⟩
    have hpn : p ≤ n := by omega
    have hqn : q ≤ n := by omega
    have e : ∑ v ∈ Finset.range (n + 1), (if R n u v then 1 else 0) =
        ∑ v ∈ Finset.range (n + 1), ((if v = p then 1 else 0) + (if v = q then 1 else 0)) := by
      refine Finset.sum_congr rfl (fun v hv => ?_)
      rw [Finset.mem_range] at hv
      by_cases h : R n u v
      · rw [if_pos h]
        rw [Rl n u v hu (by omega)] at h
        split_ifs <;> omega
      · rw [if_neg h]
        rw [Rl n u v hu (by omega)] at h
        split_ifs <;> omega
    have s1 := Leq n p 1 hpn
    have s2 := Leq n q 1 hqn
    rw [e, Finset.sum_add_distrib]
    omega
  -- summing a pointwise identity with an R-indicator and an indicator at one point
  have G2 : ∀ (n : ℕ) (g : ℕ → ℕ) (u e D1 c A B C : ℕ), 2 ≤ n → u ≤ n → e ≤ n →
      (∀ x, x ≤ n → g x + D1 * (if R n u x then 1 else 0) + (if x = e then c else 0) =
        A + B * (if R n u x then 1 else 0) + (if x = e then C else 0)) →
      ∑ x ∈ Finset.range (n + 1), g x + 2 * D1 + c = (n + 1) * A + 2 * B + C := by
    intro n g u e D1 c A B C hn hu he h
    have h1 : ∑ x ∈ Finset.range (n + 1),
        (g x + D1 * (if R n u x then 1 else 0) + (if x = e then c else 0)) =
        ∑ x ∈ Finset.range (n + 1),
        (A + B * (if R n u x then 1 else 0) + (if x = e then C else 0)) :=
      Finset.sum_congr rfl (fun x hx => h x (by rw [Finset.mem_range] at hx; omega))
    simp only [Finset.sum_add_distrib] at h1
    rw [← Finset.mul_sum, ← Finset.mul_sum, CR n u hn hu, Leq n e c he, Leq n e C he,
      Lc n A] at h1
    linarith
  -- the value of the indicator of ok, through the linear form of R
  have OKV : ∀ n x1 x2 x3 x4 x5 q : ℕ, x1 ≤ n → x2 ≤ n → x3 ≤ n → x4 ≤ n →
      ((((x1 = x2 → x2 = x3 →
          (x2 = x1 + 1 ∨ x1 = x2 + 1 ∨ (x1 = 0 ∧ x2 = n) ∨ (x1 = n ∧ x2 = 0))) ∧
        (x2 = x3 → x3 = x4 →
          (x3 = x2 + 1 ∨ x2 = x3 + 1 ∨ (x2 = 0 ∧ x3 = n) ∨ (x2 = n ∧ x3 = 0))) ∧
        (x3 = x4 → x4 = x5 →
          (x4 = x3 + 1 ∨ x3 = x4 + 1 ∨ (x3 = 0 ∧ x4 = n) ∨ (x3 = n ∧ x4 = 0)))) ∧
       ((x1 = x2 → x2 ≠ x3 → x3 = x4 →
          (x3 = x1 + 1 ∨ x1 = x3 + 1 ∨ (x1 = 0 ∧ x3 = n) ∨ (x1 = n ∧ x3 = 0))) ∧
        (x2 = x3 → x3 ≠ x4 → x4 = x5 →
          (x4 = x2 + 1 ∨ x2 = x4 + 1 ∨ (x2 = 0 ∧ x4 = n) ∨ (x2 = n ∧ x4 = 0))) ∧
        (x1 = x2 → x2 ≠ x3 → x3 ≠ x4 → x4 = x5 →
          (x4 = x1 + 1 ∨ x1 = x4 + 1 ∨ (x1 = 0 ∧ x4 = n) ∨ (x1 = n ∧ x4 = 0))))) → q = 1) →
      (¬ (((x1 = x2 → x2 = x3 →
          (x2 = x1 + 1 ∨ x1 = x2 + 1 ∨ (x1 = 0 ∧ x2 = n) ∨ (x1 = n ∧ x2 = 0))) ∧
        (x2 = x3 → x3 = x4 →
          (x3 = x2 + 1 ∨ x2 = x3 + 1 ∨ (x2 = 0 ∧ x3 = n) ∨ (x2 = n ∧ x3 = 0))) ∧
        (x3 = x4 → x4 = x5 →
          (x4 = x3 + 1 ∨ x3 = x4 + 1 ∨ (x3 = 0 ∧ x4 = n) ∨ (x3 = n ∧ x4 = 0)))) ∧
       ((x1 = x2 → x2 ≠ x3 → x3 = x4 →
          (x3 = x1 + 1 ∨ x1 = x3 + 1 ∨ (x1 = 0 ∧ x3 = n) ∨ (x1 = n ∧ x3 = 0))) ∧
        (x2 = x3 → x3 ≠ x4 → x4 = x5 →
          (x4 = x2 + 1 ∨ x2 = x4 + 1 ∨ (x2 = 0 ∧ x4 = n) ∨ (x2 = n ∧ x4 = 0))) ∧
        (x1 = x2 → x2 ≠ x3 → x3 ≠ x4 → x4 = x5 →
          (x4 = x1 + 1 ∨ x1 = x4 + 1 ∨ (x1 = 0 ∧ x4 = n) ∨ (x1 = n ∧ x4 = 0))))) → q = 0) →
      (if ok n x1 x2 x3 x4 x5 then 1 else 0) = q := by
    intro n x1 x2 x3 x4 x5 q b1 b2 b3 b4 hL hN
    have hk : ok n x1 x2 x3 x4 x5 ↔
        (((x1 = x2 → x2 = x3 →
          (x2 = x1 + 1 ∨ x1 = x2 + 1 ∨ (x1 = 0 ∧ x2 = n) ∨ (x1 = n ∧ x2 = 0))) ∧
        (x2 = x3 → x3 = x4 →
          (x3 = x2 + 1 ∨ x2 = x3 + 1 ∨ (x2 = 0 ∧ x3 = n) ∨ (x2 = n ∧ x3 = 0))) ∧
        (x3 = x4 → x4 = x5 →
          (x4 = x3 + 1 ∨ x3 = x4 + 1 ∨ (x3 = 0 ∧ x4 = n) ∨ (x3 = n ∧ x4 = 0)))) ∧
       ((x1 = x2 → x2 ≠ x3 → x3 = x4 →
          (x3 = x1 + 1 ∨ x1 = x3 + 1 ∨ (x1 = 0 ∧ x3 = n) ∨ (x1 = n ∧ x3 = 0))) ∧
        (x2 = x3 → x3 ≠ x4 → x4 = x5 →
          (x4 = x2 + 1 ∨ x2 = x4 + 1 ∨ (x2 = 0 ∧ x4 = n) ∨ (x2 = n ∧ x4 = 0))) ∧
        (x1 = x2 → x2 ≠ x3 → x3 ≠ x4 → x4 = x5 →
          (x4 = x1 + 1 ∨ x1 = x4 + 1 ∨ (x1 = 0 ∧ x4 = n) ∨ (x1 = n ∧ x4 = 0))))) := by
      unfold ok
      rw [Rl n x1 x2 b1 b2, Rl n x2 x3 b2 b3, Rl n x3 x4 b3 b4, Rl n x1 x3 b1 b3,
        Rl n x2 x4 b2 b4, Rl n x1 x4 b1 b4]
    by_cases h : ok n x1 x2 x3 x4 x5
    · rw [if_pos h]
      exact (hL (hk.mp h)).symm
    · rw [if_neg h]
      exact (hN (fun hl => h (hk.mpr hl))).symm
  -- the count over x5
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ, ∀ n x1 x2 x3 x4, E n x1 x2 x3 x4 =
      ∑ x5 ∈ Finset.range (n + 1), (if ok n x1 x2 x3 x4 x5 then 1 else 0) :=
    ⟨_, fun _ _ _ _ _ => rfl⟩
  have hEv : ∀ (n x1 x2 x3 x4 p q w : ℕ), x4 ≤ n →
      (∀ x5, x5 ≤ n → x5 ≠ x4 → (if ok n x1 x2 x3 x4 x5 then 1 else 0) = q) →
      (if ok n x1 x2 x3 x4 x4 then 1 else 0) = w → w + p = q →
      E n x1 x2 x3 x4 + p = (n + 1) * q := by
    intro n x1 x2 x3 x4 p q w hx4 h1 hw hwq
    have hm : x4 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have e1 : ∑ x5 ∈ (Finset.range (n + 1)).erase x4, (if ok n x1 x2 x3 x4 x5 then 1 else 0) =
        ∑ _x5 ∈ (Finset.range (n + 1)).erase x4, q := by
      refine Finset.sum_congr rfl (fun x5 hx5 => h1 x5 ?_ (Finset.ne_of_mem_erase hx5))
      have hx5' := Finset.mem_of_mem_erase hx5
      rw [Finset.mem_range] at hx5'
      omega
    rw [Finset.sum_const, Finset.card_erase_of_mem hm, Finset.card_range, smul_eq_mul,
      Nat.add_sub_cancel] at e1
    rw [hE, ← Finset.add_sum_erase (Finset.range (n + 1)) _ hm, e1, hw]
    linarith
  -- the count over x4 and x5, by the pattern of x1, x2, x3 (for n >= 2)
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℕ → ℕ → ℕ → ℕ, ∀ n x2 x3 x1, D n x2 x3 x1 =
      ∑ x4 ∈ Finset.range (n + 1), E n x1 x2 x3 x4 := ⟨_, fun _ _ _ _ => rfl⟩
  have DA : ∀ n x2 x3 x1, 2 ≤ n → x1 ≤ n → x2 ≤ n → x3 ≤ n → x1 ≠ x2 → x2 ≠ x3 →
      D n x2 x3 x1 = n * n + 2 * n := by
    intro n x2 x3 x1 hn b1 b2 b3 h12 h23
    have hp : ∀ x4, x4 ≤ n → E n x1 x2 x3 x4 + 0 * (if R n 0 x4 then 1 else 0) +
        (if x4 = x3 then 1 else 0) = n + 1 + 0 * (if R n 0 x4 then 1 else 0) +
        (if x4 = x3 then 0 else 0) := by
      intro x4 hx4
      by_cases h : x4 = x3
      · have := hEv n x1 x2 x3 x4 1 1 0 hx4
          (fun x5 _ hx5 => OKV n x1 x2 x3 x4 x5 1 b1 b2 b3 hx4 (fun _ => rfl)
            (fun hl => by omega))
          (OKV n x1 x2 x3 x4 x4 0 b1 b2 b3 hx4 (fun hl => by omega) (fun _ => rfl))
          (by norm_num)
        split_ifs <;> omega
      · have := hEv n x1 x2 x3 x4 0 1 1 hx4
          (fun x5 _ hx5 => OKV n x1 x2 x3 x4 x5 1 b1 b2 b3 hx4 (fun _ => rfl)
            (fun hl => by omega))
          (OKV n x1 x2 x3 x4 x4 1 b1 b2 b3 hx4 (fun _ => rfl) (fun hl => by omega))
          (by norm_num)
        split_ifs <;> omega
    have hG := G2 n (E n x1 x2 x3) 0 x3 0 1 (n + 1) 0 0 hn (by omega) b3 hp
    rw [hD]
    linarith
  have DB : ∀ n x2 x3 x1, 2 ≤ n → x1 ≤ n → x2 ≤ n → x3 ≤ n → x1 = x2 → x2 ≠ x3 →
      D n x2 x3 x1 + n + (if R n x1 x3 then 1 else 0) =
        n * n + n + 2 + n * (if R n x1 x3 then 1 else 0) := by
    intro n x2 x3 x1 hn b1 b2 b3 h12 h23
    have hp : ∀ x4, x4 ≤ n → E n x1 x2 x3 x4 + 0 * (if R n x1 x4 then 1 else 0) +
        (if x4 = x3 then n + (if R n x1 x3 then 1 else 0) else 0) =
        n + 1 * (if R n x1 x4 then 1 else 0) +
        (if x4 = x3 then n * (if R n x1 x3 then 1 else 0) else 0) := by
      intro x4 hx4
      by_cases h : x4 = x3
      · by_cases hR : R n x1 x3
        · have hRl := (Rl n x1 x3 b1 b3).mp hR
          have := hEv n x1 x2 x3 x4 1 1 0 hx4
            (fun x5 _ hx5 => OKV n x1 x2 x3 x4 x5 1 b1 b2 b3 hx4 (fun _ => rfl)
              (fun hl => by omega))
            (OKV n x1 x2 x3 x4 x4 0 b1 b2 b3 hx4 (fun hl => by omega) (fun _ => rfl))
            (by norm_num)
          simp only [if_pos h]
          rw [h] at this ⊢
          simp only [if_pos hR]
          omega
        · have hRl : ¬ (x3 = x1 + 1 ∨ x1 = x3 + 1 ∨ (x1 = 0 ∧ x3 = n) ∨ (x1 = n ∧ x3 = 0)) :=
            fun hl => hR ((Rl n x1 x3 b1 b3).mpr hl)
          have := hEv n x1 x2 x3 x4 0 0 0 hx4
            (fun x5 _ hx5 => OKV n x1 x2 x3 x4 x5 0 b1 b2 b3 hx4 (fun hl => by omega)
              (fun _ => rfl))
            (OKV n x1 x2 x3 x4 x4 0 b1 b2 b3 hx4 (fun hl => by omega) (fun _ => rfl))
            (by norm_num)
          simp only [if_pos h]
          rw [h] at this ⊢
          simp only [if_neg hR]
          omega
      · by_cases hR : R n x1 x4
        · have hRl := (Rl n x1 x4 b1 hx4).mp hR
          have := hEv n x1 x2 x3 x4 0 1 1 hx4
            (fun x5 _ hx5 => OKV n x1 x2 x3 x4 x5 1 b1 b2 b3 hx4 (fun _ => rfl)
              (fun hl => by omega))
            (OKV n x1 x2 x3 x4 x4 1 b1 b2 b3 hx4 (fun _ => rfl) (fun hl => by omega))
            (by norm_num)
          simp only [if_pos hR, if_neg h]
          omega
        · have hRl : ¬ (x4 = x1 + 1 ∨ x1 = x4 + 1 ∨ (x1 = 0 ∧ x4 = n) ∨ (x1 = n ∧ x4 = 0)) :=
            fun hl => hR ((Rl n x1 x4 b1 hx4).mpr hl)
          have := hEv n x1 x2 x3 x4 1 1 0 hx4
            (fun x5 _ hx5 => OKV n x1 x2 x3 x4 x5 1 b1 b2 b3 hx4 (fun _ => rfl)
              (fun hl => by omega))
            (OKV n x1 x2 x3 x4 x4 0 b1 b2 b3 hx4 (fun hl => by omega) (fun _ => rfl))
            (by norm_num)
          simp only [if_neg hR, if_neg h]
          omega
    have hG := G2 n (E n x1 x2 x3) x1 x3 0 (n + (if R n x1 x3 then 1 else 0)) n 1
      (n * (if R n x1 x3 then 1 else 0)) hn b1 b3 hp
    rw [hD]
    linarith
  have DC : ∀ n x2 x3 x1, 2 ≤ n → x1 ≤ n → x2 ≤ n → x3 ≤ n → x1 ≠ x2 → x2 = x3 →
      D n x2 x3 x1 = n * n + 2 := by
    intro n x2 x3 x1 hn b1 b2 b3 h12 h23
    have hp : ∀ x4, x4 ≤ n → E n x1 x2 x3 x4 + 0 * (if R n x2 x4 then 1 else 0) +
        (if x4 = x3 then n else 0) = n + 1 * (if R n x2 x4 then 1 else 0) +
        (if x4 = x3 then 0 else 0) := by
      intro x4 hx4
      by_cases h : x4 = x3
      · have hRn : ¬ R n x2 x4 := by
          rw [Rl n x2 x4 b2 hx4]
          omega
        have := hEv n x1 x2 x3 x4 0 0 0 hx4
          (fun x5 _ hx5 => OKV n x1 x2 x3 x4 x5 0 b1 b2 b3 hx4 (fun hl => by omega)
            (fun _ => rfl))
          (OKV n x1 x2 x3 x4 x4 0 b1 b2 b3 hx4 (fun hl => by omega) (fun _ => rfl))
          (by norm_num)
        simp only [if_neg hRn, if_pos h]
        omega
      · by_cases hR : R n x2 x4
        · have hRl := (Rl n x2 x4 b2 hx4).mp hR
          have := hEv n x1 x2 x3 x4 0 1 1 hx4
            (fun x5 _ hx5 => OKV n x1 x2 x3 x4 x5 1 b1 b2 b3 hx4 (fun _ => rfl)
              (fun hl => by omega))
            (OKV n x1 x2 x3 x4 x4 1 b1 b2 b3 hx4 (fun _ => rfl) (fun hl => by omega))
            (by norm_num)
          simp only [if_pos hR, if_neg h]
          omega
        · have hRl : ¬ (x4 = x2 + 1 ∨ x2 = x4 + 1 ∨ (x2 = 0 ∧ x4 = n) ∨ (x2 = n ∧ x4 = 0)) :=
            fun hl => hR ((Rl n x2 x4 b2 hx4).mpr hl)
          have := hEv n x1 x2 x3 x4 1 1 0 hx4
            (fun x5 _ hx5 => OKV n x1 x2 x3 x4 x5 1 b1 b2 b3 hx4 (fun _ => rfl)
              (fun hl => by omega))
            (OKV n x1 x2 x3 x4 x4 0 b1 b2 b3 hx4 (fun hl => by omega) (fun _ => rfl))
            (by norm_num)
          simp only [if_neg hR, if_neg h]
          omega
    have hG := G2 n (E n x1 x2 x3) x2 x3 0 n n 1 0 hn b2 b3 hp
    rw [hD]
    linarith
  have DD : ∀ n x2 x3 x1, 2 ≤ n → x1 ≤ n → x2 ≤ n → x3 ≤ n → x1 = x2 → x2 = x3 →
      D n x2 x3 x1 = 0 := by
    intro n x2 x3 x1 hn b1 b2 b3 h12 h23
    rw [hD]
    apply Finset.sum_eq_zero
    intro x4 hx4
    have hx4' : x4 ≤ n := by
      rw [Finset.mem_range] at hx4
      omega
    have := hEv n x1 x2 x3 x4 0 0 0 hx4'
      (fun x5 _ hx5 => OKV n x1 x2 x3 x4 x5 0 b1 b2 b3 hx4' (fun hl => by omega)
        (fun _ => rfl))
      (OKV n x1 x2 x3 x4 x4 0 b1 b2 b3 hx4' (fun hl => by omega) (fun _ => rfl))
      (by norm_num)
    omega
  -- the sum over x1
  obtain ⟨H, hH⟩ : ∃ H : ℕ → ℕ → ℕ → ℕ, ∀ n x2 x3, H n x2 x3 =
      ∑ x1 ∈ Finset.range (n + 1), D n x2 x3 x1 := ⟨_, fun _ _ _ => rfl⟩
  have HE : ∀ n x2 x3, 2 ≤ n → x2 ≤ n → x3 ≤ n → x2 = x3 →
      H n x2 x3 = n * (n * n + 2) := by
    intro n x2 x3 hn b2 b3 h23
    have hp : ∀ x1, x1 ≤ n → D n x2 x3 x1 + 0 * (if R n 0 x1 then 1 else 0) +
        (if x1 = x2 then n * n + 2 else 0) = n * n + 2 + 0 * (if R n 0 x1 then 1 else 0) +
        (if x1 = x2 then 0 else 0) := by
      intro x1 hx1
      by_cases h : x1 = x2
      · have := DD n x2 x3 x1 hn hx1 b2 b3 h h23
        split_ifs <;> omega
      · have := DC n x2 x3 x1 hn hx1 b2 b3 h h23
        split_ifs <;> omega
    have hG := G2 n (D n x2 x3) 0 x2 0 (n * n + 2) (n * n + 2) 0 0 hn (by omega) b2 hp
    rw [hH]
    linarith
  have HN : ∀ n x2 x3, 2 ≤ n → x2 ≤ n → x3 ≤ n → x2 ≠ x3 →
      H n x2 x3 + (n * n + 3 * n + (if R n x2 x3 then 1 else 0)) =
        (n + 1) * (n * n + 2 * n) + (n * n + n + 2 + n * (if R n x2 x3 then 1 else 0)) := by
    intro n x2 x3 hn b2 b3 h23
    have hp : ∀ x1, x1 ≤ n → D n x2 x3 x1 + 0 * (if R n 0 x1 then 1 else 0) +
        (if x1 = x2 then n * n + 3 * n + (if R n x2 x3 then 1 else 0) else 0) =
        n * n + 2 * n + 0 * (if R n 0 x1 then 1 else 0) +
        (if x1 = x2 then n * n + n + 2 + n * (if R n x2 x3 then 1 else 0) else 0) := by
      intro x1 hx1
      by_cases h : x1 = x2
      · have := DB n x2 x3 x1 hn hx1 b2 b3 h h23
        rw [h] at this ⊢
        by_cases hR : R n x2 x3
        · simp only [if_pos hR] at this ⊢
          split_ifs <;> omega
        · simp only [if_neg hR] at this ⊢
          split_ifs <;> omega
      · have := DA n x2 x3 x1 hn hx1 b2 b3 h h23
        split_ifs <;> omega
    have hG := G2 n (D n x2 x3) 0 x2 0 (n * n + 3 * n + (if R n x2 x3 then 1 else 0))
      (n * n + 2 * n) 0 (n * n + n + 2 + n * (if R n x2 x3 then 1 else 0)) hn (by omega) b2 hp
    rw [hH]
    linarith
  -- the sum over x3
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℕ → ℕ, ∀ n x2, K n x2 =
      ∑ x3 ∈ Finset.range (n + 1), H n x2 x3 := ⟨_, fun _ _ => rfl⟩
  have KK : ∀ n x2, 2 ≤ n → x2 ≤ n →
      K n x2 + (3 * n ^ 2 + 4) = (n + 1) * (n ^ 3 + 3 * n ^ 2 + 2) + 4 * n := by
    intro n x2 hn b2
    have hp : ∀ x3, x3 ≤ n → H n x2 x3 + 1 * (if R n x2 x3 then 1 else 0) +
        (if x3 = x2 then 3 * n ^ 2 + 2 else 0) =
        n ^ 3 + 3 * n ^ 2 + 2 + n * (if R n x2 x3 then 1 else 0) +
        (if x3 = x2 then 2 * n else 0) := by
      intro x3 hx3
      by_cases h : x3 = x2
      · have hRn : ¬ R n x2 x3 := by
          rw [Rl n x2 x3 b2 hx3]
          omega
        have := HE n x2 x3 hn b2 hx3 h.symm
        simp only [if_neg hRn, if_pos h]
        rw [this]
        ring
      · have := HN n x2 x3 hn b2 hx3 (Ne.symm h)
        simp only [if_neg h]
        linarith
    have hG := G2 n (H n x2) x2 x2 1 (3 * n ^ 2 + 2) (n ^ 3 + 3 * n ^ 2 + 2) n (2 * n)
      hn b2 b2 hp
    rw [hK]
    linarith
  -- a(n) as the iterated sum
  have hsum : ∀ n, a n = ∑ x2 ∈ Finset.range (n + 1), K n x2 := by
    intro n
    have e1 : a n = ∑ x1 ∈ Finset.range (n + 1), ∑ x2 ∈ Finset.range (n + 1),
        ∑ x3 ∈ Finset.range (n + 1), D n x2 x3 x1 := by
      unfold a
      rw [Finset.card_filter]
      simp only [Finset.sum_product, hD, hE]
    rw [e1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x2 _ => ?_)
    rw [hK, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun x3 _ => (hH n x2 x3).symm)
  -- the closed form for n >= 2
  have hcf : ∀ n, 2 ≤ n → a n + 2 = n ^ 5 + 5 * n ^ 4 + 4 * n ^ 3 + 6 * n ^ 2 + 4 * n := by
    intro n hn
    have e1 := hsum n
    have h1 : ∑ x2 ∈ Finset.range (n + 1), (K n x2 + (3 * n ^ 2 + 4)) =
        ∑ x2 ∈ Finset.range (n + 1), ((n + 1) * (n ^ 3 + 3 * n ^ 2 + 2) + 4 * n) :=
      Finset.sum_congr rfl (fun x2 hx2 => KK n x2 hn (by rw [Finset.mem_range] at hx2; omega))
    rw [Finset.sum_add_distrib, Lc n, Lc n] at h1
    rw [e1]
    linarith
  have hcfz : ∀ n : ℕ, 2 ≤ n → (a n : ℤ) + 2 =
      (n : ℤ) ^ 5 + 5 * (n : ℤ) ^ 4 + 4 * (n : ℤ) ^ 3 + 6 * (n : ℤ) ^ 2 + 4 * (n : ℤ) := by
    intro n hn
    exact_mod_cast hcf n hn
  have hcfq : ∀ n : ℕ, 2 ≤ n → (a n : ℚ) + 2 =
      (n : ℚ) ^ 5 + 5 * (n : ℚ) ^ 4 + 4 * (n : ℚ) ^ 3 + 6 * (n : ℚ) ^ 2 + 4 * (n : ℚ) := by
    intro n hn
    exact_mod_cast hcf n hn
  have a1 : a 1 = 14 := by decide +kernel
  have a2 : a 2 = 174 := by
    have h := hcf 2 (by norm_num)
    norm_num at h
    omega
  have a3 : a 3 = 820 := by
    have h := hcf 3 (by norm_num)
    norm_num at h
    omega
  have a4 : a 4 = 2670 := by
    have h := hcf 4 (by norm_num)
    norm_num at h
    omega
  have a5 : a 5 = 6918 := by
    have h := hcf 5 (by norm_num)
    norm_num at h
    omega
  have a6 : a 6 = 15358 := by
    have h := hcf 6 (by norm_num)
    norm_num at h
    omega
  have a7 : a 7 = 30504 := by
    have h := hcf 7 (by norm_num)
    norm_num at h
    omega
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    rw [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega,
      show k + 8 - 3 = k + 5 by omega, show k + 8 - 4 = k + 4 by omega,
      show k + 8 - 5 = k + 3 by omega, show k + 8 - 6 = k + 2 by omega]
    have h2 := hcfz (k + 2) (by omega)
    have h3 := hcfz (k + 3) (by omega)
    have h4 := hcfz (k + 4) (by omega)
    have h5 := hcfz (k + 5) (by omega)
    have h6 := hcfz (k + 6) (by omega)
    have h7 := hcfz (k + 7) (by omega)
    have h8 := hcfz (k + 8) (by omega)
    push_cast at h2 h3 h4 h5 h6 h7 h8
    linarith
  · have hb : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - PowerSeries.X) ^ 6 =
        14 + 90 * PowerSeries.X - 14 * PowerSeries.X ^ 2 + 80 * PowerSeries.X ^ 3 -
          72 * PowerSeries.X ^ 4 + 26 * PowerSeries.X ^ 5 - 4 * PowerSeries.X ^ 6 := by
      have e : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - PowerSeries.X) ^ 6 =
          PowerSeries.mk (fun n => (a (n + 1) : ℚ))
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 *
              (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * PowerSeries.X ^ 1)
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 15 *
              (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * PowerSeries.X ^ 2)
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 20 *
              (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * PowerSeries.X ^ 3)
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 15 *
              (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * PowerSeries.X ^ 4)
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 *
              (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * PowerSeries.X ^ 5)
            + PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * PowerSeries.X ^ 6 := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 15,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 20]
        ring
      have e2 : (14 + 90 * PowerSeries.X - 14 * PowerSeries.X ^ 2 + 80 * PowerSeries.X ^ 3 -
          72 * PowerSeries.X ^ 4 + 26 * PowerSeries.X ^ 5 - 4 * PowerSeries.X ^ 6 :
          PowerSeries ℚ) =
          (PowerSeries.C : ℚ →+* PowerSeries ℚ) 14 +
            (PowerSeries.C : ℚ →+* PowerSeries ℚ) 90 * PowerSeries.X ^ 1 -
            (PowerSeries.C : ℚ →+* PowerSeries ℚ) 14 * PowerSeries.X ^ 2 +
            (PowerSeries.C : ℚ →+* PowerSeries ℚ) 80 * PowerSeries.X ^ 3 -
            (PowerSeries.C : ℚ →+* PowerSeries ℚ) 72 * PowerSeries.X ^ 4 +
            (PowerSeries.C : ℚ →+* PowerSeries ℚ) 26 * PowerSeries.X ^ 5 -
            (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 * PowerSeries.X ^ 6 := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 14,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 90,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 80,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 72,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 26,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
        ring
      rw [e, e2]
      ext m
      simp only [map_add, map_sub]
      simp only [PowerSeries.coeff_C_mul_X_pow]
      simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
        PowerSeries.coeff_C]
      rcases Nat.lt_or_ge m 7 with hm | hm
      · interval_cases m <;> norm_num [a1, a2, a3, a4, a5, a6, a7]
      · obtain ⟨j, rfl⟩ : ∃ j, m = j + 7 := ⟨m - 7, by omega⟩
        rw [if_pos (show 1 ≤ j + 7 by omega), if_pos (show 2 ≤ j + 7 by omega),
          if_pos (show 3 ≤ j + 7 by omega), if_pos (show 4 ≤ j + 7 by omega),
          if_pos (show 5 ≤ j + 7 by omega), if_pos (show 6 ≤ j + 7 by omega),
          if_neg (show ¬ (j + 7 = 0) by omega), if_neg (show ¬ (j + 7 = 1) by omega),
          if_neg (show ¬ (j + 7 = 2) by omega), if_neg (show ¬ (j + 7 = 3) by omega),
          if_neg (show ¬ (j + 7 = 4) by omega), if_neg (show ¬ (j + 7 = 5) by omega),
          if_neg (show ¬ (j + 7 = 6) by omega),
          show j + 7 - 1 + 1 = j + 7 by omega, show j + 7 - 2 + 1 = j + 6 by omega,
          show j + 7 - 3 + 1 = j + 5 by omega, show j + 7 - 4 + 1 = j + 4 by omega,
          show j + 7 - 5 + 1 = j + 3 by omega, show j + 7 - 6 + 1 = j + 2 by omega]
        have h2 := hcfq (j + 2) (by omega)
        have h3 := hcfq (j + 3) (by omega)
        have h4 := hcfq (j + 4) (by omega)
        have h5 := hcfq (j + 5) (by omega)
        have h6 := hcfq (j + 6) (by omega)
        have h7 := hcfq (j + 7) (by omega)
        have h8 := hcfq (j + 7 + 1) (by omega)
        push_cast at h2 h3 h4 h5 h6 h7 h8
        linarith
    rw [mul_assoc, hb]
    ring
