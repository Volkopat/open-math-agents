import OMAStatements.S_oeis_a333794

namespace OMA.S_oeis_a333794




/-- Control: the first 24 terms of the entry. -/
theorem first_terms :
    (List.range 24).map (fun i => a (i + 1)) = [1, 3, 6, 7, 12, 13, 20, 15, 22, 25, 36, 27, 40,
      41, 42, 31, 48, 45, 64, 51, 66, 73, 96, 55] := by
  decide +kernel

theorem mem_S {n p : ℕ} (hn : n ≠ 0) :
    p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ∣ n) ↔ p.Prime ∧ p ∣ n := by
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h.2), h⟩

theorem gpf_spec {n : ℕ} (hn : 2 ≤ n) : (gpf n).Prime ∧ gpf n ∣ n := by
  have hne : ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ∣ n)).Nonempty :=
    ⟨n.minFac, (mem_S (by omega)).mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩⟩
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [gpf, heq]
  exact (mem_S (by omega)).mp hi

theorem le_gpf {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : n ≠ 0) : p ≤ gpf n :=
  Finset.le_sup (f := id) ((mem_S hn).mpr ⟨hp, hpn⟩)

theorem step_lt {n : ℕ} (hn : 2 ≤ n) : n - n / gpf n < n := by
  obtain ⟨hP, hPn⟩ := gpf_spec hn
  have hd : 0 < n / gpf n := Nat.div_pos (Nat.le_of_dvd (by omega) hPn) hP.pos
  generalize n / gpf n = d at hd ⊢
  omega

theorem aux_stable : ∀ f g n, n ≤ f → n ≤ g → aux f n = aux g n := by
  intro f
  induction f with
  | zero =>
    intro g n hf hg
    have h0 : n = 0 := by omega
    subst h0
    cases g <;> simp [aux]
  | succ f ih =>
    intro g n hf hg
    cases g with
    | zero =>
      have h0 : n = 0 := by omega
      subst h0
      simp [aux]
    | succ g =>
      simp only [aux]
      split_ifs with h
      · rfl
      · have hlt := step_lt (n := n) (by omega)
        rw [ih g (n - n / gpf n) (by omega) (by omega)]

/-- The entry's recursion: a(n) = n + a(n - A052126(n)) for n > 1. -/
theorem a_rec {n : ℕ} (hn : 2 ≤ n) : a n = n + a (n - n / gpf n) := by
  obtain ⟨f, rfl⟩ : ∃ f, n = f + 1 := ⟨n - 1, by omega⟩
  have hlt := step_lt hn
  unfold a
  conv_lhs => rw [aux, if_neg (by omega)]
  rw [aux_stable f (f + 1 - (f + 1) / gpf (f + 1)) (f + 1 - (f + 1) / gpf (f + 1))
    (by omega) le_rfl]

theorem step_eq {n p : ℕ} (h : p ∣ n) : n - n / p = (p - 1) * (n / p) := by
  rw [Nat.sub_one_mul, Nat.mul_div_cancel' h]

/-- The largest prime factor is an optimal first step. -/
theorem key : ∀ n, 2 ≤ n → ∀ q, q.Prime → q ∣ n → a (n - n / q) ≤ a (n - n / gpf n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn q hq hqn
    obtain ⟨hP, hPn⟩ := gpf_spec hn
    by_cases hqP : q = gpf n
    · rw [hqP]
    have hqleP : q ≤ gpf n := le_gpf hq hqn (by omega)
    have hqltP : q < gpf n := lt_of_le_of_ne hqleP hqP
    have hcop : Nat.Coprime q (gpf n) := (Nat.coprime_primes hq hP).mpr hqP
    obtain ⟨k, hk⟩ := hcop.mul_dvd_of_dvd_of_dvd hqn hPn
    have hq2 := hq.two_le
    have hP2 := hP.two_le
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk
        omega
      · exact h
    have hnq : n / q = gpf n * k := Nat.div_eq_of_eq_mul_left hq.pos (hk.trans (by ring))
    have hnP : n / gpf n = q * k := Nat.div_eq_of_eq_mul_left hP.pos (hk.trans (by ring))
    have hu' : n - n / q = gpf n * ((q - 1) * k) := by
      rw [step_eq hqn, hnq]
      ring
    have hx' : n - n / gpf n = q * ((gpf n - 1) * k) := by
      rw [step_eq hPn, hnP]
      ring
    have hqk : 0 < (q - 1) * k := Nat.mul_pos (by omega) hk0
    have hPk : 0 < (gpf n - 1) * k := Nat.mul_pos (by omega) hk0
    have hu2 : 2 ≤ n - n / q := by
      rw [hu']
      calc 2 ≤ gpf n := hP2
        _ ≤ gpf n * ((q - 1) * k) := Nat.le_mul_of_pos_right _ hqk
    have hx2 : 2 ≤ n - n / gpf n := by
      rw [hx']
      calc 2 ≤ q := hq2
        _ ≤ q * ((gpf n - 1) * k) := Nat.le_mul_of_pos_right _ hPk
    have hxn : n - n / gpf n < n := step_lt hn
    have hux : n - n / q ≤ n - n / gpf n := by
      rw [hu', hx']
      have h1 : (q - 1) * gpf n ≤ (gpf n - 1) * q := by
        rw [Nat.sub_one_mul, Nat.sub_one_mul, mul_comm (gpf n) q]
        exact Nat.sub_le_sub_left hqleP _
      calc gpf n * ((q - 1) * k) = ((q - 1) * gpf n) * k := by ring
        _ ≤ ((gpf n - 1) * q) * k := Nat.mul_le_mul_right k h1
        _ = q * ((gpf n - 1) * k) := by ring
    -- the greatest prime factor of u = n - n/q is gpf n
    have hgu : gpf (n - n / q) = gpf n := by
      apply le_antisymm
      · obtain ⟨hr, hru⟩ := gpf_spec hu2
        have hru' : gpf (n - n / q) ∣ (q - 1) * (gpf n * k) := by
          have e : n - n / q = (q - 1) * (gpf n * k) := by rw [hu']; ring
          rw [← e]
          exact hru
        rcases (Nat.Prime.dvd_mul hr).mp hru' with h | h
        · have := Nat.le_of_dvd (by omega) h
          omega
        · have hkn : gpf n * k ∣ n := ⟨q, hk.trans (by ring)⟩
          exact le_gpf hr (h.trans hkn) (by omega)
      · exact le_gpf hP (by rw [hu']; exact Dvd.intro _ rfl) (by omega)
    have huP : (n - n / q) / gpf n = (q - 1) * k := by
      rw [hu', Nat.mul_div_cancel_left _ hP.pos]
    have hxq : (n - n / gpf n) / q = (gpf n - 1) * k := by
      rw [hx', Nat.mul_div_cancel_left _ hq.pos]
    have hPu : gpf n ∣ n - n / q := by rw [hu']; exact Dvd.intro _ rfl
    have hqx : q ∣ n - n / gpf n := by rw [hx']; exact Dvd.intro _ rfl
    have hw : (n - n / q) - (n - n / q) / gpf n = (n - n / gpf n) - (n - n / gpf n) / q := by
      rw [step_eq hPu, huP, step_eq hqx, hxq]
      ring
    have hau : a (n - n / q) = (n - n / q) + a ((n - n / gpf n) - (n - n / gpf n) / q) := by
      rw [a_rec hu2, hgu, hw]
    have ihx := ih (n - n / gpf n) hxn hx2 q hq hqx
    have hax := a_rec hx2
    rw [hau, hax]
    exact Nat.add_le_add hux ihx

/-- The formula of the entry, conjectured there: for n > 1, a(n) = n + max over the primes p
dividing n of a(n - n/p). -/
theorem conjecture (n : ℕ) (hn : 2 ≤ n) :
    a n = n + n.primeFactors.sup (fun p => a (n - n / p)) := by
  rw [a_rec hn]
  congr 1
  apply le_antisymm
  · obtain ⟨hP, hPn⟩ := gpf_spec hn
    exact Finset.le_sup (f := fun p => a (n - n / p)) (Nat.mem_primeFactors.mpr ⟨hP, hPn, by omega⟩)
  · apply Finset.sup_le
    intro q hq
    obtain ⟨hqp, hqn, -⟩ := Nat.mem_primeFactors.mp hq
    exact key n hn q hqp hqn

end OMA.S_oeis_a333794

theorem OMA.solution : type_of% @OMA.S_oeis_a333794.main :=
  fun n hn => OMA.S_oeis_a333794.conjecture n hn
