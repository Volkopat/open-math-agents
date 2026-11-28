import OMAReductions.R_Erdos287_erdos_287_R1

/-!
# Proof of `Erdos287.erdos_287.R1.H1`

Erdős (1932) / Kürschák (1918): if `1 < s 0 < ... < s (k - 1)` (`k ≥ 2`) and
`∑ i, 1 / (s i : ℝ) = 1`, then `max_gap k s ≥ 2`.
-/

open Erdos287 Finset

private lemma oddPart_mul (m : ℕ) :
    2 ^ (m.factorization 2) * (m / 2 ^ (m.factorization 2)) = m :=
  Nat.mul_div_cancel' (Nat.ordProj_dvd m 2)

private lemma oddPart_odd {m : ℕ} (hm : m ≠ 0) :
    Odd (m / 2 ^ (m.factorization 2)) := by
  rw [Nat.odd_iff]
  by_contra h
  have h2 : 2 ∣ m / 2 ^ (m.factorization 2) := by omega
  have hpow : 2 ^ (m.factorization 2 + 1) ∣ m := by
    calc 2 ^ (m.factorization 2 + 1)
        = 2 ^ (m.factorization 2) * 2 := pow_succ _ _
      _ ∣ 2 ^ (m.factorization 2) * (m / 2 ^ (m.factorization 2)) := mul_dvd_mul_left _ h2
      _ = m := oddPart_mul m
  have hle : m.factorization 2 + 1 ≤ m.factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hm).mp hpow
  omega

private lemma prod_odd {α : Type*} (s : Finset α) (f : α → ℕ) (hf : ∀ x ∈ s, Odd (f x)) :
    Odd (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.prod_insert has]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))

private lemma consecutive_recip_ne_one {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    ∑ m ∈ Finset.Icc a b, (1 : ℝ) / (m : ℝ) ≠ 1 := by
  intro hsum
  set S : Finset ℕ := Finset.Icc a b
  have hSne : S.Nonempty := ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, hab.le⟩⟩
  set e : ℕ := S.sup (fun m => m.factorization 2)
  have he1 : 1 ≤ e := by
    have hmem : (if Even a then a else a + 1) ∈ S := by
      split_ifs <;> exact Finset.mem_Icc.mpr (by omega)
    have heven : 2 ∣ (if Even a then a else a + 1) := by
      split_ifs with h
      · exact even_iff_two_dvd.mp h
      · rw [Nat.not_even_iff_odd] at h
        obtain ⟨t, ht⟩ := h
        exact ⟨t + 1, by omega⟩
    have hne : (if Even a then a else a + 1) ≠ 0 := by split_ifs <;> omega
    have h1 : 1 ≤ (if Even a then a else a + 1).factorization 2 :=
      (Nat.prime_two.dvd_iff_one_le_factorization hne).mp heven
    exact h1.trans (Finset.le_sup (f := fun m => m.factorization 2) hmem)
  obtain ⟨m₀, hm₀S, hm₀e⟩ := Finset.exists_mem_eq_sup S hSne (fun m => m.factorization 2)
  have hm₀e' : m₀.factorization 2 = e := hm₀e.symm
  have hm₀_uniq : ∀ m ∈ S, m ≠ m₀ → m.factorization 2 < e := by
    intro m hmS hne
    have hle : m.factorization 2 ≤ e := Finset.le_sup (f := fun m => m.factorization 2) hmS
    by_contra hge
    have hme : m.factorization 2 = e := by omega
    have hlt_or : m < m₀ ∨ m₀ < m := lt_or_gt_of_ne hne
    have aux : ∀ x y : ℕ, x ∈ S → y ∈ S → x < y →
        x.factorization 2 = e → y.factorization 2 = e → False := by
      intro x y hxS hyS hxy hxe hye
      have hx0 : x ≠ 0 := by have := (Finset.mem_Icc.mp hxS).1; omega
      have hy0 : y ≠ 0 := by have := (Finset.mem_Icc.mp hyS).1; omega
      set ux := x / 2 ^ e
      set uy := y / 2 ^ e
      have hxu : 2 ^ e * ux = x := by simpa [ux, hxe] using oddPart_mul x
      have hyu : 2 ^ e * uy = y := by simpa [uy, hye] using oddPart_mul y
      have hux_odd : Odd ux := by simpa [ux, hxe] using oddPart_odd hx0
      have huy_odd : Odd uy := by simpa [uy, hye] using oddPart_odd hy0
      have hux_lt : ux < uy := by nlinarith [Nat.one_le_pow e 2 (by omega)]
      have hux1_lt : ux + 1 < uy := by
        obtain ⟨tx, htx⟩ := hux_odd
        obtain ⟨ty, hty⟩ := huy_odd
        omega
      set z := 2 ^ e * (ux + 1)
      have hzS : z ∈ S := by
        have hxI := Finset.mem_Icc.mp hxS
        have hyI := Finset.mem_Icc.mp hyS
        refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
        · dsimp [z]; nlinarith [Nat.one_le_pow e 2 (by omega), hxI.1, hxu]
        · dsimp [z]; nlinarith [Nat.one_le_pow e 2 (by omega), hyI.2, hyu, hux1_lt]
      have h2_ux1 : 2 ∣ ux + 1 := by
        obtain ⟨tx, htx⟩ := hux_odd
        exact ⟨tx + 1, by omega⟩
      have hz_dvd : 2 ^ (e + 1) ∣ z := by
        rw [pow_succ]
        exact mul_dvd_mul_left _ h2_ux1
      have hz0 : z ≠ 0 := by
        have := Nat.one_le_pow e 2 (by omega)
        positivity
      have hz_ge : e + 1 ≤ z.factorization 2 :=
        (Nat.prime_two.pow_dvd_iff_le_factorization hz0).mp hz_dvd
      have hz_le : z.factorization 2 ≤ e := Finset.le_sup (f := fun m => m.factorization 2) hzS
      omega
    rcases hlt_or with hlt | hgt
    · exact aux m m₀ hmS hm₀S hlt hme hm₀e'
    · exact aux m₀ m hm₀S hmS hgt hm₀e' hme
  set O : ℕ := ∏ m ∈ S, (m / 2 ^ (m.factorization 2))
  have hO_odd : Odd O := prod_odd S _ (fun m hm => oddPart_odd (by have := (Finset.mem_Icc.mp hm).1; omega))
  set M : ℕ := 2 ^ e * O
  have hdvd : ∀ m ∈ S, m ∣ M := by
    intro m hm
    have hle : m.factorization 2 ≤ e := Finset.le_sup (f := fun m => m.factorization 2) hm
    rw [← oddPart_mul m]
    exact mul_dvd_mul (Nat.pow_dvd_pow 2 hle)
      (Finset.dvd_prod_of_mem (fun x => x / 2 ^ (x.factorization 2)) hm)
  have hM_eq : (∑ m ∈ S, M / m : ℕ) = M := by
    have hreal : ((∑ m ∈ S, M / m : ℕ) : ℝ) = (M : ℝ) := by
      push_cast
      have hterm : ∀ m ∈ S, ((M / m : ℕ) : ℝ) = (M : ℝ) * (1 / (m : ℝ)) := by
        intro m hm
        have hmpos : 0 < m := by
          have := (Finset.mem_Icc.mp hm).1
          omega
        have hm0 : (m : ℝ) ≠ 0 := by positivity
        rw [Nat.cast_div (hdvd m hm) hm0]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum, mul_one]
    exact_mod_cast hreal
  have hM_even : Even M := by
    have h2e : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
    exact even_iff_two_dvd.mpr (dvd_mul_of_dvd_left h2e O)
  have hterm_even : ∀ m ∈ S.erase m₀, Even (M / m) := by
    intro m hm
    have hmS : m ∈ S := Finset.mem_of_mem_erase hm
    have hmne : m ≠ m₀ := Finset.ne_of_mem_erase hm
    have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hmS).1; omega
    have hlt : m.factorization 2 < e := hm₀_uniq m hmS hmne
    have hpow : 2 * 2 ^ (m.factorization 2) ∣ 2 ^ e := by
      rw [mul_comm, ← pow_succ]
      exact Nat.pow_dvd_pow 2 (by omega)
    have hodd : m / 2 ^ (m.factorization 2) ∣ O :=
      Finset.dvd_prod_of_mem (fun x => x / 2 ^ (x.factorization 2)) hmS
    have h2m : 2 * m ∣ M := by
      have : 2 * m = (2 * 2 ^ (m.factorization 2)) * (m / 2 ^ (m.factorization 2)) := by
        rw [mul_assoc, oddPart_mul m]
      rw [this]
      exact mul_dvd_mul hpow hodd
    obtain ⟨q, hq⟩ := h2m
    have hdiv : M / m = 2 * q := by
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      rw [hq, show 2 * m * q = m * (2 * q) by ring, Nat.mul_div_cancel_left _ hmpos]
    exact ⟨q, by omega⟩
  have hm₀_odd : Odd (M / m₀) := by
    have hm₀0 : m₀ ≠ 0 := by have := (Finset.mem_Icc.mp hm₀S).1; omega
    have hO_dvd : m₀ / 2 ^ e ∣ O := by
      rw [← hm₀e']
      exact Finset.dvd_prod_of_mem (fun x => x / 2 ^ (x.factorization 2)) hm₀S
    obtain ⟨q, hq⟩ := hO_dvd
    have hq_odd : Odd q := by
      have hO' : Odd ((m₀ / 2 ^ e) * q) := hq ▸ hO_odd
      exact (Nat.odd_mul.mp hO').2
    have hMq : M = m₀ * q := by
      have hm₀_mul : 2 ^ e * (m₀ / 2 ^ e) = m₀ := by
        rw [← hm₀e']
        exact oddPart_mul m₀
      calc M = 2 ^ e * O := rfl
        _ = 2 ^ e * ((m₀ / 2 ^ e) * q) := by rw [hq]
        _ = (2 ^ e * (m₀ / 2 ^ e)) * q := by ring
        _ = m₀ * q := by rw [hm₀_mul]
    rw [hMq, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm₀0)]
    exact hq_odd
  have hsum_even : Even (∑ m ∈ S.erase m₀, M / m) := by
    have h2dvd : 2 ∣ ∑ m ∈ S.erase m₀, M / m :=
      Finset.dvd_sum (fun m hm => even_iff_two_dvd.mp (hterm_even m hm))
    exact even_iff_two_dvd.mpr h2dvd
  have hsplit : ∑ m ∈ S, M / m = M / m₀ + ∑ m ∈ S.erase m₀, M / m :=
    (Finset.add_sum_erase S (fun m => M / m) hm₀S).symm
  rw [hsplit] at hM_eq
  have hodd_sum : Odd (M / m₀ + ∑ m ∈ S.erase m₀, M / m) := hm₀_odd.add_even hsum_even
  rw [hM_eq] at hodd_sum
  exact (Nat.not_even_iff_odd.mpr hodd_sum) hM_even

theorem OMA.solution : OMA.R_Erdos287_erdos_287_R1.H1 := by
  intro k hk s hs h0 hsum
  by_contra hlt
  have hle1 : max_gap k s ≤ 1 := by omega
  have hstep : ∀ j : ℕ, (hj : j + 1 < k) → s ⟨j + 1, hj⟩ = s ⟨j, by omega⟩ + 1 := by
    intro j hj
    have hinc : s ⟨j, by omega⟩ < s ⟨j + 1, hj⟩ := hs (show (⟨j, by omega⟩ : Fin k) < ⟨j + 1, hj⟩ by simp)
    have hgap : s ⟨j + 1, hj⟩ - s ⟨j, by omega⟩ ≤ max_gap k s :=
      Finset.le_sup (f := fun i : Fin (k - 1) => s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)
        (Finset.mem_univ (⟨j, by omega⟩ : Fin (k - 1)))
    omega
  have hlin : ∀ i : Fin k, s i = s ⟨0, by omega⟩ + i.val := by
    intro ⟨i, hi⟩
    induction i with
    | zero => simp
    | succ j ih =>
      rw [hstep j hi, ih (by omega)]
      dsimp
      omega
  set a := s ⟨0, by omega⟩
  have hsum_eq : ∑ i : Fin k, (1 : ℝ) / (s i : ℝ) =
      ∑ m ∈ Finset.Icc a (a + k - 1), (1 : ℝ) / (m : ℝ) := by
    refine Finset.sum_nbij (fun i : Fin k => a + i.val) ?_ ?_ ?_ ?_
    · intro i _
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i₁ _ i₂ _ h
      dsimp at h
      exact Fin.ext (by omega)
    · intro m hm
      have hmI := Finset.mem_Icc.mp hm
      exact ⟨⟨m - a, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
    · intro i _
      rw [hlin i]
  exact consecutive_recip_ne_one (by omega) (by omega) (hsum_eq.symm.trans hsum)
