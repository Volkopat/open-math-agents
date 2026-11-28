import OMAStatements.S_oeis_a104102

namespace OMA.S_oeis_a104102



/-! ### Kernel arithmetic

The hot functions use `Nat.rec` and the raw operations `Nat.mul`, `Nat.mod`, ..., which the kernel
evaluates on literals directly. -/

/-- `acc * b ^ e % m` by repeated squaring; `fuel` bounds the number of bits of `e`. -/
def powMod (m fuel : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => Nat.mod acc m)
    (fun _ ih b e acc => cond (Nat.beq e 0) (Nat.mod acc m)
      (ih (Nat.mod (Nat.mul b b) m) (Nat.div e 2)
        (cond (Nat.beq (Nat.mod e 2) 1) (Nat.mod (Nat.mul acc b) m) acc))) fuel

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem beq_true {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  subst h
  exact Nat.beq_refl a

theorem powMod_zero (m b e acc : ℕ) : powMod m 0 b e acc = acc % m := rfl

theorem powMod_succ (m fuel b e acc : ℕ) : powMod m (fuel + 1) b e acc =
    if e = 0 then acc % m
    else powMod m fuel (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc) := by
  show cond (Nat.beq e 0) _ _ = _
  by_cases h0 : e = 0
  · subst h0; rfl
  · rw [beq_false h0, if_neg h0]
    show powMod m fuel (Nat.mod (Nat.mul b b) m) (Nat.div e 2)
      (cond (Nat.beq (Nat.mod e 2) 1) (Nat.mod (Nat.mul acc b) m) acc) = _
    by_cases h2 : e % 2 = 1
    · have h2' : Nat.mod e 2 = 1 := h2
      rw [beq_true h2', if_pos h2]; rfl
    · have h2' : Nat.mod e 2 ≠ 1 := h2
      rw [beq_false h2', if_neg h2]; rfl

theorem powMod_spec (m : ℕ) : ∀ fuel b e acc, e < 2 ^ fuel →
    powMod m fuel b e acc = acc * b ^ e % m := by
  intro fuel
  induction fuel with
  | zero =>
    intro b e acc he
    have : e = 0 := by simpa using he
    subst this
    simp [powMod_zero]
  | succ fuel ih =>
    intro b e acc he
    rw [powMod_succ]
    by_cases h0 : e = 0
    · subst h0
      simp
    · have he2 : e / 2 < 2 ^ fuel := by
        rw [pow_succ] at he
        omega
      rw [if_neg h0, ih _ _ _ he2]
      have hb : (b * b % m) ^ (e / 2) ≡ b ^ (2 * (e / 2)) [MOD m] := by
        rw [pow_mul, sq]
        exact (Nat.mod_modEq _ _).pow _
      rcases Nat.mod_two_eq_zero_or_one e with hr | hr
      · rw [if_neg (by omega)]
        have he' : e = 2 * (e / 2) := by omega
        have := hb.mul_left acc
        rw [← he'] at this
        exact this
      · rw [if_pos hr]
        have he' : b ^ e = b * b ^ (2 * (e / 2)) := by
          rw [← pow_succ']
          congr 1
          omega
        have := (Nat.mod_modEq (acc * b) m).mul hb
        rw [he', ← mul_assoc]
        exact this

/-- Fermat's little theorem to base 2, in the form the kernel test uses. -/
theorem fermat_two {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) : 2 ^ (q - 1) % q = 1 := by
  have := Fact.mk hq
  have hne : (2 : ZMod q) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod q) = 0 := by simpa using h
    have hd := (ZMod.natCast_eq_zero_iff 2 q).mp h'
    exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hd)
  have h := ZMod.pow_card_sub_one_eq_one hne
  have h' : ((2 ^ (q - 1) : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by simpa using h
  rw [ZMod.natCast_eq_natCast_iff'] at h'
  rw [h', Nat.mod_eq_of_lt hq.one_lt]

/-! ### The interval for n = 36 -/

/-- `151#`, the product of the first 36 primes. -/
def P : ℕ := 225319534991831177328890236228992001350685163362356544091910

theorem primorial_151 : primorial 151 = P := by
  decide +kernel

/-- The test that a prime `m > 151` always passes: `m` is coprime to `151#` and satisfies Fermat's
congruence to base 2. A number that fails it is composite. -/
def test (m : ℕ) : Bool :=
  Nat.beq (Nat.gcd m P) 1 && Nat.beq (powMod m 200 2 (Nat.sub m 1) 1) 1

theorem prime_dvd_primorial_le {q n : ℕ} (hq : q.Prime) (h : q ∣ primorial n) : q ≤ n := by
  unfold primorial at h
  obtain ⟨r, hr, hqr⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp h
  rw [Finset.mem_filter, Finset.mem_range] at hr
  have := (Nat.prime_dvd_prime_iff_eq hq hr.2).mp hqr
  omega

theorem test_of_prime {m : ℕ} (hm : m.Prime) (hlt : 151 < m) (hsmall : m < 2 ^ 200) :
    test m = true := by
  have hcop : Nat.gcd m P = 1 := by
    rw [← primorial_151]
    apply (Nat.Prime.coprime_iff_not_dvd hm).mpr
    intro hd
    have := prime_dvd_primorial_le hm hd
    omega
  have hferm : powMod m 200 2 (m - 1) 1 = 1 := by
    rw [powMod_spec _ _ _ _ _ (by omega), one_mul]
    exact fermat_two hm (by omega)
  show (Nat.beq (Nat.gcd m P) 1 && Nat.beq (powMod m 200 2 (m - 1) 1) 1) = true
  rw [beq_true hcop, beq_true hferm]
  rfl

/-- The number of `m ∈ [s, s + L)` that pass `test`. -/
def cnt (s L : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun L ih => Nat.add ih (cond (test (Nat.add s L)) 1 0)) L

theorem cnt_succ (s L : ℕ) : cnt s (L + 1) = cnt s L + if test (s + L) then 1 else 0 := by
  show Nat.add (cnt s L) (cond (test (Nat.add s L)) 1 0) = _
  cases test (s + L) <;> rfl

theorem card_le_cnt (s : ℕ) (hs : 151 < s) : ∀ L, s + L ≤ 2 ^ 200 →
    ((Finset.Ico s (s + L)).filter Nat.Prime).card ≤ cnt s L := by
  intro L
  induction L with
  | zero => intro _; simp [cnt]
  | succ L ih =>
    intro hL
    have hIco : Finset.Ico s (s + (L + 1)) = insert (s + L) (Finset.Ico s (s + L)) := by
      rw [← add_assoc]
      exact (Finset.insert_Ico_right_eq_Ico_add_one (by omega)).symm
    rw [hIco, Finset.filter_insert, cnt_succ]
    have hnot : s + L ∉ Finset.filter Nat.Prime (Finset.Ico s (s + L)) := by simp
    by_cases hp : Nat.Prime (s + L)
    · rw [if_pos hp, Finset.card_insert_of_notMem hnot]
      have ht := test_of_prime hp (by omega) (by omega)
      rw [if_pos ht]
      have := ih (by omega)
      omega
    · rw [if_neg hp]
      have := ih (by omega)
      omega

theorem cnt_add (s L₁ : ℕ) : ∀ L₂, cnt s (L₁ + L₂) = cnt s L₁ + cnt (s + L₁) L₂ := by
  intro L₂
  induction L₂ with
  | zero => rfl
  | succ L ih =>
    rw [← add_assoc, cnt_succ, ih, cnt_succ, add_assoc s L₁ L]
    ring

/-! Each block is a separate declaration, so the kernel frees its cache between blocks. -/

theorem b0 : cnt P 2000 = 13 := by decide +kernel
theorem b1 : cnt (P + 2000) 2000 = 11 := by decide +kernel
theorem b2 : cnt (P + 4000) 2000 = 7 := by decide +kernel
theorem b3 : cnt (P + 6000) 2000 = 14 := by decide +kernel
theorem b4 : cnt (P + 8000) 2000 = 12 := by decide +kernel
theorem b5 : cnt (P + 10000) 2000 = 13 := by decide +kernel
theorem b6 : cnt (P + 12000) 2000 = 19 := by decide +kernel
theorem b7 : cnt (P + 14000) 2000 = 12 := by decide +kernel
theorem b8 : cnt (P + 16000) 2000 = 11 := by decide +kernel
theorem b9 : cnt (P + 18000) 2000 = 14 := by decide +kernel
theorem b10 : cnt (P + 20000) 2000 = 12 := by decide +kernel
theorem b11 : cnt (P + 22000) 2000 = 16 := by decide +kernel
theorem b12 : cnt (P + 24000) 649 = 2 := by decide +kernel

theorem cnt_value : cnt P 24649 = 156 := by
  have e : ∀ k, P + 2000 * k + 2000 = P + 2000 * (k + 1) := fun k => by ring
  rw [show (24649 : ℕ) = 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000 + 2000
    + 2000 + 2000 + 649 by norm_num]
  simp only [cnt_add, b0]
  norm_num only [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]

theorem p36 : p 36 = 151 := by
  have h : Nat.count Nat.Prime 151 = 35 := by decide +kernel
  show Nat.nth Nat.Prime 35 = 151
  rw [← h]
  exact Nat.nth_count (by norm_num)

theorem p37 : p 37 = 157 := by
  have h : Nat.count Nat.Prime 157 = 36 := by decide +kernel
  show Nat.nth Nat.Prime 36 = 157
  rw [← h]
  exact Nat.nth_count (by norm_num)

/-! Controls: the entry's first two terms, a(1) = 4 and a(2) = 7. -/

theorem p1 : p 1 = 2 := by
  have h : Nat.count Nat.Prime 2 = 0 := by decide +kernel
  show Nat.nth Nat.Prime 0 = 2
  rw [← h]
  exact Nat.nth_count (by norm_num)

theorem p2 : p 2 = 3 := by
  have h : Nat.count Nat.Prime 3 = 1 := by decide +kernel
  show Nat.nth Nat.Prime 1 = 3
  rw [← h]
  exact Nat.nth_count (by norm_num)

theorem p3 : p 3 = 5 := by
  have h : Nat.count Nat.Prime 5 = 2 := by decide +kernel
  show Nat.nth Nat.Prime 2 = 5
  rw [← h]
  exact Nat.nth_count (by norm_num)

theorem a1 : a 1 = 4 := by
  unfold a
  rw [p1, show 1 + 1 = 2 from rfl, p2]
  decide +kernel

theorem a2 : a 2 = 7 := by
  unfold a
  rw [p2, show 2 + 1 = 3 from rfl, p3]
  decide +kernel

theorem a36 : a 36 ≤ 156 := by
  unfold a
  rw [p36, show 36 + 1 = 37 from rfl, p37, primorial_151]
  have h := card_le_cnt P (by norm_num [P]) 24649 (by norm_num [P])
  rw [show (157 : ℕ) ^ 2 = 24649 by norm_num, ← cnt_value]
  exact h

theorem disproof : ¬ (∀ n : ℕ, 1 ≤ n → p (n + 1) < a n) := by
  intro h
  have h36 := h 36 (by norm_num)
  rw [show 36 + 1 = 37 from rfl, p37] at h36
  have := a36
  omega

end OMA.S_oeis_a104102

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a104102.main) :=
  OMA.S_oeis_a104102.disproof
