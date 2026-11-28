import OMAStatements.S_oeis_a062091
import Mathlib
open OMA.S_oeis_a062091

theorem Pa062091.oddNext_spec {B : ℕ} (hB : 0 < B) :
    Odd (oddNext B) ∧ ¬ oddNext B ∣ B ∧ ∀ m, Odd m → m < oddNext B → m ∣ B := by
  have hne : ({m : ℕ | Odd m ∧ ¬ m ∣ B}).Nonempty := ⟨2 * B + 1, by
    refine ⟨odd_two_mul_add_one B, fun h => ?_⟩
    have := Nat.le_of_dvd hB h; omega⟩
  have hmem := Nat.sInf_mem hne
  refine ⟨hmem.1, hmem.2, fun m hm hlt => ?_⟩
  by_contra hc
  exact absurd (Nat.sInf_le (show m ∈ {m : ℕ | Odd m ∧ ¬ m ∣ B} from ⟨hm, hc⟩))
    (not_le.mpr hlt)

theorem Pa062091.oddNext_le {B m : ℕ} (hm : Odd m) (h : ¬ m ∣ B) : oddNext B ≤ m :=
  Nat.sInf_le (show m ∈ {m : ℕ | Odd m ∧ ¬ m ∣ B} from ⟨hm, h⟩)

theorem Pa062091.evenNext_eq (B e : ℕ) (hB : Odd B) (ho : oddNext B ≤ 2 ^ e) :
    evenNext (2 ^ (e + 1) * B) = 2 * oddNext B := by
  obtain ⟨hoodd, hond, hlow⟩ := Pa062091.oddNext_spec hB.pos
  have hin : 2 * oddNext B ∈ {m : ℕ | Even m ∧ 0 < m ∧ ¬ m ∣ 2 ^ (e + 1) * B} := by
    refine ⟨even_two_mul _, by have := hoodd.pos; omega, fun h => hond ?_⟩
    rw [pow_succ', mul_assoc] at h
    have h2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right e
      (Nat.coprime_two_right.mpr hoodd)) h2
  apply le_antisymm (Nat.sInf_le hin)
  by_contra hlt
  push Not at hlt
  have hmem : evenNext (2 ^ (e + 1) * B) ∈ {m : ℕ | Even m ∧ 0 < m ∧ ¬ m ∣ 2 ^ (e + 1) * B} :=
    Nat.sInf_mem ⟨_, hin⟩
  obtain ⟨hev, hpos, hnd⟩ := hmem
  apply hnd
  have hlt' : evenNext (2 ^ (e + 1) * B) < 2 * oddNext B := hlt
  generalize evenNext (2 ^ (e + 1) * B) = m at hev hpos hlt' ⊢
  obtain ⟨f, s, hs, hm⟩ := Nat.exists_eq_two_pow_mul_odd (n := m) hpos.ne'
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      rw [pow_zero, one_mul] at hm
      rw [hm] at hev
      exact absurd hev (Nat.not_even_iff_odd.mpr hs)
    · exact h
  have h2f : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h2s : 2 * s ≤ m := by rw [hm]; exact Nat.mul_le_mul_right s h2f
  have hslt : s < oddNext B := by omega
  have hsd := hlow s hs hslt
  have hfm : 2 ^ f ≤ m := by rw [hm]; exact Nat.le_mul_of_pos_right _ hs.pos
  have hfe : f ≤ e + 1 := by
    by_contra hc
    push Not at hc
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hc
    rw [pow_succ] at this
    have : 2 ^ e * 2 * 2 ≤ m := le_trans this hfm
    omega
  rw [hm]
  exact mul_dvd_mul (pow_dvd_pow 2 hfe) hsd

theorem Pa062091.bProd_succ (k : ℕ) (hk : 1 ≤ k) :
    bProd (k + 1) = bProd k * oddNext (bProd k) ∧ b (k + 1) = oddNext (bProd k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine ⟨rfl, ?_⟩
  simp [b]

theorem Pa062091.inv (k : ℕ) (hk : 1 ≤ k) :
    Odd (bProd k) ∧ Odd (b k) ∧ (∀ m, Odd m → m ≤ b k → m ∣ bProd k) ∧
      (∀ p, p.Prime → p ∣ bProd k → p ≤ b k) ∧ b k ≤ 2 ^ k ∧ (2 ≤ k → 3 ≤ b k) := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h1 : bProd 1 = 1 := rfl
    have h2 : b 1 = 1 := by simp [b]
    rw [h1, h2]
    refine ⟨odd_one, odd_one, fun m _ _ => ?_, fun p hp hd => ?_, by norm_num, by omega⟩
    · have : m = 1 := by have := Nat.odd_iff.mp ‹Odd m›; omega
      subst this; exact dvd_refl 1
    · exact absurd (Nat.le_of_dvd one_pos hd) (by have := hp.two_le; omega)
  | succ k hk ih =>
    obtain ⟨hBo, hbo, hdiv, hpr, hbd, h3⟩ := ih
    obtain ⟨hP, hb⟩ := Pa062091.bProd_succ k hk
    obtain ⟨hoodd, hond, hlow⟩ := Pa062091.oddNext_spec hBo.pos
    have hgt : b k < oddNext (bProd k) := by
      by_contra hc
      push Not at hc
      exact hond (hdiv _ hoodd hc)
    rw [hP, hb]
    refine ⟨hBo.mul hoodd, hoodd, fun m hm hle => ?_, fun p hp hd => ?_, ?_, fun _ => ?_⟩
    · rcases lt_or_eq_of_le hle with h | h
      · exact Dvd.dvd.mul_right (hlow m hm h) _
      · rw [h]; exact dvd_mul_left _ _
    · rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
      · exact le_trans (hpr p hp h) hgt.le
      · exact Nat.le_of_dvd hoodd.pos h
    · rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have : k = 1 := by omega
        subst this
        have := Pa062091.oddNext_le (B := bProd 1) (m := 3) (by decide)
          (by show ¬ 3 ∣ 1; decide)
        calc oddNext (bProd 1) ≤ 3 := this
          _ ≤ 2 ^ (1 + 1) := by norm_num
      · have hb3 := h3 hk2
        obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (b k) (by omega)
        have hpodd : Odd p := hp.odd_of_ne_two (by omega)
        have hnd : ¬ p ∣ bProd k := fun h => absurd (hpr p hp h) (by omega)
        have := Pa062091.oddNext_le hpodd hnd
        rw [pow_succ]
        omega
    · have h1 : 1 ≤ b k := hbo.pos
      have hodd2 := Nat.odd_iff.mp hoodd
      have hb2 := Nat.odd_iff.mp hbo
      omega

theorem Pa062091.evenNext_two : evenNext 2 = 4 := by
  have hin : 4 ∈ {m : ℕ | Even m ∧ 0 < m ∧ ¬ m ∣ 2} := ⟨by decide, by norm_num, by decide⟩
  apply le_antisymm (Nat.sInf_le hin)
  show 4 ≤ evenNext 2
  have hmem : evenNext 2 ∈ {m : ℕ | Even m ∧ 0 < m ∧ ¬ m ∣ 2} := Nat.sInf_mem ⟨_, hin⟩
  obtain ⟨hev, hpos, hnd⟩ := hmem
  have hlt' : 0 < evenNext 2 := hpos
  have hev' : Even (evenNext 2) := hev
  have hnd' : ¬ evenNext 2 ∣ 2 := hnd
  generalize evenNext 2 = m at hev' hlt' hnd' ⊢
  by_contra hc
  push Not at hc
  interval_cases m <;> simp_all <;> contradiction

theorem Pa062091.aside (k : ℕ) (hk : 1 ≤ k) :
    aProd (k + 1) = 2 ^ (k + 2) * bProd k ∧ a (k + 2) = 2 * b (k + 1) := by
  have hstep : ∀ k, 1 ≤ k → aProd (k + 1) = 2 ^ (k + 2) * bProd k →
      a (k + 2) = 2 * b (k + 1) := by
    intro k hk h
    obtain ⟨_, hb⟩ := Pa062091.bProd_succ k hk
    have ha : a (k + 2) = evenNext (aProd (k + 1)) := by simp [a]
    have hI := Pa062091.inv (k + 1) (by omega)
    rw [ha, h, hb]
    rw [hb] at hI
    exact Pa062091.evenNext_eq (bProd k) (k + 1) (Pa062091.inv k hk).1 hI.2.2.2.2.1
  induction k, hk using Nat.le_induction with
  | base =>
    have h : aProd 2 = 2 ^ 3 * bProd 1 := by
      show aProd 1 * evenNext (aProd 1) = 2 ^ 3 * bProd 1
      have h1 : aProd 1 = 2 := rfl
      have h2 : bProd 1 = 1 := rfl
      rw [h1, h2, Pa062091.evenNext_two]
      norm_num
    exact ⟨h, hstep 1 le_rfl h⟩
  | succ k hk ih =>
    obtain ⟨h1, h2⟩ := ih
    have h : aProd (k + 1 + 1) = 2 ^ (k + 1 + 2) * bProd (k + 1) := by
      show aProd (k + 1) * evenNext (aProd (k + 1)) = _
      have ha : a (k + 2) = evenNext (aProd (k + 1)) := by simp [a]
      rw [← ha, h2, h1, (Pa062091.bProd_succ k hk).1, ← (Pa062091.bProd_succ k hk).2]
      ring
    exact ⟨h, hstep (k + 1) (by omega) h⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a062091.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega]
  exact (Pa062091.aside k (by omega)).2
