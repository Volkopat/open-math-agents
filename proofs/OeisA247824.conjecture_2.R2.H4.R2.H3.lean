import OMAReductions.R_OeisA247824_conjecture_2_R2_H4_R2

namespace OMA_A247824_PrimeWindows

def lin (lo : ℕ) : ℕ → ℕ
  | 0 => 1
  | l+1 => lin lo l * (lo + l)

def pr : ℕ → ℕ → ℕ → ℕ
  | 0, lo, len => lin lo len
  | f+1, lo, len => if len = 0 then 1 else if len = 1 then lo else
      pr f lo (len/2) * pr f (lo + len/2) (len - len/2)

theorem lin_dvd (lo : ℕ) : ∀ len i, lo ≤ i → i < lo + len → i ∣ lin lo len := by
  intro len
  induction len with
  | zero => intro i _ _; omega
  | succ l ih =>
    intro i h1 h2
    simp only [lin]
    rcases (show i < lo + l ∨ i = lo + l by omega) with c | c
    · exact (ih i h1 c).mul_right _
    · subst c; exact dvd_mul_left _ _

theorem lin_prime (lo : ℕ) (hlo : 1 ≤ lo) : ∀ len p, p.Prime → p ∣ lin lo len → p < lo + len := by
  intro len
  induction len with
  | zero => intro p hp h; simp [lin] at h; exact absurd h hp.ne_one
  | succ l ih =>
    intro p hp h
    simp only [lin] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with c | c
    · have := ih p hp c; omega
    · have := Nat.le_of_dvd (by omega) c; omega

theorem pr_dvd : ∀ f lo len i, lo ≤ i → i < lo + len → i ∣ pr f lo len := by
  intro f
  induction f with
  | zero => intro lo len i h1 h2; exact lin_dvd lo len i h1 h2
  | succ f ih =>
    intro lo len i h1 h2
    simp only [pr]
    split_ifs with a b
    · omega
    · have : i = lo := by omega
      subst this; exact dvd_rfl
    · rcases (show i < lo + len/2 ∨ lo + len/2 ≤ i by omega) with c | c
      · exact (ih lo (len/2) i h1 c).mul_right _
      · exact (ih (lo+len/2) (len - len/2) i c (by omega)).mul_left _

theorem pr_prime : ∀ f lo len p, 1 ≤ lo → p.Prime → p ∣ pr f lo len → p < lo + len := by
  intro f
  induction f with
  | zero => intro lo len p hlo hp h; exact lin_prime lo hlo len p hp h
  | succ f ih =>
    intro lo len p hlo hp h
    simp only [pr] at h
    split_ifs at h with a b
    · exact absurd (Nat.eq_one_of_dvd_one h) hp.ne_one
    · have := Nat.le_of_dvd (by omega) h; omega
    · rcases (Nat.Prime.dvd_mul hp).mp h with c | c
      · have := ih lo (len/2) p hlo hp c; omega
      · have := ih (lo+len/2) (len - len/2) p (by omega) hp c; omega

def code (F s k : ℕ) : ℕ := if 2 ≤ s ∧ s < k ∧ k < (s+1)*(s+1) then
  (if Nat.gcd k F = 1 then 1 else 0) else 2

theorem code_one (f s k : ℕ) (h : code (pr f 2 (s-1)) s k = 1) : k.Prime := by
  unfold code at h
  split_ifs at h with h1 h2
  all_goals try omega
  obtain ⟨hs2, hs, hk⟩ := h1
  by_contra hp
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  have hmf : 2 ≤ k.minFac := (Nat.minFac_prime (by omega)).two_le
  have hle : k.minFac ≤ s := by
    by_contra hlt
    have : (s+1)*(s+1) ≤ k.minFac ^ 2 := by nlinarith
    omega
  have hd : k.minFac ∣ pr f 2 (s-1) := pr_dvd f 2 (s-1) _ hmf (by omega)
  have := Nat.dvd_gcd (Nat.minFac_dvd k) hd
  rw [h2] at this
  exact absurd (Nat.eq_one_of_dvd_one this) (by omega)

theorem code_zero (f s k : ℕ) (h : code (pr f 2 (s-1)) s k = 0) : ¬ k.Prime := by
  unfold code at h
  split_ifs at h with h1 h2
  all_goals try omega
  obtain ⟨hs2, hs, hk⟩ := h1
  intro hp
  have hd : k ∣ pr f 2 (s-1) := by
    by_contra hnd
    exact h2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
  have := pr_prime f 2 (s-1) k (by omega) hp hd
  omega

def cntO (F s a : ℕ) : ℕ → Option ℕ
  | 0 => some 0
  | l+1 => (cntO F s a l).bind fun c =>
      if code F s (a+l) = 1 then some (c+1) else if code F s (a+l) = 0 then some c else none

theorem cntO_spec (f s a : ℕ) : ∀ l c, cntO (pr f 2 (s-1)) s a l = some c →
    Nat.count (fun i => (a+i).Prime) l = c := by
  intro l
  induction l with
  | zero => intro c h; simp [cntO] at h; subst h; simp
  | succ l ih =>
    intro c h
    simp only [cntO] at h
    cases hc : cntO (pr f 2 (s-1)) s a l with
    | none => rw [hc] at h; simp at h
    | some c0 =>
      rw [hc] at h
      simp only [Option.bind_some] at h
      rw [Nat.count_succ, ih c0 hc]
      split_ifs at h with h1 h2
      · simp at h; rw [if_pos (code_one f s _ h1)]; omega
      · simp at h; rw [if_neg (code_zero f s _ h2)]; omega

def chain (F s a base : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | (b,d)::rest => decide (a ≤ b) && decide (base ≤ d) &&
      decide (cntO F s (a+1) (b-a) = some (d-base)) && chain F s b d rest

theorem chain_spec (f s a0 : ℕ) : ∀ L a base, chain (pr f 2 (s-1)) s a base L = true →
    Nat.primeCounting a = Nat.primeCounting a0 + base →
    ∀ t ∈ L, Nat.primeCounting t.1 = Nat.primeCounting a0 + t.2 := by
  intro L
  induction L with
  | nil => intro a base _ _ t ht; simp at ht
  | cons hd rest ih =>
    obtain ⟨b, d⟩ := hd
    intro a base h ha
    simp only [chain, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hab, hbd⟩, hc⟩, hr⟩ := h
    have hb : Nat.primeCounting b = Nat.primeCounting a0 + d := by
      have := cntO_spec f s (a+1) (b-a) _ hc
      rw [Nat.primeCounting, Nat.primeCounting', show b + 1 = (a+1) + (b-a) by omega,
        Nat.count_add, this]
      rw [Nat.primeCounting, Nat.primeCounting'] at ha
      omega
    intro t ht
    rcases List.mem_cons.mp ht with e | e
    · subst e; exact hb
    · exact ih b d hr hb t e

end OMA_A247824_PrimeWindows

open OMA_A247824_PrimeWindows

set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_OeisA247824_conjecture_2_R2_H4_R2.H3 := by
  unfold OMA.R_OeisA247824_conjecture_2_R2_H4_R2.H3
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact chain_spec 20 9710 94085731 _ 94085731 0 (by decide +kernel) (Nat.add_zero _).symm
  · exact chain_spec 20 24300 590237761 _ 590237761 0 (by decide +kernel) (Nat.add_zero _).symm
  · exact chain_spec 20 102110 10425579253 _ 10425579253 0 (by decide +kernel) (Nat.add_zero _).symm
  · exact chain_spec 20 2 28006150079 _ 28006150079 0 (by decide +kernel) (Nat.add_zero _).symm
