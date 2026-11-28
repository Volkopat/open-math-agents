import OMAStatements.S_oeis_a097602

namespace P097602
open OMA.S_oeis_a097602

def G (j k : ℕ) : ℕ := if k ≤ 3 then (3*j+1)^2 + k*(2*j+1) else (3*j+2)^2 + (k-3)*(2*j+2)

def D (j k : ℕ) : ℕ := if k < 3 then 2*j+1 else 2*j+2

lemma no_sq_between (t m : ℕ) (h1 : t^2 < m^2) (h2 : m^2 < (t+1)^2) : False := by
  have a1 : t < m := by
    by_contra hc
    push_neg at hc
    have : m^2 ≤ t^2 := Nat.pow_le_pow_left hc 2
    omega
  have a2 : m < t + 1 := by
    by_contra hc
    push_neg at hc
    have : (t+1)^2 ≤ m^2 := Nat.pow_le_pow_left hc 2
    omega
  omega

lemma not_sq (t x : ℕ) (h1 : t^2 < x) (h2 : x < (t+1)^2) : ¬ IsSquare x := by
  rintro ⟨r, rfl⟩
  exact no_sq_between t r (by rw [sq r]; exact h1) (by rw [sq r]; exact h2)

lemma sq_inj (m t : ℕ) (h : m^2 = t^2) : m = t := by
  rcases lt_trichotomy m t with hc | hc | hc
  · have := Nat.pow_lt_pow_left hc (by norm_num : (2:ℕ) ≠ 0)
    omega
  · exact hc
  · have := Nat.pow_lt_pow_left hc (by norm_num : (2:ℕ) ≠ 0)
    omega

lemma stepG (j k : ℕ) (hk : k < 9) : G j k + D j k = G (j + (k+1)/9) ((k+1)%9) := by
  interval_cases k <;> simp [G, D] <;> ring

lemma G_sq (j k : ℕ) (hk : k < 9) : IsSquare (G j k) ↔ (k = 0 ∨ k = 3) := by
  interval_cases k
  · simp only [true_or, iff_true]
    exact ⟨3*j+1, by simp [G]; ring⟩
  · simp
    exact not_sq (3*j+1) _ (by simp [G] <;> nlinarith) (by simp [G] <;> nlinarith)
  · simp
    exact not_sq (3*j+1) _ (by simp [G] <;> nlinarith) (by simp [G] <;> nlinarith)
  · simp only [or_true, iff_true]
    exact ⟨3*j+2, by simp [G]; ring⟩
  · simp
    exact not_sq (3*j+2) _ (by simp [G] <;> nlinarith) (by simp [G] <;> nlinarith)
  · simp
    exact not_sq (3*j+2) _ (by simp [G] <;> nlinarith) (by simp [G] <;> nlinarith)
  · simp
    exact not_sq (3*j+3) _ (by simp [G] <;> nlinarith) (by simp [G] <;> nlinarith)
  · simp
    exact not_sq (3*j+3) _ (by simp [G] <;> nlinarith) (by simp [G] <;> nlinarith)
  · simp
    exact not_sq (3*j+3) _ (by simp [G] <;> nlinarith) (by simp [G] <;> nlinarith)

lemma stepD (j k : ℕ) (hk : k < 9) :
    D j k + (if IsSquare (G (j + (k+1)/9) ((k+1)%9)) then 1 else 0)
      = D (j + (k+1)/9) ((k+1)%9) := by
  have hs := G_sq (j + (k+1)/9) ((k+1)%9) (Nat.mod_lt _ (by norm_num))
  by_cases hc : IsSquare (G (j + (k+1)/9) ((k+1)%9))
  · rw [if_pos hc]
    rw [hs] at hc
    interval_cases k <;> simp_all [D] <;> omega
  · rw [if_neg hc]
    rw [hs] at hc
    interval_cases k <;> simp_all [D] <;> omega

lemma card_succ (a : ℕ → ℕ) (n : ℕ) :
    ((Finset.Icc 1 (n+1)).filter fun i => IsSquare (a i)).card
      = ((Finset.Icc 1 n).filter fun i => IsSquare (a i)).card
        + (if IsSquare (a (n+1)) then 1 else 0) := by
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_Icc_succ_top (by omega)]

lemma inv (a : ℕ → ℕ) (h : IsA097602 a) (n : ℕ) (hn : 1 ≤ n) :
    a n = G ((n-1)/9) ((n-1)%9) ∧
    ((Finset.Icc 1 n).filter fun i => IsSquare (a i)).card = D ((n-1)/9) ((n-1)%9) := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨by simp [G, h.1], ?_⟩
    rw [show Finset.Icc 1 1 = Finset.Icc 1 (0+1) from rfl, card_succ]
    simp [D, h.1]
  | succ n hn ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e1 : (n + 1 - 1) / 9 = (n-1)/9 + ((n-1)%9 + 1)/9 := by omega
    have e2 : (n + 1 - 1) % 9 = ((n-1)%9 + 1)%9 := by omega
    have hk : (n-1)%9 < 9 := Nat.mod_lt _ (by norm_num)
    have ha : a (n+1) = G ((n-1)/9) ((n-1)%9) + D ((n-1)/9) ((n-1)%9) := by
      rw [h.2 n hn, ih1, ih2]
    rw [stepG _ _ hk] at ha
    rw [e1, e2]
    refine ⟨ha, ?_⟩
    rw [card_succ, ih2, ha]
    exact stepD _ _ hk

end P097602

theorem OMA.solution : type_of% @OMA.S_oeis_a097602.main := by
  intro a h m
  constructor
  · rintro ⟨n, hn, hm⟩
    obtain ⟨h1, -⟩ := P097602.inv a h n hn
    have hk : (n-1)%9 < 9 := Nat.mod_lt _ (by norm_num)
    have hsq : IsSquare (P097602.G ((n-1)/9) ((n-1)%9)) := ⟨m, by rw [← h1, hm, sq]⟩
    rw [P097602.G_sq _ _ hk] at hsq
    rcases hsq with h0 | h3
    · rw [h0] at h1
      have : m = 3 * ((n-1)/9) + 1 :=
        P097602.sq_inj _ _ (by rw [← hm, h1]; simp [P097602.G])
      omega
    · rw [h3] at h1
      have : m = 3 * ((n-1)/9) + 2 :=
        P097602.sq_inj _ _ (by rw [← hm, h1]; simp [P097602.G]; ring)
      omega
  · intro hm
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h1 | h2
    · obtain ⟨q, rfl⟩ : ∃ q, m = 3*q+1 := ⟨m/3, by omega⟩
      refine ⟨9 * q + 1, by omega, ?_⟩
      obtain ⟨e, -⟩ := P097602.inv a h (9 * q + 1) (by omega)
      rw [e]
      have q1 : (9 * q + 1 - 1)/9 = q := by omega
      have q2 : (9 * q + 1 - 1)%9 = 0 := by omega
      rw [q1, q2]
      simp [P097602.G]
    · obtain ⟨q, rfl⟩ : ∃ q, m = 3*q+2 := ⟨m/3, by omega⟩
      refine ⟨9 * q + 4, by omega, ?_⟩
      obtain ⟨e, -⟩ := P097602.inv a h (9 * q + 4) (by omega)
      rw [e]
      have q1 : (9 * q + 4 - 1)/9 = q := by omega
      have q2 : (9 * q + 4 - 1)%9 = 3 := by omega
      rw [q1, q2]
      simp [P097602.G]
      ring
