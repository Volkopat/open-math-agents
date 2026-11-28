import OMAStatements.S_oeis_a138904
import Mathlib

namespace OMA.A138904Proof

open OMA.S_oeis_a138904

lemma rotate_mul_self {l : List ℕ} {p : ℕ} (hp : l.rotate p = l) (q : ℕ) :
    l.rotate (p * q) = l := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← List.rotate_rotate, ih, hp]

lemma count_mult (p d : ℕ) (hp : 0 < p) :
    ((Finset.range (p * d)).filter (fun r => p ∣ r)).card = d := by
  have e : (Finset.range (p * d)).filter (fun r => p ∣ r) =
      (Finset.range d).image (fun q => p * q) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hr, q, rfl⟩
      exact ⟨q, (Nat.mul_lt_mul_left hp).mp hr, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(Nat.mul_lt_mul_left hp).mpr hq, dvd_mul_right _ _⟩
  rw [e, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hp h)]
  simp

lemma count_of_iff {l : List ℕ} {p : ℕ} (hp : 0 < p) (hpl : p ∣ l.length)
    (h : ∀ r, l.rotate r = l ↔ p ∣ r) :
    ((Finset.range l.length).filter (fun r => l.rotate r = l)).card = l.length / p := by
  obtain ⟨d, hd⟩ := hpl
  have e : (Finset.range l.length).filter (fun r => l.rotate r = l) =
      (Finset.range (p * d)).filter (fun r => p ∣ r) := by
    rw [hd]; exact Finset.filter_congr (fun r _ => h r)
  rw [e, count_mult p d hp, hd, Nat.mul_div_cancel_left d hp]

lemma period_exists (l : List ℕ) (hl : 0 < l.length) :
    ∃ p, 0 < p ∧ p ∣ l.length ∧ ∀ r, l.rotate r = l ↔ p ∣ r := by
  classical
  have hex : ∃ p, 0 < p ∧ l.rotate p = l := ⟨l.length, hl, List.rotate_length l⟩
  have hp : 0 < Nat.find hex ∧ l.rotate (Nat.find hex) = l := Nat.find_spec hex
  have key : ∀ r, l.rotate r = l ↔ Nat.find hex ∣ r := by
    intro r
    constructor
    · intro hr
      have h1 : l.rotate (r % Nat.find hex) = l := by
        have e := Nat.div_add_mod r (Nat.find hex)
        have h2 : l.rotate (Nat.find hex * (r / Nat.find hex) + r % Nat.find hex) = l := by
          rw [e]; exact hr
        rw [← List.rotate_rotate, rotate_mul_self hp.2] at h2
        exact h2
      by_contra hnd
      have hpos : 0 < r % Nat.find hex :=
        Nat.pos_of_ne_zero (fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0))
      exact Nat.find_min hex (Nat.mod_lt r hp.1) ⟨hpos, h1⟩
    · rintro ⟨q, rfl⟩
      exact rotate_mul_self hp.2 q
  exact ⟨Nat.find hex, hp.1, (key l.length).mp (List.rotate_length l), key⟩

lemma a_dvd (m n : ℕ) (hm : (Nat.digits 2 m).length = n) (hn : 1 ≤ n) : a m ∣ n := by
  obtain ⟨p, hp, hpl, h⟩ := period_exists (Nat.digits 2 m) (by omega)
  have : a m = (Nat.digits 2 m).length / p := count_of_iff hp hpl h
  rw [this, hm]
  rw [hm] at hpl
  exact Nat.div_dvd_of_dvd hpl

/-- The word with a one at every position `i` with `p ∣ i + 1`. -/
def word (n p : ℕ) : List ℕ := (List.range n).map (fun i => if p ∣ i + 1 then 1 else 0)

lemma word_length (n p : ℕ) : (word n p).length = n := by simp [word]

lemma word_getElem (n p k : ℕ) (hk : k < (word n p).length) :
    (word n p)[k] = if p ∣ k + 1 then 1 else 0 := by
  simp [word]

lemma word_rotate_iff (n p : ℕ) (hp : 0 < p) (hpn : p ∣ n) (hpn' : p ≤ n) (r : ℕ) :
    (word n p).rotate r = word n p ↔ p ∣ r := by
  constructor
  · intro heq
    have hk : p - 1 < ((word n p).rotate r).length := by
      rw [List.length_rotate, word_length]; omega
    have hk' : p - 1 < (word n p).length := by rw [word_length]; omega
    have e := List.getElem_of_eq heq hk
    rw [List.getElem_rotate, word_getElem, word_getElem, word_length] at e
    have hp1 : p - 1 + 1 = p := by omega
    rw [hp1, if_pos dvd_rfl] at e
    have hd : p ∣ (p - 1 + r) % n + 1 := by
      by_contra hc
      rw [if_neg hc] at e
      exact absurd e (by norm_num)
    have h1 : (p - 1 + r) % n + 1 ≡ p - 1 + r + 1 [MOD p] :=
      (show (p - 1 + r) % n ≡ p - 1 + r [MOD p] from Nat.mod_mod_of_dvd _ hpn).add_right 1
    have h2 : p - 1 + r + 1 = r + p := by omega
    rw [h2] at h1
    have h3 : r + p ≡ r [MOD p] := by
      show (r + p) % p = r % p
      simp
    exact ((h1.trans h3).dvd_iff dvd_rfl).mp hd
  · intro hr
    apply List.ext_getElem (by simp)
    intro k h1 h2
    rw [List.getElem_rotate, word_getElem, word_getElem, word_length]
    have e1 : (k + r) % n + 1 ≡ k + r + 1 [MOD p] :=
      (show (k + r) % n ≡ k + r [MOD p] from Nat.mod_mod_of_dvd _ hpn).add_right 1
    have e2 : k + r + 1 ≡ k + 1 [MOD p] := by
      have : k + 1 + r ≡ k + 1 + 0 [MOD p] :=
        (Nat.ModEq.refl (k + 1)).add (Nat.modEq_zero_iff_dvd.mpr hr)
      rw [Nat.add_zero, Nat.add_right_comm] at this
      exact this
    exact if_congr ((e1.trans e2).dvd_iff dvd_rfl) rfl rfl

lemma exists_of_dvd (n d : ℕ) (hn : 1 ≤ n) (hd : d ∣ n) :
    ∃ m : ℕ, (Nat.digits 2 m).length = n ∧ a m = d := by
  obtain ⟨p, hp⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hp0 : 0 < p := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hpn : p ∣ n := ⟨d, by rw [hp, Nat.mul_comm]⟩
  have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have hdig : Nat.digits 2 (Nat.ofDigits 2 (word n p)) = word n p := by
    apply Nat.digits_ofDigits 2 (by norm_num)
    · intro x hx
      simp only [word, List.mem_map] at hx
      obtain ⟨i, -, rfl⟩ := hx
      split_ifs <;> norm_num
    · intro hne
      rw [List.getLast_eq_getElem, word_getElem, word_length]
      have : n - 1 + 1 = n := by omega
      rw [this, if_pos hpn]
      norm_num
  refine ⟨Nat.ofDigits 2 (word n p), by rw [hdig, word_length], ?_⟩
  unfold a
  rw [hdig]
  rw [count_of_iff hp0 (by rw [word_length]; exact hpn) (word_rotate_iff n p hp0 hpn hpn'),
    word_length, hp, Nat.mul_div_cancel _ hp0]

end OMA.A138904Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a138904.main := by
  intro n hn
  ext s
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact OMA.A138904Proof.a_dvd m n hm hn
  · intro hs
    exact OMA.A138904Proof.exists_of_dvd n s hn hs
