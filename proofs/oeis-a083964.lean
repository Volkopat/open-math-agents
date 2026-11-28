import OMAStatements.S_oeis_a083964
import Mathlib

namespace A083964Proof
open OMA.S_oeis_a083964

lemma ofDigits_rep (d : ℕ) (l : List ℕ) (h : 10 ^ l.length ≡ 1 [MOD d]) (t : ℕ) :
    Nat.ofDigits 10 (List.replicate t l).flatten ≡ t * Nat.ofDigits 10 l [MOD d] := by
  induction t with
  | zero => simp [Nat.ModEq]
  | succ t ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append]
    have h1 : 10 ^ l.length * Nat.ofDigits 10 (List.replicate t l).flatten
        ≡ 1 * (t * Nat.ofDigits 10 l) [MOD d] := Nat.ModEq.mul h ih
    have h2 := Nat.ModEq.add_left (Nat.ofDigits 10 l) h1
    have e : (t + 1) * Nat.ofDigits 10 l = Nat.ofDigits 10 l + 1 * (t * Nat.ofDigits 10 l) := by
      ring
    rw [e]
    exact h2

lemma last_of_split (D T : List ℕ) (hD : D ≠ []) :
    ∀ (M : List ℕ) (h : M ≠ []), M = T ++ D → M.getLast h = D.getLast hD := by
  intro M h hM
  subst hM
  exact List.getLast_append_of_ne_nil _ hD

lemma core (d : ℕ) (hd : 1 ≤ d) (hcop : Nat.Coprime 10 d) :
    ∃ m, 0 < m ∧ d ∣ m ∧ (Nat.digits 10 m).reverse = Nat.digits 10 m ∧
      ∃ tail : List ℕ, Nat.digits 10 m = tail ++ Nat.digits 10 d := by
  obtain ⟨c, hc⟩ : ∃ c, Nat.totient d = c + 1 :=
    ⟨Nat.totient d - 1, by have := Nat.totient_pos.mpr hd; omega⟩
  obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hDne : Nat.digits 10 d ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have hDlt : ∀ x ∈ Nat.digits 10 d, x < 10 := fun x hx => Nat.digits_lt_base (by norm_num) hx
  have hDlast : (Nat.digits 10 d).getLast hDne ≠ 0 := Nat.getLast_digit_ne_zero 10 (by omega)
  generalize Nat.digits 10 d = D at hDne hDlt hDlast ⊢
  obtain ⟨l, hl⟩ : ∃ l, l = D.reverse ++ (List.replicate (2 * D.length * c) 0 ++ D) := ⟨_, rfl⟩
  have hlrev : l.reverse = l := by
    rw [hl]
    simp
  have hlen : l.length = Nat.totient d * (2 * D.length) := by
    rw [hc, hl]
    simp
    ring
  have hpow : 10 ^ l.length ≡ 1 [MOD d] := by
    rw [hlen, pow_mul]
    have h1 := (Nat.ModEq.pow_totient hcop).pow (2 * D.length)
    rwa [one_pow] at h1
  have hsplit : (List.replicate d l).flatten =
      ((List.replicate e l).flatten ++ (D.reverse ++ List.replicate (2 * D.length * c) 0))
        ++ D := by
    rw [he, List.replicate_succ', List.flatten_append, hl]
    simp
  have hrev : ((List.replicate d l).flatten).reverse = (List.replicate d l).flatten := by
    rw [List.reverse_flatten, List.map_replicate, List.reverse_replicate, hlrev]
  have hne : (List.replicate d l).flatten ≠ [] := by
    rw [hsplit]
    simp [hDne]
  have hlt : ∀ x ∈ (List.replicate d l).flatten, x < 10 := by
    intro x hx
    rw [List.mem_flatten] at hx
    obtain ⟨l', hl', hx⟩ := hx
    rw [List.eq_of_mem_replicate hl', hl] at hx
    simp only [List.mem_append, List.mem_reverse, List.mem_replicate] at hx
    rcases hx with hx | ⟨-, rfl⟩ | hx
    · exact hDlt x hx
    · norm_num
    · exact hDlt x hx
  have hlast : ∀ h : (List.replicate d l).flatten ≠ [],
      ((List.replicate d l).flatten).getLast h ≠ 0 := by
    intro h
    rw [last_of_split D _ hDne _ h hsplit]
    exact hDlast
  have hdig := Nat.digits_ofDigits 10 (by norm_num) _ hlt hlast
  refine ⟨Nat.ofDigits 10 (List.replicate d l).flatten, ?_, ?_, ?_, ?_⟩
  · by_contra h0
    have hz : Nat.ofDigits 10 (List.replicate d l).flatten = 0 := by omega
    rw [hz, Nat.digits_zero] at hdig
    exact hne hdig.symm
  · have h1 := ofDigits_rep d l hpow d
    exact (Nat.modEq_zero_iff_dvd).mp
      (h1.trans ((Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right d _)))
  · rw [hdig]
    exact hrev
  · rw [hdig]
    exact ⟨_, hsplit⟩

end A083964Proof

open OMA.S_oeis_a083964 A083964Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a083964.main := by
  intro n hn h5
  have hodd : ¬ 2 ∣ (2 * n - 1) := by omega
  have c2 : Nat.Coprime 2 (2 * n - 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
  have c5 : Nat.Coprime 5 (2 * n - 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5
  have c10 : Nat.Coprime 10 (2 * n - 1) := Nat.Coprime.mul_left c2 c5
  have h : ∃ m, admissible n m := core (2 * n - 1) (by omega) c10
  have key : ∀ (inst : DecidablePred (admissible n)), @Nat.find _ inst h ≠ 0 :=
    fun inst => (@Nat.find_spec _ inst h).1.ne'
  unfold a
  rw [dif_pos h]
  exact key _
