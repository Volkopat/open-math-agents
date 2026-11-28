import OMAStatements.S_oeis_a060765
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

/-!
Reflect adjacent divisors by taking their complementary divisors. The
reflected gap divides the original number, which forces the original gap
to divide the product of the original neighbors. If the larger neighbor
is prime, the gap is coprime to both neighbors, so it equals one.
-/

namespace A060765

open Nat

private theorem quotient_pos {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) :
    0 < n / d :=
  Nat.div_pos (Nat.le_of_dvd hn hd) (Nat.pos_of_dvd_of_pos hd hn)

private theorem reverse_lt {n a b : ℕ} (hn : 0 < n) (ha : a ∣ n) (hb : b ∣ n)
    (hab : a < b) : n / b < n / a := by
  by_contra! h
  have h₁ := Nat.mul_lt_mul_of_pos_left hab (quotient_pos hn ha)
  have h₂ := Nat.mul_le_mul_right b h
  have h₃ := Nat.div_mul_cancel ha
  have h₄ := Nat.div_mul_cancel hb
  omega

private theorem neighbor {n p : ℕ} (hn : 0 < n) (hp : p.Prime) :
    ∃ a : ℕ, a ∣ n ∧ a < p ∧ (∀ d : ℕ, d ∣ n → a < d → d < p → False) := by
  let s := (n.divisors).filter (· < p)
  have hs : s.Nonempty := ⟨1, Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨one_dvd n, hn.ne'⟩, hp.one_lt⟩⟩
  let a := s.max' hs
  have ha : a ∈ s := Finset.max'_mem _ _
  obtain ⟨had, hap⟩ := Finset.mem_filter.mp ha
  refine ⟨a, (Nat.mem_divisors.mp had).1, hap, ?_⟩
  intro d hd had hdp
  have hds : d ∈ s := Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd,hn.ne'⟩,hdp⟩
  exact (not_lt_of_ge (Finset.le_max' s d hds)) had

private theorem gap_dvd_product {n a b : ℕ} (hn : 0 < n) (ha : a ∣ n) (hb : b ∣ n)
    (hab : a < b) (adj : ∀ d : ℕ, d ∣ n → a < d → d < b → False)
    (property : OMA.S_oeis_a060765.belongs n) :
    b - a ∣ a * b := by
  have hqa := Nat.div_dvd_of_dvd ha
  have hqb := Nat.div_dvd_of_dvd hb
  have hq := reverse_lt hn ha hb hab
  have hadj (d : ℕ) (hd : d ∣ n) (h₁ : n / b < d) (h₂ : d < n / a) : False := by
    apply adj (n / d) (Nat.div_dvd_of_dvd hd)
    · simpa only [Nat.div_div_self ha hn.ne'] using reverse_lt hn hd hqa h₂
    · simpa only [Nat.div_div_self hb hn.ne'] using reverse_lt hn hqb hd h₁
  obtain ⟨t,ht⟩ := property.2 (n / b) (n / a) hqb hqa hq hadj
  have hs : (n / a - n / b) * (a * b) = n * (b - a) := by
    rw [Nat.sub_mul, Nat.mul_sub, ← Nat.mul_assoc, Nat.div_mul_cancel ha,
      mul_comm a b, ← Nat.mul_assoc, Nat.div_mul_cancel hb]
  have he : (n / a - n / b) * (a * b) = (n / a - n / b) * ((b - a) * t) := by
    rw [hs]; nth_rw 1 [ht]; ring
  exact ⟨t, Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hq) he⟩

end A060765

theorem OMA.solution : type_of% @OMA.S_oeis_a060765.main := by
  intro n h p hp hpn
  obtain ⟨a,ha,hap,adj⟩ := A060765.neighbor h.1 hp
  have ha0 := Nat.pos_of_dvd_of_pos ha h.1
  have hc := Nat.coprime_of_lt_prime ha0.ne' hap hp
  have hgap := A060765.gap_dvd_product h.1 ha hpn hap adj h
  have hga : (p - a).Coprime a := (Nat.coprime_sub_self_left hap.le).mpr hc
  have hgp : (p - a).Coprime p := (Nat.coprime_self_sub_left hap.le).mpr hc.symm
  have hone := Nat.eq_one_of_dvd_coprimes (hga.mul_right hgp) (dvd_refl _) hgap
  have he : p - 1 = a := by omega
  rw [he]
  apply hc.symm.dvd_of_dvd_mul_left
  rwa [Nat.mul_comm, Nat.div_mul_cancel hpn]
