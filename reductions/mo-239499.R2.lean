import OMAStatements.S_mo_239499
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Semiprime candidates in the square-plus-four test

For a passing odd candidate N = p q with q prime, Fermat's theorem forces
q to divide 2^p - 2. Exact prime factorizations then exclude every semiprime
with smaller prime at most 73, for all odd n. The same cofactor condition
applies separately to every prime factor of a composite with three or more factors.

Source: https://mathoverflow.net/questions/239499
Credit: @wtho704
-/

namespace OMA.R_mo_239499_R2

private theorem frobenius_nat (p m : ℕ) [Fact p.Prime] : (m : ZMod p) ^ p = m := by
  simpa only [frobenius_def] using map_natCast (frobenius (ZMod p) p) m

private theorem fermat_nat (p m : ℕ) [hp : Fact p.Prime] (hm : (m : ZMod p) ≠ 0) :
    (m : ZMod p) ^ (p - 1) = 1 := by
  apply mul_right_cancel₀ hm
  rw [one_mul, ← pow_succ, Nat.sub_add_cancel hp.out.one_le, frobenius_nat]

/-- In the prime field, (n + 2)^4 = -64. Fermat's theorem at n + 2 and at
2 gives the required minus sign since (N - 1) / 4 is odd. -/
private theorem prime_passes {n : ℕ} (hn : n % 2 = 1) (hp : (4 + n ^ 2).Prime) :
    4 + n ^ 2 ∣ 2 ^ ((4 + n ^ 2 - 1) / 2) + 1 := by
  let N := 4 + n ^ 2
  change N ∣ 2 ^ ((N - 1) / 2) + 1
  let _ : Fact N.Prime := ⟨hp⟩
  have hm : N % 8 = 5 := by
    have hres : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
    dsimp [N]
    rw [Nat.add_mod, Nat.pow_mod]
    rcases hres with h | h | h | h <;> norm_num [h]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, N = 8 * k + 5 := ⟨N / 8, by omega⟩
  have hle : n ≤ n ^ 2 := by simpa [pow_two] using Nat.le_mul_self n
  have hnz (m : ℕ) (hpos : 0 < m) (hlt : m < N) : (m : ZMod N) ≠ 0 := by
    exact fun h => (Nat.not_dvd_of_pos_of_lt hpos hlt) ((ZMod.natCast_eq_zero_iff m N).mp h)
  have ht : (2 : ZMod N) ^ (N - 1) = 1 := fermat_nat N 2 (hnz 2 (by decide) (by omega))
  have hx := fermat_nat N (n + 2) (hnz (n + 2) (by omega) (by dsimp [N]; omega))
  push_cast at hx
  have hs := (ZMod.natCast_eq_zero_iff (4 + n ^ 2) N).mpr (dvd_refl N)
  push_cast at hs
  have hfour : ((n : ZMod N) + 2) ^ 4 = -64 := by
    linear_combination ((n : ZMod N) ^ 2 + 8 * n + 20) * hs
  rw [show N - 1 = 4 * (2 * k + 1) by omega, pow_mul, hfour,
    show (-64 : ZMod N) = -(2 ^ 6) by norm_num,
    (show Odd (2 * k + 1) from ⟨k, rfl⟩).neg_pow, ← pow_mul,
    show 6 * (2 * k + 1) = (N - 1) + (N - 1) / 2 by omega, pow_add, ht, one_mul] at hx
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  linear_combination -hx

/-- A prime factor q of a passing odd candidate with cofactor p divides 2^p - 2. -/
private theorem prime_factor_constraint {N p q : ℕ} (ho : N % 2 = 1) (hq : q.Prime)
    (hN : N = p * q) (hpass : N ∣ 2 ^ ((N - 1) / 2) + 1) : q ∣ 2 ^ p - 2 := by
  let _ : Fact q.Prime := ⟨hq⟩
  have hqN : q ∣ N := hN ▸ dvd_mul_left q p
  have hz := (ZMod.natCast_eq_zero_iff _ q).mpr (hqN.trans hpass)
  push_cast at hz
  have hm : (2 : ZMod q) ^ ((N - 1) / 2) = -1 := eq_neg_of_add_eq_zero_left hz
  have hfull : (2 : ZMod q) ^ N = 2 := by
    conv_lhs => rw [show N = (N - 1) / 2 * 2 + 1 by omega]
    rw [pow_succ, pow_mul, hm]
    ring
  have hred : (2 : ZMod q) ^ p = 2 := by
    calc
      _ = ((2 : ZMod q) ^ q) ^ p := by rw [show (2 : ZMod q) ^ q = 2 from frobenius_nat q 2]
      _ = (2 : ZMod q) ^ N := by rw [← pow_mul, Nat.mul_comm q p, ← hN]
      _ = 2 := hfull
  apply Nat.dvd_of_mod_eq_zero
  apply Nat.sub_mod_eq_zero_of_mod_eq
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast
  exact hred

set_option maxRecDepth 20000 in
private theorem small_factor_certificate (p : ℕ) (hp : p.Prime) (hb : p ≤ 73) :
    ∃ L : List ℕ, L.prod = 2 ^ p - 2 ∧ ∀ q ∈ L, q.Prime ∧
      (q < p ∨ (p * q - 4).sqrt ^ 2 ≠ p * q - 4 ∨ (p * q - 4).sqrt % 2 = 0) := by
  have cover : ∀ j : Fin 74, j.val.Prime → j.val ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73] := by decide
  have h := cover ⟨p, by omega⟩ hp
  change p ∈ _ at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨[2], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 5], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 3, 7], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 11, 31], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 3, 5, 7, 13], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 5, 17, 257], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 3, 3, 7, 19, 73], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 23, 89, 683], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 5, 29, 43, 113, 127], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 3, 7, 11, 31, 151, 331], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 3, 3, 5, 7, 13, 19, 37, 73, 109], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 5, 5, 11, 17, 31, 41, 61681], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 3, 7, 7, 43, 127, 337, 5419], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 47, 178481, 2796203], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 5, 53, 157, 1613, 2731, 8191], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 59, 233, 1103, 2089, 3033169], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 3, 5, 5, 7, 11, 13, 31, 41, 61, 151, 331, 1321], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 3, 7, 23, 67, 89, 683, 20857, 599479], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 11, 31, 43, 71, 127, 281, 86171, 122921], by norm_num [List.prod_cons, List.forall_mem_cons]⟩
  · exact ⟨[2, 3, 3, 3, 5, 7, 13, 17, 19, 37, 73, 109, 241, 433, 38737], by norm_num [List.prod_cons, List.forall_mem_cons]⟩

private theorem prime_mem_factors {q : ℕ} (hq : q.Prime) (L : List ℕ)
    (hL : ∀ r ∈ L, r.Prime) (hd : q ∣ L.prod) : q ∈ L := by
  induction L with
  | nil =>
    exact (hq.not_dvd_one hd).elim
  | cons r rs ih =>
    rcases hq.dvd_mul.mp hd with h | h
    · exact List.mem_cons.mpr (.inl ((Nat.prime_dvd_prime_iff_eq hq (hL r (by simp))).mp h))
    · exact List.mem_cons.mpr (.inr (ih (fun s hs => hL s (by simp [hs])) h))

private theorem small_semiprime {n p q : ℕ} (hn : n % 2 = 1) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≤ q) (hN : 4 + n ^ 2 = p * q) (hdiv : q ∣ 2 ^ p - 2) : 73 < p := by
  by_contra! hb
  obtain ⟨L, hprod, hall⟩ := small_factor_certificate p hp hb
  have hmem := prime_mem_factors hq L (fun r hr => (hall r hr).1) (hprod ▸ hdiv)
  have he : p * q - 4 = n ^ 2 := by omega
  have hh := (hall q hmem).2
  rw [he, Nat.sqrt_eq'] at hh
  omega

private theorem split_composite {m : ℕ} (hm : 2 ≤ m) (hprime : ¬ m.Prime) :
    ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ a * b = m := by
  obtain ⟨a, b, ha, hb, he⟩ := (Nat.not_prime_iff_exists_mul_eq hm).mp hprime
  refine ⟨a, b, ?_, ?_, he⟩
  · by_contra! h
    have hz : a = 0 ∨ a = 1 := by omega
    rcases hz with rfl | rfl <;> simp_all
  · by_contra! h
    have hz : b = 0 ∨ b = 1 := by omega
    rcases hz with rfl | rfl <;> simp_all

/-- Products of two primes. A passing candidate can only have a smaller prime
larger than 73, and each prime must satisfy the cofactor divisibility test. -/
def H1 : Prop := ∀ n p q : ℕ, n % 2 = 1 → p.Prime → q.Prime → 73 < p → p ≤ q →
    4 + n ^ 2 = p * q → q ∣ 2 ^ p - 2 → p ∣ 2 ^ q - 2 →
    ¬ (p * q ∣ 2 ^ ((p * q - 1) / 2) + 1)

/-- Candidates with three or more prime factors, counted with multiplicity. -/
def H2 : Prop := ∀ n a b c : ℕ, n % 2 = 1 → 2 ≤ a → 2 ≤ b → 2 ≤ c →
    4 + n ^ 2 = a * b * c →
    (∀ r : ℕ, r.Prime → r ∣ 4 + n ^ 2 → r ∣ 2 ^ ((4 + n ^ 2) / r) - 2) →
    ¬ (4 + n ^ 2 ∣ 2 ^ ((4 + n ^ 2 - 1) / 2) + 1)

theorem main : H1 → H2 → type_of% @OMA.S_mo_239499.main := by
  intro hsemi hthree n hn
  change (4 + n ^ 2).Prime ↔ 4 + n ^ 2 ∣ 2 ^ ((4 + n ^ 2 - 1) / 2) + 1
  refine ⟨prime_passes hn, ?_⟩
  intro hpass
  by_contra hcomp
  let N := 4 + n ^ 2
  have hlarge : 2 ≤ N := by dsimp [N]; omega
  have hodd : N % 2 = 1 := by simp [N, Nat.add_mod, Nat.pow_mod n 2 2, hn]
  have all_factors (r : ℕ) (hr : r.Prime) (hd : r ∣ N) : r ∣ 2 ^ (N / r) - 2 :=
    prime_factor_constraint hodd hr (Nat.div_mul_cancel hd).symm hpass
  have semi (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hle : p ≤ q) (he : N = p * q) :
      False := by
    have hqtest := prime_factor_constraint hodd hq he hpass
    have hptest := prime_factor_constraint hodd hp (he.trans (Nat.mul_comm p q)) hpass
    have hb := small_semiprime hn hp hq hle he hqtest
    exact hsemi n p q hn hp hq hb hle he hqtest hptest (he ▸ hpass)
  obtain ⟨a, b, ha, hb, hab⟩ := split_composite hlarge hcomp
  by_cases hpa : a.Prime
  · by_cases hpb : b.Prime
    · rcases le_total a b with h | h
      · exact semi a b hpa hpb h hab.symm
      · exact semi b a hpb hpa h (hab.symm.trans (Nat.mul_comm a b))
    · obtain ⟨u, v, hu, hv, huv⟩ := split_composite hb hpb
      exact hthree n a u v hn ha hu hv (by rw [mul_assoc, huv]; exact hab.symm) all_factors hpass
  · obtain ⟨u, v, hu, hv, huv⟩ := split_composite ha hpa
    exact hthree n u v b hn hu hv hb (by rw [huv]; exact hab.symm) all_factors hpass

end OMA.R_mo_239499_R2
