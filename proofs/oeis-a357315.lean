import OMAStatements.S_oeis_a357315
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

open Finset

namespace SquarefreeNeighbors

private lemma fifth_root_interval (m : ℕ) : ∃ x : ℕ, x^5 ≤ m ∧ m < (x+1)^5 := by
  have h : ∃ y : ℕ, m < (y+1)^5 := by
    exact ⟨m, (Nat.lt_succ_self _).trans_le (Nat.le_self_pow (by decide) _)⟩
  let x := Nat.find h
  refine ⟨x, ?_, Nat.find_spec h⟩
  by_cases h0 : x = 0
  · simp [h0]
  obtain ⟨y, hy⟩ := Nat.exists_eq_succ_of_ne_zero h0
  rw [hy]
  exact Nat.le_of_not_gt (Nat.find_min h (show y < x by omega))

/-- Six disjoint Bertrand intervals above x contain at least two primes not
dividing m, as the product of any five already exceeds m. -/
private lemma missing_primes {m x : ℕ} (hm : 0 < m) (hx : 0 < x) (hlim : m < (x+1)^5) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ ¬ p ∣ m ∧ ¬ q ∣ m ∧ p ≤ 64*x ∧ q ≤ 64*x := by
  classical
  choose p hp hlo hhi using fun i : Fin 6 =>
    Nat.exists_prime_lt_and_le_two_mul (2 ^ i.val * x) (by positivity)
  have upper (i : Fin 6) : p i ≤ 2^(i.val+1) * x := by
    simpa [pow_succ', Nat.mul_assoc] using hhi i
  have mono : StrictMono p := by
    intro i j hij
    have hij' : i.val+1 ≤ j.val := hij
    exact (upper i).trans_lt <|
      (Nat.mul_le_mul_right x (Nat.pow_le_pow_right (by decide : 0 < 2) hij')).trans_lt (hlo j)
  have lower (i : Fin 6) : x + 1 ≤ p i := by
    have he : 1 ≤ 2 ^ i.val := Nat.one_le_pow _ _ (by decide)
    have h := Nat.mul_le_mul_right x he
    exact (by simpa using h : x ≤ 2 ^ i.val * x).trans_lt (hlo i)
  have cap (i : Fin 6) : p i ≤ 64*x :=
    (upper i).trans (Nat.mul_le_mul_right x (Nat.pow_le_pow_right (by decide : 0 < 2) i.isLt))
  let s := univ.filter fun i : Fin 6 => p i ∣ m
  have prod_dvd : (∏ i ∈ s, p i) ∣ m := by
    refine Finset.prod_dvd_of_isRelPrime ?_ ?_
    · intro i _ j _ hij
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp i) (hp j)).2 (mono.injective.ne hij))
    · intro i hi
      simpa [s] using hi
  have hc : s.card < 5 := by
    by_contra! hge
    have prod_le : (x+1)^s.card ≤ ∏ i ∈ s, p i := by
      simpa using Finset.prod_le_prod' (s := s) (fun i _ => lower i)
    have := (Nat.pow_le_pow_right (by omega : 0 < x+1) hge).trans
      (prod_le.trans (Nat.le_of_dvd hm prod_dvd))
    omega
  have hc' : 1 < sᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hc'
  exact ⟨p i, p j, hp i, hp j, mono.injective.ne hij, by simpa [s] using hi,
    by simpa [s] using hj, cap i, cap j⟩

/-- Inside a complete residue interval, the CRT produces a multiple of m
that is one above a multiple of p² and one below a multiple of q². -/
private lemma witness {m p q : ℕ} (hm : 0 < m) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpm : ¬ p ∣ m) (hqm : ¬ q ∣ m) (hsize : p^2*q^2 ≤ m) :
    ∃ k : ℕ, 0 < k ∧ k < m ∧ ¬ Squarefree (m*k-1) ∧ ¬ Squarefree (m*k+1) := by
  let M := p^2*q^2
  have hp2 : 1 < p^2 := one_lt_pow₀ hp.one_lt (by decide)
  have hq2 : 1 < q^2 := one_lt_pow₀ hq.one_lt (by decide)
  have hpq2 := Nat.coprime_pow_primes 2 2 hp hq hpq
  let t := Nat.chineseRemainder hpq2 1 (q^2-1)
  have hmM : m.Coprime M := Nat.coprime_mul_iff_right.mpr
    ⟨hp.coprime_pow_of_not_dvd hpm, hq.coprime_pow_of_not_dvd hqm⟩
  let y := Nat.chineseRemainder hmM 0 t.val
  obtain ⟨k, hk⟩ := Nat.modEq_zero_iff_dvd.mp y.property.1
  have hyp : m*k ≡ 1 [MOD p^2] := by
    rw [← hk]
    exact (y.property.2.of_dvd (dvd_mul_right (p^2) (q^2))).trans t.property.1
  have hyq : m*k ≡ q^2-1 [MOD q^2] := by
    rw [← hk]
    exact (y.property.2.of_dvd (dvd_mul_left (q^2) (p^2))).trans t.property.2
  have hkpos : 0 < k := by
    by_contra! h
    have hk0 : k = 0 := by omega
    simp [Nat.ModEq, hk0, Nat.mod_eq_of_lt hp2] at hyp
  have hkm : k < m := by
    have hylt : y.val < m*M := Nat.chineseRemainder_lt_mul hmM 0 t.val hm.ne' (by dsimp [M]; positivity)
    rw [hk] at hylt
    exact (Nat.lt_of_mul_lt_mul_left hylt).trans_le hsize
  refine ⟨k, hkpos, hkm, ?_, ?_⟩
  · intro hs
    have h := (Nat.modEq_iff_dvd' (show 1 ≤ m*k from Nat.mul_pos hm hkpos)).mp hyp.symm
    exact Nat.squarefree_iff_prime_squarefree.mp hs p hp (by simpa [sq] using h)
  · intro hs
    have he := hyq.add_right 1
    rw [Nat.sub_add_cancel hq2.le] at he
    have h := he.trans (dvd_refl (q^2)).modEq_zero_nat
    exact Nat.squarefree_iff_prime_squarefree.mp hs q hq (by simpa [sq] using Nat.modEq_zero_iff_dvd.mp h)

end SquarefreeNeighbors

theorem OMA.solution : type_of% @OMA.S_oeis_a357315.main := by
  apply (Set.finite_Iio ((64^4+1)^5 : ℕ)).subset
  intro m hmem
  obtain ⟨hm, hall⟩ := hmem
  change m < (64^4+1)^5
  by_contra! hbig
  obtain ⟨x, hlo, hhi⟩ := SquarefreeNeighbors.fifth_root_interval m
  have hx : 64^4 < x := by
    by_contra! hle
    have hpow : (x+1)^5 ≤ (64^4+1)^5 := Nat.pow_le_pow_left (Nat.succ_le_succ hle) 5
    exact (not_lt_of_ge hbig) (hhi.trans_le hpow)
  obtain ⟨p, q, hp, hq, hpq, hpm, hqm, hpc, hqc⟩ :=
    SquarefreeNeighbors.missing_primes hm (by omega) hhi
  have hsize : p^2*q^2 ≤ m := calc
    p^2*q^2 ≤ (64*x)^2 * (64*x)^2 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hpc _) (Nat.pow_le_pow_left hqc _)
    _ = (64^4) * x^4 := by ring
    _ ≤ x*x^4 := Nat.mul_le_mul_right _ hx.le
    _ = x^5 := by ring
    _ ≤ m := hlo
  obtain ⟨k, hk, hkm, hminus, hplus⟩ := SquarefreeNeighbors.witness hm hp hq hpq hpm hqm hsize
  exact (hall k hk hkm).elim hminus hplus
