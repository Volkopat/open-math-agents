import OMAReductions.R_OeisA219791_conjecture_2_R1

-- Credit: @gdyan2022
/-! The discriminant parameter gives an exact count on the half interval.
For even targets, odd splits never survive, leaving a polynomial of half the length. -/

namespace OMA.R_OeisA219791_conjecture_2_R1_H2_R1

open Finset
open scoped Classical
open OMA.R_OeisA219791_conjecture_2_R1 (split_product_strict paired_of_composite)

/-- Sieve comparison for the even targets, with both summands divided by two. -/
def H1 : Prop := ∀ k : ℕ, 0 < k → ∃ M : ℕ, ∀ m ≥ M,
  let f := fun j : ℕ => (4 * j * (m-j))^(2^k) + 1
  let s := Icc 1 (m/2)
  2 * (s.filter fun j => f j < (f j).minFac^3 ∧ ¬ (f j).Prime).card ≤
    (s.filter fun j => f j < (f j).minFac^4).card

/-- Sieve comparison for odd targets, with one representative of each split. -/
def H2 : Prop := ∀ k : ℕ, 0 < k → ∃ M : ℕ, ∀ m ≥ M,
  let f := fun j : ℕ => (j * (2*m+1-j))^(2^k) + 1
  let s := Icc 1 m
  2 * (s.filter fun j => f j < (f j).minFac^3 ∧ ¬ (f j).Prime).card ≤
    (s.filter fun j => f j < (f j).minFac^4).card

lemma split_of_disc {t u n : ℕ} (ht : 0 < t) (heq : 4*t+u^2=n^2) :
    ∃ x ∈ Icc 1 (n/2), x*(n-x)=t := by
  have hul : u < n := by nlinarith
  have hpar : n % 2 = u % 2 := by
    have hs (a : ℕ) : a^2 % 2 = a % 2 := by
      rw [Nat.pow_mod]
      rcases Nat.mod_two_eq_zero_or_one a with h | h <;> rw [h]
    have h4 : (4*t)%2=0 := by omega
    calc
      n % 2 = n^2 % 2 := (hs n).symm
      _ = (4*t+u^2)%2 := by rw [heq]
      _ = u % 2 := by rw [Nat.add_mod, h4, hs]; omega
  let x := (n-u)/2
  have hx : 2*x + u = n := by dsimp [x]; omega
  refine ⟨x, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  have hs : n-x = x+u := by omega
  rw [hs]
  nlinarith [show n^2 = (2*x+u)^2 by rw [hx]]

lemma least_of_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (p*q).minFac = p := by
  have hprime : (p*q).minFac.Prime := Nat.minFac_prime (by nlinarith [hp.two_le, hq.two_le])
  have hle := Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q)
  rcases hprime.dvd_mul.mp (Nat.minFac_dvd (p*q)) with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hprime hp).mp h
  · have := (Nat.prime_dvd_prime_iff_eq hprime hq).mp h
    omega

lemma count_paired (n k : ℕ) (hn : 8 ≤ n) (hk : 0 < k) :
    let f := fun x : ℕ => (x*(n-x))^(2^k)+1
    let paired := (Icc 1 (n^2/4)).filter fun t =>
      (∃ u : ℕ, 4*t+u^2=n^2) ∧ ∃ p q : ℕ,
        p.Prime ∧ q.Prime ∧ p<q ∧ q<p^2 ∧ 2^(k+1) ∣ p-1 ∧
        2^(k+1) ∣ q-1 ∧ p*q=t^(2^k)+1
    ((Icc 1 (n/2)).filter fun x => f x < (f x).minFac^3 ∧ ¬ (f x).Prime).card =
      paired.card := by
  classical
  dsimp only
  apply card_bij (fun x _ => x*(n-x))
  · intro x hx
    obtain ⟨hmem, hrough, hcomp⟩ := mem_filter.mp hx
    exact mem_filter.mpr (paired_of_composite hk hn hmem hrough hcomp)
  · intro x hx y hy hxy
    have xx := (mem_Icc.mp (mem_filter.mp hx).1).2
    have yy := (mem_Icc.mp (mem_filter.mp hy).1).2
    rcases lt_trichotomy x y with h | h | h
    · exact ((split_product_strict h yy).ne hxy).elim
    · exact h
    · exact ((split_product_strict h xx).ne hxy.symm).elim
  · intro t ht
    obtain ⟨hi, ⟨u, hu⟩, p, q, hp, hq, hlt, hsmall, _, _, hprod⟩ := mem_filter.mp ht
    obtain ⟨x, hx, hbase⟩ := split_of_disc (mem_Icc.mp hi).1 hu
    refine ⟨x, mem_filter.mpr ⟨hx, ?_⟩, hbase⟩
    rw [hbase, ← hprod, least_of_pair hp hq hlt]
    exact ⟨by simpa [pow_succ, Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left hsmall hp.pos,
      Nat.not_prime_mul hp.ne_one hq.ne_one⟩

lemma even_base (m j : ℕ) :
    2*j*(2*m-2*j)=4*j*(m-j) := by
  rw [← Nat.mul_sub_left_distrib]
  ring

lemma even_split (m k x : ℕ) (hm : 16 ≤ m) (hx : x ∈ Icc 1 m)
    (hrough : (x*(2*m-x))^(2^k)+1 < ((x*(2*m-x))^(2^k)+1).minFac^4) :
    2 ∣ x := by
  by_contra hd
  obtain ⟨xl, xu⟩ := mem_Icc.mp hx
  have hodd : Odd x := by rw [Nat.odd_iff]; omega
  have hy : Odd (2*m-x) := by rw [Nat.odd_iff]; omega
  have hpar : Even ((x*(2*m-x))^(2^k)+1) := (hodd.mul hy).pow.add_odd odd_one
  have hmin := Nat.minFac_le_of_dvd (by decide : 2 ≤ 2) (even_iff_two_dvd.mp hpar)
  have hpow := Nat.pow_le_pow_left hmin 4
  have hlarge : 16 ≤ x*(2*m-x) := by
    have hz : m ≤ 2*m-x := by omega
    nlinarith [Nat.mul_le_mul xl hz]
  have hmono := Nat.le_self_pow (show 2^k ≠ 0 by positivity) (x*(2*m-x))
  omega

lemma double_count (m : ℕ) (p : ℕ → Prop) [DecidablePred p]
    (heven : ∀ x ∈ Icc 1 m, p x → 2 ∣ x) :
    ((Icc 1 (m/2)).filter fun j => p (2*j)).card = ((Icc 1 m).filter p).card := by
  apply card_bij (fun j _ => 2*j)
  · intro j hj
    obtain ⟨hl, hu⟩ := mem_Icc.mp (mem_filter.mp hj).1
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, (mem_filter.mp hj).2⟩
  · intro i hi j hj e
    omega
  · intro x hx
    obtain ⟨hb, hp⟩ := mem_filter.mp hx
    obtain ⟨j, rfl⟩ := heven x hb hp
    obtain ⟨hl, hu⟩ := mem_Icc.mp hb
    exact ⟨j, mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩, hp⟩, rfl⟩

theorem main : H1 → H2 → OMA.R_OeisA219791_conjecture_2_R1.H2 := by
  classical
  intro he ho k hk
  obtain ⟨Me, he⟩ := he k hk
  obtain ⟨Mo, ho⟩ := ho k hk
  refine ⟨2*max Me Mo+32, ?_⟩
  intro n hn
  dsimp only
  rw [← count_paired n k (by omega) hk]
  obtain ⟨m,rfl|rfl⟩ : ∃ m, n = 2*m ∨ n = 2*m+1 := ⟨n/2, by omega⟩
  · simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    let f := fun x : ℕ => (x*(2*m-x))^(2^k)+1
    let bad := fun x => f x < (f x).minFac^3 ∧ ¬ (f x).Prime
    let rough := fun x => f x < (f x).minFac^4
    change 2*((Icc 1 m).filter bad).card ≤ ((Icc 1 m).filter rough).card
    have hb := double_count m bad (fun x hx h => even_split m k x (by omega) hx
      (h.1.trans_le (Nat.pow_le_pow_right (by have := Nat.minFac_pos (f x); omega) (by decide : 3 ≤ 4))))
    have hr := double_count m rough (fun x hx h => even_split m k x (by omega) hx h)
    rw [← hb, ← hr]
    have h := he m (by omega)
    simp only [bad, rough, f, even_base]
    exact h
  · simpa [show (2*m+1)/2=m by omega] using ho m (by omega)

end OMA.R_OeisA219791_conjecture_2_R1_H2_R1
