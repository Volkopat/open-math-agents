import FormalConjectures.ErdosProblems.«148»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
Konyagin's Egyptian-fraction lower bound (Mathematical Notes 95, 2014,
DOI 10.1134/S0001434614010295). The telescoping sum uses the corrected
final identity recorded at https://erdosproblemaday.com/report/148.

Distinctness of the prefix follows from its powers of two and odd factors.
For the prime count, use a squarefree exponent built from primes above a
square-root cutoff. Each divisor used in the count contains three reserved
primes. This forces a prime divisor of its cyclotomic value to be primitive.
-/

open Filter Finset
open scoped BigOperators Topology

namespace OMA148

def ex (j : ℕ) : ℕ := 3 ^ j

def base (j : ℕ) : ℕ := 2 ^ ex j

def ord (j : ℕ) (t : Fin 3) : ℕ :=
  if t = 0 then ex j * 3 else if t = 1 then ex j else ex j - 1

def part (j : ℕ) (t : Fin 3) : ℕ :=
  if t = 0 then 1 else if t = 1 then base j ^ 4 - base j ^ 2 + 1
  else (base j ^ 2 - 1) * (base j ^ 8 + base j ^ 4 + 1)

def den (i : ℕ × Fin 3) : ℕ := 2 ^ ord i.1 i.2 * part i.1 i.2

def recp (d : ℕ) : ℚ := 1 / d

lemma ex_pos (j : ℕ) : 0 < ex j := by unfold ex; positivity

lemma ex_odd (j : ℕ) : Odd (ex j) := by
  unfold ex
  exact (by decide : Odd (3 : ℕ)).pow

lemma ex_mono : StrictMono ex := by
  intro i j hij
  exact Nat.pow_lt_pow_right (by decide) hij

lemma base_ge (j : ℕ) : 2 ≤ base j := by
  unfold base
  exact Nat.succ_le_of_lt (Nat.one_lt_two_pow (ex_pos j).ne')

lemma base_even (j : ℕ) : Even (base j) := by
  exact even_iff_two_dvd.mpr (dvd_pow_self 2 (ex_pos j).ne')

lemma base_succ (j : ℕ) : base (j + 1) = base j ^ 3 := by
  unfold base ex
  rw [pow_succ, pow_mul]

lemma part_odd (j : ℕ) (t : Fin 3) : Odd (part j t) := by
  have hb := base_ge j
  have he := base_even j
  have h2 : Even (base j ^ 2) := he.pow_of_ne_zero (by decide)
  have h4 : Even (base j ^ 4) := he.pow_of_ne_zero (by decide)
  have h8 : Even (base j ^ 8) := he.pow_of_ne_zero (by decide)
  have hs : base j ^ 2 ≤ base j ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hs' : 1 ≤ base j ^ 2 := Nat.pow_pos (by omega)
  have hodd : Odd (base j ^ 2 - 1) := by
    rw [Nat.odd_iff]
    rw [Nat.even_iff] at h2
    omega
  fin_cases t
  · simp [part]
  · change Odd (part j 1)
    change Odd (base j ^ 4 - base j ^ 2 + 1)
    rw [Nat.odd_iff]
    rw [Nat.even_iff] at h2 h4
    omega
  · change Odd (part j 2)
    have hr : Odd (base j ^ 8 + base j ^ 4 + 1) := (h8.add h4).add_odd (by decide)
    simpa [part] using hodd.mul hr

lemma part_large (j : ℕ) (t : Fin 3) (ht : t ≠ 0) : 1 < part j t := by
  have hx := base_ge j
  have h1 : base j ^ 2 < base j ^ 4 := Nat.pow_lt_pow_right (by omega) (by decide)
  have h2 : 1 < base j ^ 2 - 1 := by
    have : 2^2 ≤ base j ^ 2 := Nat.pow_le_pow_left hx 2
    omega
  fin_cases t
  · exact (ht rfl).elim
  · change 1 < part j 1
    simp [part]; omega
  · change 1 < part j 2
    simp only [part, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, if_false]
    exact h2.trans_le (Nat.le_mul_of_pos_right _ (by positivity))

lemma den_pos (i : ℕ × Fin 3) : 0 < den i := by
  unfold den
  exact Nat.mul_pos (by positivity) (part_odd i.1 i.2).pos

lemma den_val (j : ℕ) (t : Fin 3) : padicValNat 2 (den (j,t)) = ord j t := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := part_odd j t
  have hnd : ¬ 2 ∣ part j t := by
    rw [← even_iff_two_dvd, Nat.even_iff, Nat.odd_iff.mp hp]
    decide
  unfold den
  rw [padicValNat.mul (by positivity) hp.pos.ne', padicValNat.pow,
    padicValNat.self (by decide), padicValNat.eq_zero_of_not_dvd hnd]
  simp

lemma ord_odd (j : ℕ) (t : Fin 3) (ht : t ≠ 2) : Odd (ord j t) := by
  fin_cases t
  · simpa [ord] using (ex_odd j).mul (by decide : Odd (3 : ℕ))
  · simpa [ord] using ex_odd j
  · exact (ht rfl).elim

lemma ord_two_even (j : ℕ) : Even (ord j 2) := by
  have he := Nat.odd_iff.mp (ex_odd j)
  have hp := ex_pos j
  simp [ord, Nat.even_iff]
  omega

lemma ord_inj (t : Fin 3) : Function.Injective (fun j ↦ ord j t) := by
  intro i j h
  apply ex_mono.injective
  have hi := ex_pos i
  have hj := ex_pos j
  fin_cases t <;> simp [ord] at h <;> omega

lemma den_injective : Function.Injective den := by
  rintro ⟨i,t⟩ ⟨j,u⟩ h
  have hv := congrArg (padicValNat 2) h
  rw [den_val, den_val] at hv
  have hp : part i t = part j u := by
    change 2 ^ ord i t * part i t = 2 ^ ord j u * part j u at h
    rw [hv] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have ht : t = u := by
    by_cases tz : t = 0
    · subst t
      by_contra hu
      have := part_large j u (Ne.symm hu)
      change 1 = part j u at hp
      omega
    by_cases uz : u = 0
    · subst u
      have := part_large i t tz
      change part i t = 1 at hp
      omega
    by_cases te : t = 2
    · subst t
      by_contra hu
      have hodd := ord_odd j u (Ne.symm hu)
      have heven := ord_two_even i
      rw [hv] at heven
      exact (Nat.not_even_iff_odd.mpr hodd) heven
    by_cases ue : u = 2
    · subst u
      have hodd := ord_odd i t te
      have heven := ord_two_even j
      rw [hv] at hodd
      exact ((Nat.not_even_iff_odd.mpr hodd) heven).elim
    fin_cases t <;> fin_cases u <;> simp_all
  subst u
  exact Prod.ext (ord_inj t hv) rfl

lemma den_form_zero (j : ℕ) : den (j,0) = base j ^ 3 := by
  simp [den, ord, part, base, ← pow_mul]

lemma den_form_one (j : ℕ) : den (j,1) = base j * (base j ^ 4 - base j ^ 2 + 1) := by
  simp [den, ord, part, base]

lemma den_form_two (j : ℕ) :
    den (j,2) = 2 ^ (ex j - 1) * (base j ^ 2 - 1) * (base j ^ 8 + base j ^ 4 + 1) := by
  simp [den, ord, part, mul_assoc]

lemma double_half (j : ℕ) : 2 * 2 ^ (ex j - 1) = base j := by
  unfold base
  rw [← pow_succ', Nat.sub_add_cancel (ex_pos j)]

lemma den_ge (i : ℕ × Fin 3) : 3 < den i := by
  obtain ⟨j,t⟩ := i
  have h := base_ge j
  have h24 : base j ^ 2 ≤ base j ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h' : 2 ≤ base j ^ 4 - base j ^ 2 + 1 := by
    have := Nat.pow_lt_pow_right (a := base j) (by omega) (show 2 < 4 by decide)
    omega
  have h2 : 3 ≤ base j ^ 2 - 1 := by
    have : 2^2 ≤ base j ^ 2 := Nat.pow_le_pow_left h 2
    omega
  have h4 : 2 ≤ base j ^ 8 + base j ^ 4 + 1 := by
    have : 0 < base j ^ 4 := by positivity
    omega
  fin_cases t
  · change 3 < den (j,0)
    rw [den_form_zero]
    exact (show 3 < 2^3 by decide).trans_le (Nat.pow_le_pow_left h 3)
  · change 3 < den (j,1)
    rw [den_form_one]
    exact (show 3 < 2 * 2 by decide).trans_le (Nat.mul_le_mul h h')
  · change 3 < den (j,2)
    rw [den_form_two]
    have hp : 1 ≤ (2 : ℕ) ^ (ex j - 1) := Nat.one_le_two_pow
    exact (show 3 < 1 * 3 * 2 by decide).trans_le (Nat.mul_le_mul (Nat.mul_le_mul hp h2) h4)

lemma den_bound (j : ℕ) (t : Fin 3) : den (j,t) < base j ^ 12 := by
  have hb := base_ge j
  have h24 : base j ^ 2 ≤ base j ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h48 : base j ^ 4 < base j ^ 8 := Nat.pow_lt_pow_right (by omega) (by decide)
  have h2 : 1 ≤ base j ^ 2 := Nat.pow_pos (by omega)
  have h5 : base j ^ 5 < base j ^ 12 := Nat.pow_lt_pow_right (by omega) (by decide)
  fin_cases t
  · change den (j,0) < base j ^ 12
    rw [den_form_zero]
    exact Nat.pow_lt_pow_right (by omega) (by decide)
  · change den (j,1) < base j ^ 12
    rw [den_form_one]
    have hh : base j ^ 4 - base j ^ 2 + 1 ≤ base j ^ 4 := by omega
    exact (Nat.mul_le_mul_left _ hh).trans_lt (by simpa [pow_succ'] using h5)
  · change den (j,2) < base j ^ 12
    rw [den_form_two]
    have hh : base j ^ 8 + base j ^ 4 + 1 ≤ 2 * base j ^ 8 := by omega
    have hl : base j ^ 2 - 1 ≤ base j ^ 2 := Nat.sub_le ..
    have hhh := Nat.mul_le_mul (Nat.mul_le_mul_left (2 ^ (ex j-1)) hl) hh
    apply hhh.trans_lt
    calc
      _ = (2 * 2 ^ (ex j - 1)) * (base j ^ 2 * base j ^ 8) := by ring
      _ = base j ^ 11 := by rw [double_half]; ring
      _ < base j ^ 12 := Nat.pow_lt_pow_right (by omega) (by decide)

lemma step_identity (j : ℕ) :
    recp (base j ^ 3 - base j) - recp (base (j+1) ^ 3 - base (j+1)) =
      recp (den (j,0)) + recp (den (j,1)) + recp (den (j,2)) := by
  rw [base_succ, den_form_zero, den_form_one, den_form_two]
  have h := base_ge j
  have h9 : base j ^ 3 ≤ (base j ^ 3) ^ 3 := by
    nth_rw 1 [← pow_one (base j ^ 3)]
    exact Nat.pow_le_pow_right (by positivity) (by decide)
  have h31 : base j ≤ base j ^ 3 := by
    nth_rw 1 [← pow_one (base j)]
    exact Nat.pow_le_pow_right (by omega) (by decide)
  have h24 : base j ^ 2 ≤ base j ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h2 : 1 ≤ base j ^ 2 := Nat.pow_pos (by omega)
  have hq : (2 : ℚ) * (2 ^ (ex j - 1) : ℕ) = base j := by exact_mod_cast double_half j
  have hb : 2 ≤ (base j : ℚ) := by exact_mod_cast h
  have g {x : ℚ} (hx : 1 < x) : x^3 - x ≠ 0 := by
    have h := pow_lt_pow_right₀ hx (show 1 < (3:ℕ) by decide)
    simpa using (sub_ne_zero.mpr (show x^3 ≠ x by simpa using h.ne'))
  have b1 : (base j : ℚ) ^ 3 - base j ≠ 0 := g (by linarith)
  have b2 : ((base j : ℚ) ^ 3) ^ 3 - (base j : ℚ) ^ 3 ≠ 0 :=
    g (one_lt_pow₀ (by linarith) (by decide))
  have b3 : (base j : ℚ) ^ 4 - (base j : ℚ) ^ 2 + 1 ≠ 0 := by
    have hh : (base j : ℚ)^2 ≤ (base j : ℚ)^4 := by exact_mod_cast h24
    linarith
  have b4 : (base j : ℚ)^2 - 1 ≠ 0 := by nlinarith
  have b5 : (base j : ℚ)^8 + (base j : ℚ)^4 + 1 ≠ 0 := by positivity
  have b6 : (base j : ℚ) ≠ 0 := by positivity
  have b7 : (2 ^ (ex j - 1) : ℕ) ≠ 0 := by positivity
  unfold recp
  push_cast [Nat.cast_sub h9, Nat.cast_sub h31, Nat.cast_sub h24, Nat.cast_sub h2]
  have hhalf : (2 : ℚ) ^ (ex j - 1) = (base j : ℚ) / 2 := by
    apply (eq_div_iff (by norm_num)).2
    push_cast at hq
    simpa [mul_comm] using hq
  rw [hhalf]
  have b8 : -1 + (base j : ℚ)^6 ≠ 0 := by
    have hr : 1 < (base j : ℚ)^6 := one_lt_pow₀ (by linarith) (by decide)
    exact ne_of_gt (by linarith)
  have b9 : 1 - (base j : ℚ)^2 + (base j : ℚ)^4 ≠ 0 := by
    convert b3 using 1 <;> ring
  have hfirst : (base j : ℚ)^3 - base j = (base j : ℚ) * ((base j : ℚ)^2-1) := by ring
  have hsecond : ((base j : ℚ)^3)^3 - (base j : ℚ)^3 =
      (base j : ℚ)^3 * ((base j : ℚ)^2-1) * ((base j : ℚ)^4 + (base j : ℚ)^2 + 1) := by ring
  have hlast : (base j : ℚ)^8 + (base j : ℚ)^4 + 1 =
      ((base j : ℚ)^4 + (base j : ℚ)^2 + 1) * ((base j : ℚ)^4 - (base j : ℚ)^2 + 1) := by ring
  rw [hfirst, hsecond, hlast]
  field_simp [b3,b4,b6]
  <;> ring_nf
  <;> field_simp [b3,b4,b6,b8,b9]
  <;> ring

end OMA148

namespace OMA148

def solutions (k : ℕ) (r : ℚ) : Set (Finset ℕ) :=
  {s | s.card = k ∧ 0 ∉ s ∧ ∑ d ∈ s, recp d = r}

lemma recp_pos {d : ℕ} (h : 0 < d) : 0 < recp d := by
  unfold recp
  positivity

lemma solutions_finite (k : ℕ) (r : ℚ) : (solutions k r).Finite := by
  induction k generalizing r with
  | zero =>
    apply (Set.finite_singleton (∅ : Finset ℕ)).subset
    intro s hs
    exact Finset.card_eq_zero.mp hs.1
  | succ k ih =>
    let N : ℕ := ⌊((k + 1 : ℕ) : ℚ) / r⌋₊
    let T : ℕ → Set (Finset ℕ) := fun d ↦ insert d '' solutions k (r - recp d)
    have hT : (⋃ d ∈ Set.Iic N, T d).Finite :=
      (Set.finite_Iic N).biUnion (fun d _ ↦ (ih (r - recp d)).image (insert d))
    apply hT.subset
    intro s hs
    change s.card = k+1 ∧ 0 ∉ s ∧ _ at hs
    obtain ⟨hc, h0, hr⟩ := hs
    have hn : s.Nonempty := Finset.card_pos.mp (by omega)
    let d := s.min' hn
    have hd : d ∈ s := s.min'_mem hn
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by intro he; exact h0 (he ▸ hd))
    have hr0 : 0 < r := by
      rw [← hr]
      exact Finset.sum_pos (fun x hx ↦ recp_pos (by
        exact Nat.pos_of_ne_zero (by rintro rfl; exact h0 hx))) hn
    have hrd : r ≤ ((k + 1 : ℕ) : ℚ) * recp d := by
      rw [← hr, ← hc]
      calc
        _ ≤ ∑ _x ∈ s, recp d := by
          apply Finset.sum_le_sum
          intro x hx
          have hdx : d ≤ x := s.min'_le x hx
          have hdq : (0 : ℚ) < d := by exact_mod_cast hd0
          have hxq : (d : ℚ) ≤ x := by exact_mod_cast hdx
          exact one_div_le_one_div_of_le hdq hxq
        _ = _ := by simp
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd0
    have hdN : d ≤ N := by
      apply Nat.le_floor
      apply (le_div_iff₀ hr0).2
      unfold recp at hrd
      have hb := (le_div_iff₀ hdq).1 (by simpa [div_eq_mul_inv] using hrd :
        r ≤ ((k + 1 : ℕ) : ℚ) / d)
      simpa [mul_comm] using hb
    have hrs := Finset.sum_erase_add s recp hd
    exact Set.mem_iUnion.2 ⟨d, Set.mem_iUnion.2 ⟨hdN, s.erase d,
      ⟨by rw [Finset.card_erase_of_mem hd, hc]; omega,
       fun h ↦ h0 (Finset.mem_of_mem_erase h), by linarith⟩,
      Finset.insert_erase hd⟩⟩

lemma F_def (k : ℕ) : Erdos148.F k = (solutions k 1).ncard := rfl

lemma no_one {k : ℕ} (hk : 2 ≤ k) {s : Finset ℕ} (hs : s ∈ solutions k 1) : 1 ∉ s := by
  intro ho
  obtain ⟨hc, h0, hr⟩ := hs
  have hre := Finset.sum_erase_add s recp ho
  have hc' := Finset.card_erase_of_mem ho
  have hp : (s.erase 1).Nonempty := Finset.card_pos.mp (by omega)
  have hps := Finset.sum_pos (f := recp) (fun x hx ↦ recp_pos
    (Nat.pos_of_ne_zero (by rintro rfl; exact h0 (Finset.mem_of_mem_erase hx)))) hp
  have hone : recp 1 = 1 := by norm_num [recp]
  rw [hone, hr] at hre
  linarith

def pad (s : Finset ℕ) : Finset ℕ := insert 2 (s.image (fun d ↦ 2*d))

lemma double_inj : Function.Injective (fun d : ℕ ↦ 2*d) := by
  intro a b h
  change 2*a = 2*b at h
  omega

lemma pad_excluded {k : ℕ} (hk : 2 ≤ k) {s : Finset ℕ} (hs : s ∈ solutions k 1) :
    2 ∉ s.image (fun d ↦ 2*d) := by
  rintro h
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp h
  have h : x = 1 := by omega
  exact no_one hk hs (h ▸ hx)

lemma pad_valid {k : ℕ} (hk : 2 ≤ k) {s : Finset ℕ} (hs : s ∈ solutions k 1) :
    pad s ∈ solutions (k+1) 1 := by
  have h2 := pad_excluded hk hs
  obtain ⟨hc,h0,hr⟩ := hs
  change (pad s).card = k+1 ∧ 0 ∉ pad s ∧ ∑ d ∈ pad s, recp d = 1
  refine ⟨by simp [pad, h2, Finset.card_image_of_injective _ double_inj, hc], ?_, ?_⟩
  · simp only [pad, Finset.mem_insert, Finset.mem_image, show (0:ℕ) ≠ 2 by decide, false_or]
    rintro ⟨x,hx,he⟩
    have h : x = 0 := by omega
    exact h0 (h ▸ hx)
  · rw [pad, Finset.sum_insert h2, Finset.sum_image double_inj.injOn]
    have ht (d : ℕ) : recp (2*d) = (1/2 : ℚ) * recp d := by
      simp [recp, Nat.cast_mul, div_mul_eq_div_div, div_eq_mul_inv, mul_comm, mul_assoc]
    simp_rw [ht, ← Finset.mul_sum, hr, recp]
    norm_num

lemma F_succ {k : ℕ} (hk : 2 ≤ k) : Erdos148.F k ≤ Erdos148.F (k+1) := by
  rw [F_def, F_def]
  apply Set.ncard_le_ncard_of_injOn pad (fun _ hs ↦ pad_valid hk hs) _
    (solutions_finite _ _)
  intro s hs t ht h
  apply Finset.image_injective double_inj
  have h' := congrArg (fun s : Finset ℕ ↦ s.erase 2) h
  simpa [pad, pad_excluded hk hs, pad_excluded hk ht] using h'

lemma F_mono {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) : Erdos148.F a ≤ Erdos148.F b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact ih.trans (F_succ (ha.trans hk))

end OMA148

namespace OMA148

def indices (k : ℕ) : Finset (ℕ × Fin 3) := (Finset.range k) ×ˢ Finset.univ

def core (k : ℕ) : Finset ℕ := (indices k).image den

def stem (k : ℕ) : Finset ℕ := insert (den (k,0)) (insert 2 (insert 3 (core k)))

lemma stem_card (k : ℕ) : (stem k).card = 3*k+3 := by
  have h2 (x : ℕ) (hx : x ∈ core k) : 3 < x := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact den_ge i
  have h3 : 3 ∉ core k := fun hh ↦ (lt_irrefl 3) (h2 3 hh)
  have h22 : 2 ∉ insert 3 (core k) := by
    simp only [Finset.mem_insert, show (2 : ℕ) ≠ 3 by decide, false_or]
    intro hh
    have := h2 2 hh
    omega
  have hd : den (k,0) ∉ insert 2 (insert 3 (core k)) := by
    have hg := den_ge (k,0)
    simp only [Finset.mem_insert, not_or]
    refine ⟨by omega, by omega, ?_⟩
    intro hh
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hh
    have hh := den_injective he
    subst i
    simpa [indices] using hi
  rw [stem, Finset.card_insert_of_notMem hd, Finset.card_insert_of_notMem h22,
    Finset.card_insert_of_notMem h3, core, Finset.card_image_of_injective _ den_injective,
    indices, Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin]
  omega

lemma stem_pos (k d : ℕ) (hd : d ∈ stem k) : 0 < d := by
  simp only [stem, Finset.mem_insert] at hd
  rcases hd with rfl | rfl | rfl | hd
  · exact den_pos _
  · decide
  · decide
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
    exact den_pos _

lemma base_mono : Monotone base := by
  intro i j h
  unfold base
  exact Nat.pow_le_pow_right (by decide) (ex_mono.monotone h)

lemma stem_bound (k d : ℕ) (hd : d ∈ stem k) : d < base k ^ 4 := by
  have hb := base_ge k
  simp only [stem, Finset.mem_insert] at hd
  rcases hd with rfl | rfl | rfl | hd
  · rw [den_form_zero]
    exact Nat.pow_lt_pow_right (by omega) (by decide)
  · exact (show 2 < 2^4 by decide).trans_le (Nat.pow_le_pow_left hb 4)
  · exact (show 3 < 2^4 by decide).trans_le (Nat.pow_le_pow_left hb 4)
  · obtain ⟨⟨j,t⟩,hj,rfl⟩ := Finset.mem_image.mp hd
    have hj' : j < k := by simpa [indices] using hj
    have hle : base (j+1) ≤ base k := base_mono (by omega)
    have hpow : base j ^ 12 = base (j+1) ^ 4 := by
      rw [base_succ, ← pow_mul]
    exact (den_bound j t).trans_le (hpow.le.trans (Nat.pow_le_pow_left hle _))

lemma one_sub_sum_stem (k : ℕ) :
    (∑ d ∈ stem k, recp d) =
      1 - recp (base k ^ 3 - base k) + recp (base k ^ 3) := by
  have hnot (x : ℕ) (hx : x ≤ 3) : x ∉ core k := by
    intro hh
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hh
    have := den_ge i
    omega
  have h2 : 2 ∉ insert 3 (core k) := by
    simp [hnot 2 (by decide)]
  have h3 : 3 ∉ core k := hnot 3 le_rfl
  have hd : den (k,0) ∉ insert 2 (insert 3 (core k)) := by
    have hg := den_ge (k,0)
    simp only [Finset.mem_insert, not_or]
    refine ⟨by omega, by omega, ?_⟩
    intro hh
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hh
    have hh := den_injective he
    subst i
    simpa [indices] using hi
  have ht :
      (∑ i ∈ Finset.range k, (recp (den (i,0)) + recp (den (i,1)) +
        recp (den (i,2)))) =
      recp (base 0 ^ 3 - base 0) - recp (base k ^ 3 - base k) := by
    clear hnot h2 h3 hd
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, ← step_identity]
      ring
  rw [stem, Finset.sum_insert hd, Finset.sum_insert h2, Finset.sum_insert h3,
    core, Finset.sum_image den_injective.injOn, indices, Finset.sum_product]
  simp_rw [Fin.sum_univ_three, ht, den_form_zero]
  norm_num [recp, base, ex]
  ring

def qfac (k : ℕ) : ℕ := base k ^ 2 - 1

def topsmall (k m : ℕ) : ℕ := qfac k * (base k ^ 3 + 2 ^ (ex k * 3 - m))

def topbig (k m : ℕ) : ℕ := qfac k * base k ^ 3 * (2 ^ m + 1)

lemma qfac_gt_base (k : ℕ) : base k < qfac k := by
  have hb := base_ge k
  unfold qfac
  have hx : base k * 2 ≤ base k * base k := Nat.mul_le_mul_left _ hb
  rw [pow_two]
  omega

lemma top_big_bound (k m : ℕ) : base k ^ 4 < topbig k m := by
  have hq := qfac_gt_base k
  have hp : 0 < base k ^ 3 := Nat.pow_pos (by have := base_ge k; omega)
  apply lt_of_lt_of_le _ (Nat.le_mul_of_pos_right _ (by positivity))
  rw [pow_succ']
  exact Nat.mul_lt_mul_of_pos_right hq hp

lemma top_small_bound (k m : ℕ) : base k ^ 4 < topsmall k m := by
  have hq := qfac_gt_base k
  have hp : 0 < base k ^ 3 := Nat.pow_pos (by have := base_ge k; omega)
  apply lt_of_lt_of_le _ (Nat.mul_le_mul_left (qfac k) (Nat.le_add_right _ _))
  rw [pow_succ']
  exact Nat.mul_lt_mul_of_pos_right hq hp

lemma top_order {k m : ℕ} (hm : 0 < m) (hm' : m ≤ ex k * 3) :
    topsmall k m < topbig k m := by
  have hq : 0 < qfac k := (Nat.zero_le _).trans_lt (qfac_gt_base k)
  have hx : 0 < base k ^ 3 := Nat.pow_pos (by have := base_ge k; omega)
  have hm2 : 1 < (2:ℕ)^m := Nat.one_lt_two_pow hm.ne'
  have hc : (2:ℕ)^(ex k * 3 - m) ≤ base k ^ 3 := by
    unfold base
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  unfold topsmall topbig
  rw [mul_assoc]
  apply Nat.mul_lt_mul_of_pos_left _ hq
  have h' : base k ^ 3 * 2 ≤ base k ^ 3 * 2^m :=
    Nat.mul_le_mul_left _ hm2
  rw [Nat.mul_add, Nat.mul_one]
  omega

lemma top_identity {k m : ℕ} (hm : m ≤ ex k * 3) :
    recp (base k ^ 3 - base k) =
      recp (base k ^ 3) + recp (topsmall k m) + recp (topbig k m) := by
  have hb := base_ge k
  have hq := qfac_gt_base k
  have h3 : base k ≤ base k ^ 3 := by
    nth_rw 1 [← pow_one (base k)]
    exact Nat.pow_le_pow_right (by omega) (by decide)
  have h2 : 1 ≤ base k ^ 2 := Nat.pow_pos (by omega)
  have hr : (2 : ℕ) ^ (ex k * 3 - m) * 2 ^ m = base k ^ 3 := by
    rw [← pow_add, Nat.sub_add_cancel hm, base, pow_mul]
  have hr' : (2 : ℚ) ^ (ex k * 3 - m) * 2 ^ m = (base k : ℚ)^3 := by exact_mod_cast hr
  have hx : (base k : ℚ) ≠ 0 := by positivity
  have hA : (base k : ℚ) ^ 3 - base k ≠ 0 := by
    have h := pow_lt_pow_right₀ (a := (base k : ℚ)) (by exact_mod_cast (show 1 < base k by omega)) (show 1 < (3:ℕ) by decide)
    exact sub_ne_zero.mpr (by simpa using h.ne')
  have hQ : (base k : ℚ) ^ 2 - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ base k := by exact_mod_cast hb
    nlinarith
  have hp : (2 : ℚ)^m ≠ 0 := by positivity
  have hP : (2 : ℚ)^m + 1 ≠ 0 := by positivity
  have hC : (2 : ℚ)^(ex k * 3 - m) = (base k : ℚ)^3 / 2^m :=
    (eq_div_iff hp).2 hr'
  unfold recp topsmall topbig qfac
  push_cast [Nat.cast_sub h3, Nat.cast_sub h2]
  rw [hC]
  have hW : (base k : ℚ)^3 + (base k : ℚ)^3 / 2^m ≠ 0 := by positivity
  field_simp
  <;> ring

lemma unit_split {A d D : ℕ} (hA : 0 < A) (hd : 0 < d) (hD : 0 < D)
    (h : d*D = A^2) : recp (A+d) + recp (A+D) = recp A := by
  have hq : (d : ℚ) * D = (A : ℚ)^2 := by exact_mod_cast h
  have ha : (A : ℚ) ≠ 0 := by exact_mod_cast hA.ne'
  have hab : (A : ℚ) + d ≠ 0 := by positivity
  have had : (A : ℚ) + D ≠ 0 := by positivity
  simp only [recp, Nat.cast_add]
  field_simp
  linear_combination -hq

def tail (k m : ℕ) : Finset ℕ := insert (topsmall k m) (stem k)

def split (k m d : ℕ) : Finset ℕ :=
  insert (topbig k m + d) (insert (topbig k m + topbig k m ^ 2 / d) (tail k m))

lemma tail_lt {k m : ℕ} (hm : 0 < m) (hm' : m ≤ ex k * 3)
    {x : ℕ} (hx : x ∈ tail k m) : x < topbig k m := by
  simp only [tail, Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact top_order hm hm'
  · exact (stem_bound k x hx).trans (top_big_bound k m)

lemma split_valid {k m d : ℕ} (hm : 0 < m) (hm' : m ≤ ex k * 3)
    (hd : d ∣ 2^m+1) : split k m d ∈ solutions (3*k+6) 1 := by
  let A := topbig k m
  let D := A^2 / d
  have hA : 0 < A := (Nat.zero_le _).trans_lt (top_big_bound k m)
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by positivity)
  have hdA : d ∣ A := hd.trans (dvd_mul_left _ _)
  have hD : d * D = A^2 := Nat.mul_div_cancel' (hdA.trans (dvd_pow_self _ (by decide)))
  have hq : 1 < qfac k * base k ^ 3 := by
    have hq' := qfac_gt_base k
    have hb := base_ge k
    have hx : 0 < base k ^ 3 := Nat.pow_pos (by have := base_ge k; omega)
    exact (show 1 < qfac k by omega).trans_le (Nat.le_mul_of_pos_right _ hx)
  have hP : 0 < (2:ℕ)^m+1 := by positivity
  have hda : d < A :=
    (Nat.le_of_dvd hP hd).trans_lt (by
      change 2^m+1 < qfac k * base k ^ 3 * (2^m+1)
      simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hq hP)
  have hAD : A < D := by
    apply Nat.lt_of_mul_lt_mul_left (a := d)
    rw [hD, pow_two]
    exact Nat.mul_lt_mul_of_pos_right hda hA
  have hs : topsmall k m ∉ stem k := by
    intro hx
    exact (not_lt_of_ge (top_small_bound k m).le) (stem_bound k _ hx)
  have hf : A+D ∉ tail k m := by
    intro hx
    exact (not_lt_of_ge (Nat.le_add_right _ _)) (tail_lt hm hm' hx)
  have he : A+d ∉ insert (A+D) (tail k m) := by
    simp only [Finset.mem_insert, not_or]
    refine ⟨by omega, fun hx ↦ ?_⟩
    have hg := tail_lt hm hm' hx
    omega
  change (insert (A+d) (insert (A+D) (tail k m))).card = 3*k+6 ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem he, Finset.card_insert_of_notMem hf, tail,
      Finset.card_insert_of_notMem hs, stem_card]
  · intro hz
    change 0 ∈ insert (A+d) (insert (A+D) (tail k m)) at hz
    simp only [tail, Finset.mem_insert] at hz
    rcases hz with h | h | h | h
    · omega
    · omega
    · have := top_small_bound k m
      omega
    · exact (Nat.lt_irrefl 0) (stem_pos k 0 h)
  · change ∑ x ∈ insert (A+d) (insert (A+D) (tail k m)), recp x = 1
    rw [Finset.sum_insert he, Finset.sum_insert hf, tail, Finset.sum_insert hs,
      one_sub_sum_stem]
    have h := unit_split hA hdpos (by omega : 0 < D) hD
    have ht := top_identity (k := k) hm'
    change recp (base k ^ 3 - base k) =
      recp (base k ^ 3) + recp (topsmall k m) + recp A at ht
    linarith

lemma split_inj {k m : ℕ} (hm : 0 < m) (hm' : m ≤ ex k * 3) :
    Set.InjOn (split k m) {d | d ∣ (2:ℕ)^m+1} := by
  intro d hd d' hd' heq
  let A := topbig k m
  have hA : 0 < A := (Nat.zero_le _).trans_lt (top_big_bound k m)
  have hq : 1 < qfac k * base k ^ 3 := by
    have hq' := qfac_gt_base k
    have hb := base_ge k
    have hx : 0 < base k ^ 3 := Nat.pow_pos (by have := base_ge k; omega)
    exact (show 1 < qfac k by omega).trans_le (Nat.le_mul_of_pos_right _ hx)
  have hP : 0 < (2 : ℕ)^m+1 := by positivity
  have hlarge : (2:ℕ)^m+1 < A := by
    change 2^m+1 < qfac k * base k ^ 3 * (2^m+1)
    simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hq hP
  have hdA : d < A := (Nat.le_of_dvd hP hd).trans_lt hlarge
  have hd'A : d' < A := (Nat.le_of_dvd hP hd').trans_lt hlarge
  have hD : d' * (A^2 / d') = A^2 :=
    Nat.mul_div_cancel' (hd'.trans ((dvd_mul_left (2^m+1) (qfac k * base k^3)).trans
      (dvd_pow_self A (by decide))))
  have hAD : A < A^2 / d' := by
    apply Nat.lt_of_mul_lt_mul_left (a := d')
    rw [hD, pow_two]
    exact Nat.mul_lt_mul_of_pos_right hd'A hA
  have hx : A+d ∈ split k m d := Finset.mem_insert_self _ _
  rw [heq] at hx
  change A+d ∈ insert (A+d') (insert (A+A^2/d') (tail k m)) at hx
  simp only [Finset.mem_insert] at hx
  rcases hx with hx | hx | hx
  · omega
  · omega
  · have ho := tail_lt hm hm' hx
    omega

end OMA148

namespace OMA148

open Polynomial

def pprod (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

lemma pprod_pos {s : Finset ℕ} (h : ∀ p ∈ s, Nat.Prime p) : 0 < pprod s :=
  Finset.prod_pos fun p hp ↦ (h p hp).pos

lemma dvd_pprod_iff {s : Finset ℕ} (h : ∀ p ∈ s, Nat.Prime p) {q : ℕ} (hq : q.Prime) :
    q ∣ pprod s ↔ q ∈ s := by
  rw [pprod, hq.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨p,hp,hd⟩
    have he := (Nat.prime_dvd_prime_iff_eq hq (h p hp)).mp hd
    simpa [he] using hp
  · intro hs
    exact ⟨q, hs, dvd_refl q⟩

lemma pprod_inj {s t : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p)
    (ht : ∀ p ∈ t, Nat.Prime p) (he : pprod s = pprod t) : s = t := by
  ext q
  constructor
  · intro hq
    have hp := hs q hq
    exact (dvd_pprod_iff ht hp).mp (he ▸ (dvd_pprod_iff hs hp).mpr hq)
  · intro hq
    have hp := ht q hq
    exact (dvd_pprod_iff hs hp).mp (he.symm ▸ (dvd_pprod_iff ht hp).mpr hq)

lemma pprod_odd {s : Finset ℕ} (hs : ∀ p ∈ s, Odd p) : Odd (pprod s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pprod]
  | @insert p t hp ih =>
    rw [pprod, Finset.prod_insert hp]
    exact (hs _ (Finset.mem_insert_self _ _)).mul
      (ih fun a ha ↦ hs a (Finset.mem_insert_of_mem ha))

lemma primitive_prime_of_large_cofactors {N : ℕ} (hN : 1 < N)
    (hsize : ∀ p, p.Prime → p ∣ N → ∃ a, N = p*a ∧ ¬ p ∣ a ∧ p < a) :
    ∃ p, p.Prime ∧ orderOf (2 : ZMod p) = N := by
  have hval : 1 < ((cyclotomic N ℤ).eval 2).natAbs := by
    simpa using sub_one_lt_natAbs_cyclotomic_eval hN (q := 2) (by decide)
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hval.ne'
  letI : Fact p.Prime := ⟨hp⟩
  have ev : (cyclotomic N (ZMod p)).eval 2 = 0 := by
    have he := cyclotomic.eval_apply (2 : ℤ) N (Int.castRingHom (ZMod p))
    simp only [eq_intCast, Int.cast_ofNat] at he
    rw [he, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natCast_dvd.2 hpd
  have hpn : ¬ p ∣ N := by
    intro hpn
    obtain ⟨a,ha,hpa,haa⟩ := hsize p hp hpn
    have hcast : NeZero (a : ZMod p) := ⟨fun ha0 ↦ hpa ((ZMod.natCast_eq_zero_iff a p).mp ha0)⟩
    letI := hcast
    rw [ha, mul_comm p a, cyclotomic_mul_prime_eq_pow_of_not_dvd (ZMod p) hpa,
      Polynomial.eval_pow] at ev
    have hr : IsRoot (cyclotomic a (ZMod p)) (2 : ZMod p) :=
      (pow_eq_zero_iff (by have := hp.two_le; omega : p-1 ≠ 0)).mp ev
    have ho : IsPrimitiveRoot (2 : ZMod p) a := isRoot_cyclotomic_iff.mp hr
    have hnz : (2 : ZMod p) ≠ 0 := by
      intro hz
      have hzero := ho.pow_eq_one
      rw [hz, zero_pow (by omega : a ≠ 0)] at hzero
      exact zero_ne_one hzero
    have hh := Nat.le_of_dvd (by have := hp.two_le; omega : 0 < p-1)
      (ZMod.orderOf_dvd_card_sub_one hnz)
    rw [← ho.eq_orderOf] at hh
    omega
  letI : NeZero (N : ZMod p) := ⟨fun hz ↦ hpn ((ZMod.natCast_eq_zero_iff N p).mp hz)⟩
  exact ⟨p,hp, ((isRoot_cyclotomic_iff).mp (show IsRoot _ _ from ev)).eq_orderOf.symm⟩

lemma prime_for_divisor {cap : ℕ} (hc : 4 ≤ cap)
    {u v : Finset ℕ} (hu : u ⊆ v) (hcard : 3 ≤ u.card)
    (hv : ∀ p ∈ v, p.Prime ∧ Nat.sqrt cap < p ∧ p ≤ cap) :
    ∃ p, p.Prime ∧ orderOf (2 : ZMod p) = 2*pprod v := by
  have h2 : 2 ∉ v := by
    intro hh
    have h := (hv 2 hh).2.1
    exact (not_lt_of_ge (Nat.le_sqrt'.2 (by simpa using hc))) h
  let S := insert 2 v
  have hprime : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    change p ∈ insert 2 v at hp
    rcases Finset.mem_insert.mp hp with rfl | hh
    · exact Nat.prime_two
    · exact (hv p hh).1
  have hN : 2*pprod v = pprod S := by simp [S, pprod, h2]
  apply primitive_prime_of_large_cofactors (show 1 < 2*pprod v by
    have hp := pprod_pos (fun p hp ↦ (hv p hp).1); omega)
  intro p hp hpd
  have hpS : p ∈ S := (dvd_pprod_iff hprime hp).mp (hN ▸ hpd)
  let a := pprod (S.erase p)
  have hprod : 2*pprod v = p*a := by
    rw [hN, pprod, ← Finset.mul_prod_erase S (fun z ↦ z) hpS]
    rfl
  refine ⟨a,hprod, ?_, ?_⟩
  · rw [dvd_pprod_iff (fun q hq ↦ hprime q (Finset.mem_of_mem_erase hq)) hp]
    exact Finset.notMem_erase _ _
  have hc' : 1 < (u.erase p).card := by
    by_cases hm : p ∈ u
    · have := Finset.card_erase_add_one hm
      omega
    · simpa [Finset.erase_eq_of_notMem hm] using (show 1 < u.card by omega)
  obtain ⟨b,hbu,c,hcu,hbc⟩ := Finset.one_lt_card.mp hc'
  have hsub : {b,c} ⊆ S.erase p := by
    intro z hz
    have hm : z ∈ u.erase p := (Finset.mem_insert.mp hz).elim
      (fun he ↦ he.symm ▸ hbu) (fun he ↦ (Finset.mem_singleton.mp he).symm ▸ hcu)
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hm).1,
      Finset.mem_insert_of_mem (hu (Finset.mem_of_mem_erase hm))⟩
  have h_dvd : b*c ∣ a := by
    obtain ⟨z,hz⟩ := Finset.prod_dvd_prod_of_subset {b,c} (S.erase p) id hsub
    refine ⟨z, ?_⟩
    change (∏ x ∈ S.erase p, x) = b*c*z
    simpa [Finset.prod_pair hbc] using hz
  have hb := (hv b (hu (Finset.mem_of_mem_erase hbu))).2.1
  have hcc := (hv c (hu (Finset.mem_of_mem_erase hcu))).2.1
  have hmul : cap < b*c :=
    (Nat.lt_succ_sqrt cap).trans_le (Nat.mul_le_mul (by omega) (by omega))
  have hpa : p ≤ cap := by
    rcases Finset.mem_insert.mp hpS with rfl | hvp
    · omega
    · exact (hv p hvp).2.2
  exact hpa.trans_lt (hmul.trans_le (Nat.le_of_dvd
    (pprod_pos (fun z hz ↦ hprime z (Finset.mem_of_mem_erase hz))) h_dvd))

lemma plus_dvd_of_order {m d p : ℕ} (hm : Odd m) (hd : d ∣ m) (hp : p.Prime)
    (ho : orderOf (2 : ZMod p) = 2*d) : p ∣ 2^m+1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p)^(2*m) = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [ho]
    exact Nat.mul_dvd_mul_left 2 hd
  have hone : (2 : ZMod p)^m ≠ 1 := by
    intro h
    have hdiv := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [ho] at hdiv
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr ((dvd_mul_right 2 d).trans hdiv))
  have hneg : (2 : ZMod p)^m + 1 = 0 := by
    have hmul : ((2 : ZMod p)^m + 1) * ((2 : ZMod p)^m - 1) = 0 := by
      rw [mul_comm 2 m, pow_mul] at htwo
      calc
        _ = ((2 : ZMod p)^m)^2 - 1 := by ring
        _ = 0 := by rw [htwo, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hone)
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  exact hneg

lemma many_prime_factors {cap : ℕ} (hc : 4 ≤ cap)
    {s u : Finset ℕ} (hu : u ⊆ s) (hcard : u.card = 3)
    (hs : ∀ p ∈ s, p.Prime ∧ Nat.sqrt cap < p ∧ p ≤ cap) :
    2^(s.card-3) ≤ ((2 : ℕ)^(pprod s)+1).primeFactors.card := by
  classical
  let t := s \ u
  let m := pprod s
  have ht : t.card = s.card-3 := by
    simp [t, Finset.card_sdiff_of_subset hu, hcard]
  have hm : Odd m := by
    apply pprod_odd
    intro p hp
    rcases (hs p hp).1.eq_two_or_odd' with h | h
    · subst p
      have h2 := (hs 2 hp).2.1
      exact (not_lt_of_ge (Nat.le_sqrt'.2 (by simpa using hc)) h2).elim
    · exact h
  have hsv (v : Finset ℕ) (hv : v ⊆ t) : u ∪ v ⊆ s :=
    Finset.union_subset hu (hv.trans Finset.sdiff_subset)
  have hprim (v : Finset ℕ) (hv : v ⊆ t) :
      ∃ p, p.Prime ∧ orderOf (2 : ZMod p) = 2*pprod (u ∪ v) :=
    prime_for_divisor hc Finset.subset_union_left hcard.ge (fun p hp ↦ hs p (hsv v hv hp))
  let f (v : Finset ℕ) := if hv : v ⊆ t then Classical.choose (hprim v hv) else 2
  have hf (v : Finset ℕ) (hv : v ⊆ t) : (f v).Prime ∧ orderOf (2 : ZMod (f v)) = 2*pprod (u∪v) := by
    have he : f v = Classical.choose (hprim v hv) := dif_pos hv
    rw [he]
    exact Classical.choose_spec (hprim v hv)
  have hinj : Set.InjOn f (t.powerset : Set (Finset ℕ)) := by
    intro v hv w hw he
    have hv' := Finset.mem_powerset.mp hv
    have hw' := Finset.mem_powerset.mp hw
    have ho := (hf v hv').2
    rw [he, (hf w hw').2] at ho
    have he' : pprod (u ∪ v) = pprod (u ∪ w) := by omega
    have hp := pprod_inj (fun z hz ↦ (hs z (hsv v hv' hz)).1)
      (fun z hz ↦ (hs z (hsv w hw' hz)).1) he'
    have hdisv : Disjoint v u := by
      apply Finset.disjoint_left.mpr
      intro z hz hzu
      exact (Finset.mem_sdiff.mp (hv' hz)).2 hzu
    have hdisw : Disjoint w u := by
      apply Finset.disjoint_left.mpr
      intro z hz hzu
      exact (Finset.mem_sdiff.mp (hw' hz)).2 hzu
    ext z
    constructor
    · intro hz
      have hz' := Finset.mem_union_right u hz
      rw [hp] at hz'
      exact (Finset.mem_union.mp hz').resolve_left (Finset.disjoint_left.mp hdisv hz)
    · intro hz
      have hz' := Finset.mem_union_right u hz
      rw [← hp] at hz'
      exact (Finset.mem_union.mp hz').resolve_left (Finset.disjoint_left.mp hdisw hz)
  have hmap : Set.MapsTo f (t.powerset : Set (Finset ℕ))
      (((2 : ℕ)^m+1).primeFactors : Set ℕ) := by
    intro v hv
    have hv' := Finset.mem_powerset.mp hv
    obtain ⟨hp,ho⟩ := hf v hv'
    exact hp.mem_primeFactors (plus_dvd_of_order hm
      (Finset.prod_dvd_prod_of_subset _ _ _ (hsv v hv')) hp ho) (by positivity)
  have h := Finset.card_le_card_of_injOn f hmap hinj
  simpa only [Finset.card_powerset, ht, m] using h

lemma many_splits {k m : ℕ} (hm : 0 < m) (hm' : m ≤ 3*ex k) :
    2^((2^m+1 : ℕ).primeFactors.card) ≤ Erdos148.F (3*k+6) := by
  classical
  let b : ℕ := 2^m+1
  let t := b.primeFactors
  let f (v : Finset ℕ) := split k m (pprod v)
  have hm'' : m ≤ ex k*3 := by omega
  have hdiv (v : Finset ℕ) (hv : v ⊆ t) : pprod v ∣ b :=
    (Finset.prod_dvd_prod_of_subset _ _ _ hv).trans (Nat.prod_primeFactors_dvd b)
  have hinj : Set.InjOn f (t.powerset : Set (Finset ℕ)) := by
    intro v hv w hw h
    have hv' := Finset.mem_powerset.mp hv
    have hw' := Finset.mem_powerset.mp hw
    exact pprod_inj (fun z hz ↦ Nat.prime_of_mem_primeFactors (hv' hz))
      (fun z hz ↦ Nat.prime_of_mem_primeFactors (hw' hz))
      (split_inj hm hm'' (hdiv v hv') (hdiv w hw') h)
  have hmapped : Set.MapsTo f (t.powerset : Set (Finset ℕ)) (solutions (3*k+6) 1) :=
    fun v hv ↦ split_valid hm hm'' (hdiv v (Finset.mem_powerset.mp hv))
  rw [F_def]
  have h := Set.ncard_le_ncard_of_injOn f hmapped hinj (solutions_finite _ _)
  simpa only [Set.ncard_coe_finset, Finset.card_powerset, t, b] using h

end OMA148

namespace OMA148

open Real

def level (n : ℕ) : ℕ := (n-6)/3

noncomputable def ell (n : ℕ) : ℝ := log (2*(n:ℝ))

noncomputable def budget (n : ℕ) : ℝ := ((n:ℝ)/3-4)*log 3

noncomputable def slots (n : ℕ) : ℕ := ⌊budget n / ell n⌋₊

def pool (n : ℕ) : Finset ℕ := (Nat.primesLE (2*n)).filter (fun p ↦ Nat.sqrt (2*n) < p)

lemma ell_pos {n : ℕ} (hn : 1 ≤ n) : 0 < ell n := by
  apply Real.log_pos
  have h : (1:ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma ell_eq {n : ℕ} (hn : 1 ≤ n) : ell n = log 2 + log n := by
  have h : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  exact Real.log_mul (by norm_num) h

lemma nat_tends : Tendsto (fun n : ℕ ↦ (n:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop

lemma twice_tends : Tendsto (fun n : ℕ ↦ 2*(n:ℝ)) atTop atTop :=
  nat_tends.const_mul_atTop (by norm_num)

lemma log_div_nat : Tendsto (fun n : ℕ ↦ log n/(n:ℝ)) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp nat_tends

lemma const_div_nat (c : ℝ) : Tendsto (fun n : ℕ ↦ c/(n:ℝ)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n : ℕ ↦ (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp nat_tends
  simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := c)).mul hh

lemma ell_div_nat : Tendsto (fun n : ℕ ↦ ell n/(n:ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ ↦ log 2/(n:ℝ) + log n/(n:ℝ)) atTop (𝓝 0) := by
    simpa using (const_div_nat (log 2)).add log_div_nat
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  rw [ell_eq hn, add_div]

lemma ell_tends : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp twice_tends

lemma cut_loss :
    ∀ᶠ n : ℕ in atTop, ((Nat.sqrt (2*n):ℕ):ℝ) * ell n / (2*(n:ℝ)) +
      ell n / (2*(n:ℝ)) < log 2/4 := by
  have ht : Tendsto (fun x : ℝ ↦ log x / √x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)).tendsto_div_nhds_zero
  have ht' : Tendsto (fun x : ℝ ↦ log x / √x + log x / x) atTop (𝓝 0) := by
    simpa using ht.add Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlog := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  have hp := (tendsto_order.mp (ht'.comp twice_tends)).2 (log 2/4) (by positivity)
  filter_upwards [hp, eventually_ge_atTop (1:ℕ)] with n hn h1
  change log (2*(n:ℝ)) / √(2*(n:ℝ)) + log (2*(n:ℝ))/(2*(n:ℝ)) < log 2/4 at hn
  have hs : (Nat.sqrt (2*n) : ℝ) ≤ √(2*(n:ℝ)) :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' (2*n))
  have hx : (0:ℝ) < 2*(n:ℝ) := by
    have h : (1:ℝ) ≤ n := by exact_mod_cast h1
    linarith
  have hs' : 0 < √(2*(n:ℝ)) := Real.sqrt_pos.2 hx
  have he : √(2*(n:ℝ)) * ell n / (2*(n:ℝ)) = ell n / √(2*(n:ℝ)) := by
    apply (div_eq_div_iff hx.ne' hs'.ne').2
    have hsq := Real.sq_sqrt hx.le
    nlinarith [congrArg (fun x : ℝ ↦ x * ell n) hsq]
  have hmono := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hs (ell_pos h1).le) hx.le
  rw [he] at hmono
  exact (add_le_add hmono (le_refl (ell n / (2*(n:ℝ))))).trans_lt hn

lemma slots_enough : ∀ᶠ n : ℕ in atTop, 3 ≤ slots n ∧ slots n ≤ (pool n).card := by
  have hln2 := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  have hln3 := Real.log_pos (show (1:ℝ) < 3 by norm_num)
  have hlower := (tendsto_order.mp ell_div_nat).2 (log 3/24) (by positivity)
  have hupper := (tendsto_order.mp ell_div_nat).2 (log 2/4) (by positivity)
  filter_upwards [eventually_ge_atTop (24:ℕ), hlower, hupper, cut_loss]
    with n hn hlow hup hcut
  have hnr : (24:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n:ℝ) := by linarith
  have he := ell_pos (by omega : 1 ≤ n)
  have hb : 0 ≤ budget n := by
    unfold budget
    exact mul_nonneg (by linarith) hln3.le
  have hR := Nat.floor_le (div_nonneg hb he.le)
  have hR' : (slots n : ℝ) * ell n ≤ budget n := (le_div_iff₀ he).mp hR
  have hlow' := (div_lt_iff₀ hnpos).mp hlow
  have hup' := (div_lt_iff₀ hnpos).mp hup
  constructor
  · apply Nat.le_floor
    apply (le_div_iff₀ he).2
    have hlo : (n:ℝ)/6 * log 3 ≤ budget n := by
      unfold budget
      exact mul_le_mul_of_nonneg_right (by linarith) hln3.le
    push_cast
    nlinarith
  have hbudget : budget n ≤ n * log 2 := by
    have hle : log 3 ≤ 3 * log 2 := by
      calc
        log 3 ≤ log ((2:ℝ)^3) := Real.log_le_log (by norm_num) (by norm_num)
        _ = 3 * log 2 := by rw [Real.log_pow]; norm_num
    unfold budget
    calc
      _ ≤ ((n:ℝ)/3) * log 3 := mul_le_mul_of_nonneg_right (by linarith) hln3.le
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hle (show 0 ≤ (n:ℝ)/3 by positivity)]
  have hcut' : ((Nat.sqrt (2*n) : ℝ)+1) * ell n < (n:ℝ) * log 2/2 := by
    rw [← add_div] at hcut
    have ht := (div_lt_iff₀ (show (0:ℝ) < 2*(n:ℝ) by positivity)).mp hcut
    rw [add_mul, one_mul]
    linarith
  have hlog' : log (2*(n:ℝ)+1) ≤ (n:ℝ) * log 2/2 := by
    have h := Real.log_le_log (x := 2*(n:ℝ)+1) (y := 2*(2*(n:ℝ))) (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : 2*(n:ℝ) ≠ 0)] at h
    change log (2*(n:ℝ)+1) ≤ log 2 + ell n at h
    nlinarith
  have hpi := Chebyshev.pi_ge (2*n)
  push_cast at hpi
  change (2*(n:ℝ)*log 2 - log (2*(n:ℝ)+1)) / ell n ≤ (Nat.primeCounting (2*n):ℝ) at hpi
  have hpi' := (div_le_iff₀ he).mp hpi
  have hout : (slots n : ℝ) + ((Nat.sqrt (2*n):ℝ)+1) ≤ (Nat.primeCounting (2*n):ℝ) := by
    apply le_of_mul_le_mul_right _ he
    rw [add_mul]
    linarith
  have hnat : slots n + (Nat.sqrt (2*n)+1) ≤ Nat.primeCounting (2*n) := by exact_mod_cast hout
  have hbad :
      ((Nat.primesLE (2*n)).filter (fun p ↦ ¬Nat.sqrt (2*n) < p)).card ≤ Nat.sqrt (2*n)+1 := by
    rw [← Finset.card_range (Nat.sqrt (2*n)+1)]
    apply Finset.card_le_card
    intro p hp
    exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hp).2; omega)
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Nat.primesLE (2*n)) (p := fun p ↦ Nat.sqrt (2*n) < p)
  rw [Nat.primesLE_card_eq_primeCounting] at hsum
  change (pool n).card + _ = _ at hsum
  omega

lemma well_sized_product {n : ℕ} (hn : 24 ≤ n) {s : Finset ℕ}
    (hs : s ⊆ pool n) (hc : s.card = slots n) :
    0 < pprod s ∧ pprod s ≤ 3*ex (level n) := by
  have hprop (p : ℕ) (hp : p ∈ s) : p ≤ 2*n ∧ p.Prime :=
    Nat.mem_primesLE.mp (Finset.mem_filter.mp (hs hp)).1
  have hpos := pprod_pos (fun p hp ↦ (hprop p hp).2)
  refine ⟨hpos, ?_⟩
  have hprod : pprod s ≤ (2*n)^(slots n) := by
    rw [← hc, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun p hp ↦ (hprop p hp).1
  have hprodR : (pprod s : ℝ) ≤ (2*(n:ℝ))^(slots n) := by exact_mod_cast hprod
  have hlogprod := Real.log_le_log (by exact_mod_cast hpos) hprodR
  rw [Real.log_pow] at hlogprod
  change log (pprod s : ℝ) ≤ (slots n : ℝ) * ell n at hlogprod
  have hnr : (24:ℝ) ≤ n := by exact_mod_cast hn
  have hb : 0 ≤ budget n := by
    unfold budget
    exact mul_nonneg (by linarith) (Real.log_nonneg (by norm_num))
  have he := ell_pos (by omega : 1 ≤ n)
  have hslots : (slots n:ℝ) * ell n ≤ budget n :=
    (le_div_iff₀ he).mp (Nat.floor_le (div_nonneg hb he.le))
  have hJ : (n:ℝ) ≤ 3*(level n:ℝ) + 8 := by
    exact_mod_cast (show n ≤ 3*level n + 8 by unfold level; omega)
  have hbr : budget n ≤ ((level n : ℝ)+1)*log 3 := by
    unfold budget
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg (by norm_num))
  have hpow : ((3*ex (level n) : ℕ) : ℝ) = (3:ℝ)^(level n+1) := by
    simp [ex, pow_succ']
  have hcmp : log (pprod s : ℝ) ≤ log ((3*ex (level n) : ℕ) : ℝ) := by
    rw [hpow, Real.log_pow, Nat.cast_succ]
    exact hlogprod.trans (hslots.trans hbr)
  exact_mod_cast (Real.log_le_log_iff (by exact_mod_cast hpos)
    (by have := ex_pos (level n); positivity)).mp hcmp

lemma counting_eventually : ∀ᶠ n : ℕ in atTop, 2^(2^(slots n-3)) ≤ Erdos148.F n := by
  filter_upwards [eventually_ge_atTop (24:ℕ), slots_enough] with n hn hslots
  obtain ⟨s,hs,hc⟩ := Finset.exists_subset_card_eq hslots.2
  obtain ⟨u,hu,hu3⟩ := Finset.exists_subset_card_eq (show 3 ≤ s.card by rw [hc]; exact hslots.1)
  have hpr (p : ℕ) (hp : p ∈ s) : p.Prime ∧ Nat.sqrt (2*n) < p ∧ p ≤ 2*n := by
    have hf := Finset.mem_filter.mp (hs hp)
    exact ⟨(Nat.mem_primesLE.mp hf.1).2,hf.2,(Nat.mem_primesLE.mp hf.1).1⟩
  have hm := well_sized_product hn hs hc
  have hmany := many_prime_factors (by omega : 4 ≤ 2*n) hu hu3 hpr
  rw [hc] at hmany
  exact (Nat.pow_le_pow_right (by decide) hmany).trans
    ((many_splits hm.1 hm.2).trans (F_mono (by omega) (by unfold level; omega)))

noncomputable def scaled (n : ℕ) : ℝ :=
  (((slots n-3 : ℕ):ℝ) * log 2 + log (log 2)) * (log n/(n:ℝ))

lemma slots_limit :
    Tendsto (fun n : ℕ ↦ (slots n:ℝ) * (ell n/(n:ℝ))) atTop (𝓝 (log 3/3)) := by
  have hbudget :
      Tendsto (fun n : ℕ ↦ budget n / (n:ℝ)) atTop (𝓝 (log 3/3)) := by
    have h : Tendsto (fun n : ℕ ↦ log 3/3 - (4*log 3)/(n:ℝ)) atTop (𝓝 (log 3/3)) := by
      simpa using tendsto_const_nhds.sub (const_div_nat (4*log 3))
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    unfold budget
    have hne : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp <;> ring
  have hfin :
      Tendsto (fun n : ℕ ↦ budget n/(n:ℝ) - ell n/(n:ℝ)) atTop (𝓝 (log 3/3)) := by
    simpa using hbudget.sub ell_div_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hfin hbudget ?_ ?_
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have he := ell_pos hn
    have hd := Nat.lt_floor_add_one (budget n / ell n)
    have hd' := (div_lt_iff₀ he).mp hd
    change budget n < ((slots n : ℝ) + 1) * ell n at hd'
    rw [add_mul, one_mul] at hd'
    have hnz : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    rw [← sub_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hnz.le
  · filter_upwards [eventually_ge_atTop (24:ℕ)] with n hn
    have he := ell_pos (by omega : 1 ≤ n)
    have hnr : (24:ℝ) ≤ n := by exact_mod_cast hn
    have hb : 0 ≤ budget n := by
      unfold budget
      exact mul_nonneg (by linarith) (Real.log_nonneg (by norm_num))
    have hf := (le_div_iff₀ he).mp (Nat.floor_le (div_nonneg hb he.le))
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hf (by positivity)

lemma scaled_limit : Tendsto scaled atTop (𝓝 (log 2 * log 3 / 3)) := by
  have hr : Tendsto (fun n : ℕ ↦ ((slots n-3 : ℕ):ℝ) * (ell n/(n:ℝ))) atTop
      (𝓝 (log 3/3)) := by
    have h := slots_limit.sub ((tendsto_const_nhds (x := (3:ℝ))).mul ell_div_nat)
    apply (show Tendsto (fun n : ℕ ↦ (slots n:ℝ) * (ell n/(n:ℝ)) -
        3 * (ell n/(n:ℝ))) atTop (𝓝 (log 3/3)) by simpa using h).congr'
    filter_upwards [slots_enough] with n hn
    rw [Nat.cast_sub hn.1]
    push_cast
    ring
  have hnorm : Tendsto (fun n : ℕ ↦ log n/ell n) atTop (𝓝 1) := by
    have ht : Tendsto (fun n : ℕ ↦ (ell n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ell_tends
    have hs := (tendsto_const_nhds (x := (1:ℝ))).sub ((tendsto_const_nhds (x := log 2)).mul ht)
    apply (show Tendsto (fun n : ℕ ↦ 1 - log 2 * (ell n)⁻¹) atTop (𝓝 1) by
      simpa using hs).congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have he := ell_pos hn
    field_simp
    rw [ell_eq hn]
    ring
  have ht := ((tendsto_const_nhds (x := log 2)).mul (hr.mul hnorm)).add
    ((tendsto_const_nhds (x := log (log 2))).mul log_div_nat)
  apply (show Tendsto (fun n : ℕ ↦ log 2 * (((slots n-3 : ℕ):ℝ) * (ell n/(n:ℝ)) *
      (log n/ell n)) + log (log 2) * (log n/(n:ℝ))) atTop
      (𝓝 (log 2 * log 3 / 3)) by simpa [mul_div_assoc] using ht).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hne := (ell_pos hn).ne'
  have hnr : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold scaled
  field_simp <;> ring

lemma exp_scaled {n : ℕ} (hn : 2 ≤ n) :
    exp (exp (scaled n * ((n:ℝ)/log n))) = ((2^(2^(slots n-3)) : ℕ) : ℝ) := by
  have hnr : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hcancel : scaled n * ((n:ℝ)/log n) = ((slots n-3:ℕ):ℝ)*log 2 + log (log 2) := by
    unfold scaled
    field_simp
  rw [hcancel, Real.exp_add, Real.exp_log hlog2]
  have hp (a : ℕ) : exp ((a:ℝ)*log 2) = (2:ℝ)^a := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [hp (slots n-3)]
  have hc : (2:ℝ)^(slots n-3) = ((2^(slots n-3) : ℕ):ℝ) := by norm_cast
  rw [hc, hp]
  push_cast
  norm_num

end OMA148

open Real

theorem OMA.solution : type_of% @Erdos148.erdos_148.variants.lower_bound := by
  refine ⟨fun n ↦ OMA148.scaled n - log 2 * log 3 / 3, ?_, ?_⟩
  · apply (Asymptotics.isLittleO_one_iff ℝ).mpr
    simpa using OMA148.scaled_limit.sub (tendsto_const_nhds (x := log 2 * log 3 / 3))
  filter_upwards [OMA148.counting_eventually, eventually_ge_atTop (2:ℕ)] with n hn hn2
  rw [show log 2 * log 3 / 3 + (OMA148.scaled n - log 2 * log 3 / 3) =
      OMA148.scaled n by ring, OMA148.exp_scaled hn2]
  exact_mod_cast hn
