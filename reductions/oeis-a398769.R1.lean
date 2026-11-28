import OMAStatements.S_oeis_a398769
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic.Tauto

namespace OMA.R_oeis_a398769_R1

/-- Without a multiple of three, exactly two digits are 5 and all the others are 7. -/
def H1 : Prop := ∀ k : ℕ, let L := Nat.digits 10 k
  L.length % 2 = 1 → (∀ d ∈ L, d = 5 ∨ d = 7) →
  L.count 5 = 2 → 7 ∈ L → k % 10 = 5 → ¬ L.prod * L.sum ∣ k

/-- If 3 or 9 occurs, the entire digit sum must be divisible by nine. -/
def H2 : Prop := ∀ k : ℕ, let L := Nat.digits 10 k
  L.length % 2 = 1 → (∀ d ∈ L, d = 3 ∨ d = 5 ∨ d = 7 ∨ d = 9) →
  (3 ∈ L ∨ 9 ∈ L) → 9 ∣ L.sum → (5 ∈ L → k % 10 = 5) →
  L.count 5 ≤ 8 → (¬ 1953125 ∣ k) → ¬ L.prod * L.sum ∣ k

lemma digits_remainder (k w : ℕ) (hn : 0 ∉ Nat.digits 10 k) :
    Nat.digits 10 (k % (10 ^ w)) = (Nat.digits 10 k).take w := by
  rw [Nat.self_mod_pow_eq_ofDigits_take w k (by decide : 2 ≤ 10)]
  apply Nat.digits_ofDigits 10 (by decide)
  · intro d hd
    exact Nat.digits_lt_base (by decide : 2 ≤ 10) (List.mem_of_mem_take hd)
  · intro h he
    have hm := List.mem_of_mem_take (List.getLast_mem h)
    exact hn (he ▸ hm)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma suffix_table : ∀ i : Fin 512, i.val % 2 = 1 →
    ((Nat.digits 10 (1953125 * i.val)).all
      (fun d => d == 3 || d == 5 || d == 7 || d == 9)) = false := by
  decide

lemma nine_fives_impossible (k : ℕ) (odd : k % 2 = 1)
    (alphabet : ∀ d ∈ Nat.digits 10 k, d = 3 ∨ d = 5 ∨ d = 7 ∨ d = 9) :
    ¬ 1953125 ∣ k := by
  intro hk
  have hn : 0 ∉ Nat.digits 10 k := by intro h; have := alphabet 0 h; omega
  let r := k % (10 ^ 9)
  have bound : r < 1000000000 := Nat.mod_lt k (by decide)
  have hd : 1953125 ∣ r := (Nat.dvd_mod_iff (by decide : 1953125 ∣ 10^9)).mpr hk
  obtain ⟨v, hv⟩ := hd
  have hvb : v < 512 := by
    rw [hv] at bound
    exact Nat.lt_of_mul_lt_mul_left (show 1953125*v < 1953125*512 from bound)
  have rpar : r % 2 = 1 := (Nat.mod_mod_of_dvd k (by decide : 2 ∣ 10^9)).trans odd
  rw [hv, Nat.mul_mod] at rpar
  have parity : v % 2 = 1 := by simpa using rpar
  have bad := suffix_table ⟨v, hvb⟩ parity
  change ((Nat.digits 10 (1953125 * v)).all _) = false at bad
  rw [← hv] at bad
  have good : ((Nat.digits 10 r).all (fun d => d == 3 || d == 5 || d == 7 || d == 9)) = true := by
    apply List.all_eq_true.mpr
    intro d hd
    rw [digits_remainder k 9 hn] at hd
    rcases alphabet d (List.mem_of_mem_take hd) with rfl | rfl | rfl | rfl <;> decide
  rw [good] at bad
  contradiction


lemma three_fives_impossible (k : ℕ) (hk : k % 2 = 1)
    (alphabet : ∀ d ∈ Nat.digits 10 k, d = 5 ∨ d = 7) : ¬ 125 ∣ k := by
  intro h
  have hn : 0 ∉ Nat.digits 10 k := by intro hz; have := alphabet 0 hz; omega
  let r := k % (10 ^ 3)
  obtain ⟨v, hv⟩ : 125 ∣ r := (Nat.dvd_mod_iff (by decide : 125 ∣ 10^3)).mpr h
  have bound : r < 1000 := Nat.mod_lt k (by decide)
  have hvb : v < 8 := by omega
  have rpar : r % 2 = 1 := (Nat.mod_mod_of_dvd k (by decide : 2 ∣ 10^3)).trans hk
  have table : ∀ i : Fin 8, i.val ≠ 0 →
      ((Nat.digits 10 (125*i.val)).all (fun d => d == 5 || d == 7)) = false := by decide
  have bad := table ⟨v, hvb⟩ (by change v ≠ 0; omega)
  change ((Nat.digits 10 (125*v)).all _) = false at bad
  rw [← hv] at bad
  have good : ((Nat.digits 10 r).all (fun d => d == 5 || d == 7)) = true := by
    apply List.all_eq_true.mpr
    intro d hd
    rw [digits_remainder k 3 hn] at hd
    rcases alphabet d (List.mem_of_mem_take hd) with rfl | rfl <;> decide
  rw [good] at bad
  contradiction

lemma count_power_dvd (L : List ℕ) (d : ℕ) : d ^ (L.count d) ∣ L.prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases h : a = d
    · subst a
      simpa [pow_succ, Nat.mul_comm] using (Nat.mul_dvd_mul_left d ih)
    · simpa [List.count_cons, h] using ih.trans (dvd_mul_left L.prod a)

lemma seven_divides_value (L : List ℕ) (h : ∀ d ∈ L, d = 7) : 7 ∣ Nat.ofDigits 10 L := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := h a (by simp)
    have ht := ih (fun d hd => h d (by simp [hd]))
    rw [Nat.ofDigits_cons, ha]
    exact dvd_add (dvd_refl _) (dvd_mul_of_dvd_right ht 10)

lemma exactly_two_fives (k : ℕ) (hk : k % 2 = 1)
    (ab : ∀ d ∈ Nat.digits 10 k, d = 5 ∨ d = 7) (hends : k % 10 = 5)
    (hseven : 7 ∣ k) (hprod : (Nat.digits 10 k).prod ∣ k) :
    (Nat.digits 10 k).count 5 = 2 := by
  let L := Nat.digits 10 k
  have hupper : L.count 5 < 3 := by
    by_contra! h
    have h125 : 125 ∣ L.prod := (pow_dvd_pow 5 h).trans (count_power_dvd L 5)
    exact three_fives_impossible k hk ab (h125.trans hprod)
  by_contra! hw
  change L.count 5 ≠ 2 at hw
  have he : L = 5 :: Nat.digits 10 (k/10) := by
    simpa [hends, L] using Nat.digits_eq_cons_digits_div (by decide : 1 < 10) (by omega : k ≠ 0)
  have hc : (Nat.digits 10 (k/10)).count 5 = 0 := by
    rw [he] at hupper hw
    simp at hupper hw
    omega
  have ht : 7 ∣ k/10 := by
    rw [← Nat.ofDigits_digits 10 (k/10)]
    apply seven_divides_value
    intro d hd
    have hd' : d ∈ L := by rw [he]; simp [hd]
    have ha := ab d hd'
    have hm : 5 ∉ Nat.digits 10 (k/10) := List.count_eq_zero.mp hc
    exact ha.resolve_left (fun e => hm (e ▸ hd))
  omega


lemma length_parity (L : List ℕ) (ho : ∀ d ∈ L, d % 2 = 1) :
    L.sum % 2 = L.length % 2 := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ha := ho a (by simp)
    have ht := ih (fun d hd => ho d (by simp [hd]))
    simp only [List.sum_cons, List.length_cons]
    omega

lemma fives (n : ℕ) :
    Nat.ofDigits 10 (List.replicate (n+1) 5) % 25 = 5 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons]
    omega

lemma sevens (n : ℕ) :
    let v := Nat.ofDigits 10 (List.replicate (2*n+1) 7) % 49
    v = 7 ∨ v = 42 ∨ v = 14 := by
  induction n with
  | zero => decide
  | succ n ih =>
    change _ % 49 = 7 ∨ _ % 49 = 42 ∨ _ % 49 = 14
    change _ % 49 = 7 ∨ _ % 49 = 42 ∨ _ % 49 = 14 at ih
    rw [show 2*(n+1)+1 = (2*n+1)+1+1 by omega]
    simp only [List.replicate_succ (n := 2*n+1+1), List.replicate_succ (n := 2*n+1), Nat.ofDigits_cons]
    omega

lemma repeated_sum (d : ℕ) (L : List ℕ) (hd : ∀ v ∈ L, v = d) : d ∣ L.sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := hd a (by simp)
    change d ∣ a + L.sum
    exact dvd_add (by rw [ha]) (ih (fun v hv => hd v (by simp [hv])))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a398769.main := by
  intro noThree hasThree k hk divides
  by_contra hOne
  let L := Nat.digits 10 k
  change L.prod * L.sum ∣ k at divides
  change 1 ∉ L at hOne
  have digitDvd {d : ℕ} (hd : d ∈ L) : d ∣ k :=
    (List.dvd_prod hd).trans ((dvd_mul_right _ _).trans divides)
  have sumDvd : L.sum ∣ k := (dvd_mul_left _ _).trans divides
  have oddDigits : ∀ d ∈ L, d % 2 = 1 := by
    intro d hd
    by_contra! h
    have : 2 ∣ k := dvd_trans (by omega : 2 ∣ d) (digitDvd hd)
    omega
  have alphabet : ∀ d ∈ L, d = 3 ∨ d = 5 ∨ d = 7 ∨ d = 9 := by
    intro d hd
    have hodd := oddDigits d hd
    have hlt := Nat.digits_lt_base (by decide : 2 ≤ 10) hd
    have hne : d ≠ 1 := fun e => hOne (e ▸ hd)
    omega
  have lenOdd : L.length % 2 = 1 := by
    have hp := length_parity L oddDigits
    by_contra! h
    have : 2 ∣ k := dvd_trans (by omega : 2 ∣ L.sum) sumDvd
    omega
  have endsFive (h : 5 ∈ L) : k % 10 = 5 := by
    have := digitDvd h
    omega
  by_cases h : 3 ∈ L ∨ 9 ∈ L
  · have hp : 3 ∣ L.prod := by
      rcases h with h | h
      · exact List.dvd_prod h
      · exact dvd_trans (by decide : 3 ∣ 9) (List.dvd_prod h)
    have hk3 : 3 ∣ k := hp.trans ((dvd_mul_right _ _).trans divides)
    have hs3 : 3 ∣ L.sum := (Nat.three_dvd_iff k).mp hk3
    have hk9 : 9 ∣ k := (Nat.mul_dvd_mul hp hs3).trans divides
    have hlim := nine_fives_impossible k hk alphabet
    have hcount : L.count 5 ≤ 8 := by
      by_contra! hmany
      have hpow : 1953125 ∣ L.prod := (pow_dvd_pow 5 hmany).trans (count_power_dvd L 5)
      exact hlim (hpow.trans ((dvd_mul_right _ _).trans divides))
    exact hasThree k lenOdd alphabet h ((Nat.nine_dvd_iff k).mp hk9) endsFive hcount hlim divides
  · have ab : ∀ d ∈ L, d = 5 ∨ d = 7 := by
      intro d hd
      rcases alphabet d hd with rfl | rfl | rfl | rfl <;> tauto
    have rep {v : ℕ} (hv : ∀ d ∈ L, d = v) :
        k = Nat.ofDigits 10 (List.replicate L.length v) := by
      calc
        k = Nat.ofDigits 10 L := (Nat.ofDigits_digits 10 k).symm
        _ = _ := congrArg (Nat.ofDigits 10) (List.eq_replicate_iff.mpr ⟨rfl, hv⟩)
    have mult {v : ℕ} (hv : ∀ d ∈ L, d = v) : v*v ∣ k := by
      have hne : L ≠ [] := by intro he; simp [he] at lenOdd
      obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil L hne
      have hp : v ∣ L.prod := List.dvd_prod (hv d hd ▸ hd)
      exact (Nat.mul_dvd_mul hp (repeated_sum v L hv)).trans divides
    have hasFive : 5 ∈ L := by
      by_contra hnot
      have hv (d) (hd : d ∈ L) : d = 7 := (ab d hd).resolve_left (fun e => hnot (e ▸ hd))
      have he := rep hv
      have hm := mult hv
      obtain ⟨u, hu⟩ : ∃ u, L.length = 2*u+1 := ⟨L.length/2, by omega⟩
      rw [hu] at he
      have hr := sevens u
      change _ % 49 = 7 ∨ _ % 49 = 42 ∨ _ % 49 = 14 at hr
      rw [← he] at hr
      omega
    have hasSeven : 7 ∈ L := by
      by_contra hnot
      have hv (d) (hd : d ∈ L) : d = 5 := (ab d hd).resolve_right (fun e => hnot (e ▸ hd))
      have he := rep hv
      have hm := mult hv
      obtain ⟨u, hu⟩ : ∃ u, L.length = u+1 := ⟨L.length-1, by omega⟩
      rw [hu] at he
      have hr := fives u
      rw [← he] at hr
      omega
    have htwo := exactly_two_fives k hk ab (endsFive hasFive) (digitDvd hasSeven)
      ((dvd_mul_right _ _).trans divides)
    exact noThree k lenOdd ab htwo hasSeven (endsFive hasFive) divides

end OMA.R_oeis_a398769_R1
