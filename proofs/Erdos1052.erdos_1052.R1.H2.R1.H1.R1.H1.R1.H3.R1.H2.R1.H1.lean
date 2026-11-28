import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H2_R1

/-!
# Step H1 of the reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H2.R1

Exponent e = 458 of 3 is impossible, so the bound holds with A = 0 (vacuously).

3 ^ 458 + 1 = 2 * 5 * 19039061 * Q, where Q is a prime of 211 digits. Since 3 is the only odd prime
whose square divides n, every odd prime factor of 3 ^ 458 + 1 other than 3 is a simple prime of n
(it divides the unitary divisor sum 2 n). So Q is a simple prime of n. But 5 divides both
3 ^ 458 + 1 and Q + 1, so 5 ^ 2 divides the unitary divisor sum 2 n, while 5 is a simple prime:
contradiction. This uses the balance equation and its consequences (kill_at, facts) proved in the
reduction files.

The primality of Q is certified by a Lucas (Pratt) certificate tree: for each prime p of the tree,
p - 1 is fully factored and a witness a of order p - 1 is given. The modular powers are computed by
the kernel with a repeated-squaring function pw, proved correct below (pw_spec).
-/

namespace OMA.Helpers

/-- Modular exponentiation by repeated squaring, with a fuel argument for structural recursion:
`pw m f b e = b ^ e % m` as soon as `e < 2 ^ f`. -/
def pw (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % m
  | f + 1, b, e =>
    if e = 0 then 1 % m
    else if e % 2 = 1 then pw m f (b * b % m) (e / 2) * b % m
    else pw m f (b * b % m) (e / 2)

theorem pw_spec (m : ℕ) : ∀ f b e, e < 2 ^ f → pw m f b e = b ^ e % m := by
  intro f
  induction f with
  | zero =>
    intro b e he
    have : e = 0 := by simpa using he
    subst this
    simp [pw]
  | succ f ih =>
    intro b e he
    have he2 : e / 2 < 2 ^ f := by rw [pow_succ] at he; omega
    have key := ih (b * b % m) (e / 2) he2
    have hpow : (b * b % m) ^ (e / 2) % m = b ^ (2 * (e / 2)) % m := by
      rw [← Nat.pow_mod, pow_mul, sq]
    by_cases h0 : e = 0
    · subst h0
      simp [pw]
    · by_cases h1 : e % 2 = 1
      · have hsplit : e = 2 * (e / 2) + 1 := by omega
        simp only [pw, h0, h1, if_false, if_true, key, hpow]
        conv_rhs => rw [hsplit, pow_succ]
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      · have hsplit : e = 2 * (e / 2) := by omega
        simp only [pw, h0, h1, if_false, key, hpow]
        rw [← hsplit]

/-- A Lucas certificate: `p - 1` is the product of the list `L`, `a` has order dividing `p - 1`,
and `a ^ ((p - 1) / q) ≠ 1` for every `q` in `L`. All computations are modulo `p`. -/
def cert (p a : ℕ) (L : List ℕ) : Bool :=
  decide (1 < p) && (p - 1 == L.prod) && (pw p p a (p - 1) == 1) &&
    L.all (fun q => pw p p a ((p - 1) / q) != 1)

theorem prime_of_cert (p a : ℕ) (L : List ℕ) (hc : cert p a L = true)
    (hL : ∀ q ∈ L, q.Prime) : p.Prime := by
  simp only [cert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨hp, hprod⟩, hfull⟩, hall⟩ := hc
  have hfuel : ∀ e, e ≤ p - 1 → pw p p a e = a ^ e % p := fun e he =>
    pw_spec p p a e (lt_of_le_of_lt he (lt_of_lt_of_le (by omega) p.lt_two_pow_self.le))
  have hcast : ∀ e, (a : ZMod p) ^ e = ((a ^ e % p : ℕ) : ZMod p) := by
    intro e
    rw [ZMod.natCast_mod, Nat.cast_pow]
  refine lucas_primality p (a : ZMod p) ?_ ?_
  · rw [hcast, ← hfuel _ le_rfl, hfull, Nat.cast_one]
  · intro q hq hqd h
    rw [hprod] at hqd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hqd
    have hqx' : q = x := (Nat.prime_dvd_prime_iff_eq hq (hL x hx)).mp hqx
    subst hqx'
    have h1 := hall q hx
    have hle : (p - 1) / q ≤ p - 1 := Nat.div_le_self _ _
    rw [hcast, ← hfuel _ hle] at h
    have hlt : pw p p a ((p - 1) / q) < p := by
      rw [hfuel _ hle]
      exact Nat.mod_lt _ (by omega)
    have h2 := (ZMod.natCast_eq_natCast_iff' (pw p p a ((p - 1) / q)) 1 p).mp (by rw [h, Nat.cast_one])
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hp] at h2
    exact h1 h2

def sp (q : ℕ) : Bool := decide (1 < q ∧ q < 360000) &&
  (List.range 600).all fun m => m < 2 || q < m * m || q % m != 0

theorem sp_ok (q : ℕ) (h : sp q = true) : q.Prime := by
  simp only [sp, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  refine Nat.prime_def_le_sqrt.2 ⟨h.1.1, fun m h2 hm hd => ?_⟩
  have := Nat.le_sqrt.1 hm
  rcases h.2 m (by nlinarith [h.1.2]) with (h3 | h3) | h3
  · omega
  · omega
  · exact h3 (Nat.mod_eq_zero_of_dvd hd)

def chain : List ℕ → List (ℕ × ℕ × List ℕ) → Bool
  | _, [] => true
  | k, (p, a, L) :: cs => L.all (fun q => k.contains q || sp q) &&
      cert p a L && chain (p :: k) cs

theorem sound (cs : List (ℕ × ℕ × List ℕ)) : ∀ k, chain k cs = true →
    (∀ q ∈ k, q.Prime) → ∀ p ∈ cs.map (·.1) ++ k, p.Prime := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨p, a, L⟩ := c
    intro k h hk
    simp only [chain, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      List.contains_iff_mem] at h
    have hp := prime_of_cert p a L h.1.2 fun q hq => (h.1.1 q hq).elim (hk q) (sp_ok q)
    have := ih _ h.2 (by simpa [hp] using hk)
    intro q hq
    simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hq this ⊢
    rcases hq with rfl | hq | hq
    · exact hp
    · exact this q (Or.inl hq)
    · exact this q (Or.inr (Or.inr hq))

def certs : List (ℕ × ℕ × List ℕ) := [
  (55375561, 11, [2, 2, 2, 3, 3, 5, 193, 797]),
  (292010161, 17, [2, 2, 2, 2, 3, 5, 13, 173, 541]),
  (6260041, 13, [2, 2, 2, 3, 3, 5, 17389]),
  (24551880803, 2, [2, 37, 53, 6260041]),
  (49103761607, 5, [2, 24551880803]),
  (665303323, 2, [2, 3, 1151, 96337]),
  (619078048117961, 3, [2, 2, 2, 5, 43, 541, 665303323]),
  (1868284339168339, 2, [2, 3, 3, 3, 7, 7, 13, 37, 6197, 236879]),
  (286529816279694857749513, 11, [2, 2, 2, 3, 709, 9013, 1868284339168339]),
  (18653681, 6, [2, 2, 2, 2, 5, 431, 541]),
  (32009716597, 2, [2, 2, 3, 11, 13, 18653681]),
  (2496757894567, 5, [2, 3, 13, 32009716597]),
  (1521374455475455781, 2, [2, 2, 5, 30467, 2496757894567]),
  (1901803, 2, [2, 3, 7, 45281]),
  (39879028822393, 5, [2, 2, 2, 3, 3, 3, 193, 503, 1901803]),
  (14072073163, 2, [2, 3, 7, 7039, 47599]),
  (31141357188987371, 2, [2, 5, 13, 29, 587, 14072073163]),
  (29416937523401, 3, [2, 2, 2, 5, 5, 7, 239, 5273, 16673]),
  (142319143738214039, 7, [2, 41, 59, 29416937523401]),
  (284638287476428079, 17, [2, 142319143738214039]),
  (1710959, 17, [2, 71, 12049]),
  (776076771549846271, 3, [2, 3, 5, 7, 641, 977, 3449, 1710959]),
  (8535292333505209288459, 2, [2, 3, 3, 13, 47, 776076771549846271]),
  (10934839, 13, [2, 3, 3, 3, 3, 67499]),
  (328045171, 2, [2, 3, 5, 10934839]),
  (35363356825689644743, 5, [2, 3, 3, 61, 499, 196751, 328045171]),
  (4931632289483375097279809, 3, [2, 2, 2, 2, 2, 2, 2179, 35363356825689644743]),
  (88769381210700751751036563, 2, [2, 3, 3, 4931632289483375097279809]),
  (3883848086440037310497051322544183, 3, [2, 3, 3, 7, 347239, 88769381210700751751036563]),
  (2938403877747137219284354089380826550354938422035201475099792317258946933632118590181850731, 2, [2, 5, 31141357188987371, 284638287476428079, 8535292333505209288459, 3883848086440037310497051322544183]),
  (68970680968988137598347931772763984981852545863721949540826705746146307928219198256064312676941049562890465273, 3, [2, 2, 2, 29, 43, 59, 39879028822393, 2938403877747137219284354089380826550354938422035201475099792317258946933632118590181850731]),
  (1049302322029657087263636853427239717061483168620014582746869687897650603407478424436347449898616761159136772402905959988275932131, 2, [2, 5, 1521374455475455781, 68970680968988137598347931772763984981852545863721949540826705746146307928219198256064312676941049562890465273]),
  (1608582317417214810130635352535801824283625580080564742616555593796775363039054605362655017772160887748612499490552428161762482617917902416636558184042356827836981572487811361331057, 3, [2, 2, 2, 2, 11, 49103761607, 619078048117961, 286529816279694857749513, 1049302322029657087263636853427239717061483168620014582746869687897650603407478424436347449898616761159136772402905959988275932131]),
  (1745376548298255875979192507374504750088219827931938208827516973981765722860972555354002702289104895588612885757598083846275425844450388650127389943613904875063115406417706454079369576338460190775339499104522829, 2, [2, 2, 229, 331, 9923, 22303, 55375561, 292010161, 1608582317417214810130635352535801824283625580080564742616555593796775363039054605362655017772160887748612499490552428161762482617917902416636558184042356827836981572487811361331057])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem kill458 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 458) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 458 * ∏ p ∈ P, p) :
    False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 458 → c ∈ ({3} : Finset ℕ) :=
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.prime_dvd_prime_pow (by norm_num)
  obtain ⟨-, -, -, -, -, -, S7, S8⟩ := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.facts hP hK E
  have hQ : 1745376548298255875979192507374504750088219827931938208827516973981765722860972555354002702289104895588612885757598083846275425844450388650127389943613904875063115406417706454079369576338460190775339499104522829 ∈ P :=
    S7 1745376548298255875979192507374504750088219827931938208827516973981765722860972555354002702289104895588612885757598083846275425844450388650127389943613904875063115406417706454079369576338460190775339499104522829 (sound certs [] (by decide +kernel) (by simp) _ (by simp [certs])) (by norm_num) (by simp) ⟨190390610, by decide +kernel⟩
  exact S8 5 (by norm_num) (by norm_num) (by simp) ⟨66460661142039879632752561757292291563438745370811350812195668292348500970518302001421468086094215485020463274649882263664704910906934921966966069814503390729048066145653009318621632410904200436486652038320911034447138, by decide +kernel⟩
    1745376548298255875979192507374504750088219827931938208827516973981765722860972555354002702289104895588612885757598083846275425844450388650127389943613904875063115406417706454079369576338460190775339499104522829 hQ ⟨349075309659651175195838501474900950017643965586387641765503394796353144572194511070800540457820979117722577151519616769255085168890077730025477988722780975012623081283541290815873915267692038155067899820904566, by decide +kernel⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H2_R1.H1 := by
  refine ⟨0, fun n h hiff he _ => ?_⟩
  exact (OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H2_R1.kill_at h hiff
    (fun _ _ hP E => OMA.Helpers.kill458 hP (by rw [he] at E; exact E))).elim
