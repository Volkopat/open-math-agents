import FormalConjectures.GreensOpenProblems.«44»

-- Credit: @senamakel

-- Problem: Green's Open Problem 44
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/44.lean (declaration Green44.green_44)
-- Disproof of the formal statement. Take N = 100000 and the 1000 smallest primes above 20003
-- (all at most 30161, so p 999 ^ 10 < N ^ 9). Let A i be the residues 10002, ..., 10001 + p i / 2,
-- which are distinct and avoid 1, ..., 10001 because p i > 20002. Then every x in [1, 10001]
-- survives the sieve, so 10 * remaining.card > N. Primality is checked by trial division up to 173.

namespace Green44Disproof

def L := ((List.range 10159).map (· + 20003)).filter fun q => (List.range 174).all fun m => m < 2 || q % m != 0

theorem L_len : L.length = 1000 := by decide +kernel

theorem L_all : L.all (fun q => 20003 ≤ q && q ≤ 30161 &&
    (List.range 174).all (fun m => m < 2 || q % m != 0)) = true := by decide +kernel

theorem L_chain : List.IsChain (· < ·) L := by decide +kernel

theorem prime_of_check (q : ℕ) (h2 : 2 ≤ q) (hlt : q < 174 * 174)
    (h : ∀ m < 174, 2 ≤ m → q % m ≠ 0) : q.Prime := by
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm hle hdvd => ?_⟩
  have hmm : m * m ≤ q := Nat.le_sqrt.1 hle
  have hm174 : m < 174 := by nlinarith
  exact h m hm174 hm (Nat.mod_eq_zero_of_dvd hdvd)

theorem mem_props (q : ℕ) (hq : q ∈ L) :
    20003 ≤ q ∧ q ≤ 30161 ∧ q.Prime := by
  have h := L_all
  rw [List.all_eq_true] at h
  have h' := h q hq
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h'
  obtain ⟨⟨h1, h2⟩, h3⟩ := h'
  refine ⟨h1, h2, prime_of_check q (by omega) (by omega) fun m hm hm2 => ?_⟩
  rcases h3 m hm with h | h
  · omega
  · exact h

def p (i : Fin 1000) : ℕ := L[i.val]'(by rw [L_len]; exact i.isLt)

theorem p_mem (i : Fin 1000) : p i ∈ L := List.getElem_mem _

theorem p_strictMono : StrictMono p := by
  intro i j hij
  have hp := List.isChain_iff_pairwise.1 L_chain
  rw [List.pairwise_iff_getElem] at hp
  exact hp i.val j.val _ _ hij

def A (q : Fin 1000 → ℕ) (i : Fin 1000) : Finset (ZMod (q i)) :=
  (Finset.range (q i / 2)).image (fun j => ((10002 + j : ℕ) : ZMod (q i)))

theorem A_card (q : Fin 1000 → ℕ) (hq : ∀ i, 20003 ≤ q i) (i : Fin 1000) :
    (A q i).card = q i / 2 := by
  have h1 := hq i
  unfold A
  rw [Finset.card_image_of_injOn]
  · simp
  · intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hab
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega

theorem not_mem_A (q : Fin 1000 → ℕ) (hq : ∀ i, 20003 ≤ q i) (i : Fin 1000) (x : ℕ)
    (hx : x ≤ 10001) : (x : ZMod (q i)) ∉ A q i := by
  have h1 := hq i
  unfold A
  rw [Finset.mem_image]
  rintro ⟨j, hj, hjx⟩
  rw [Finset.mem_range] at hj
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hjx
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

theorem main (q : Fin 1000 → ℕ) (hlo : ∀ i, 20003 ≤ q i) (hhi : ∀ i, q i ≤ 30161)
    (hpr : ∀ i, (q i).Prime) (hm : StrictMono q) : ¬ (type_of% @Green44.green_44) := by
  intro H
  have hb : q 999 ^ 10 < 100000 ^ 9 := by
    have h10 : q 999 ^ 10 ≤ 30161 ^ 10 := Nat.pow_le_pow_left (hhi 999) 10
    have h11 : (30161 : ℕ) ^ 10 < 100000 ^ 9 := by norm_num
    exact lt_of_le_of_lt h10 h11
  have h := H 100000 q (A q) hpr hm hb (A_card q hlo)
  have hsub : Finset.Icc 1 10001 ⊆ (Finset.Icc 1 100000).filter
      (fun x => ∀ i, (x : ZMod (q i)) ∉ A q i) := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hx.1, by omega⟩, fun i => not_mem_A q hlo i x hx.2⟩
  have hc := Finset.card_le_card hsub
  simp only [Nat.card_Icc] at hc
  omega

end Green44Disproof

theorem OMA.disproof : ¬ (type_of% @Green44.green_44) :=
  Green44Disproof.main Green44Disproof.p (fun i => (Green44Disproof.mem_props _ (Green44Disproof.p_mem i)).1)
    (fun i => (Green44Disproof.mem_props _ (Green44Disproof.p_mem i)).2.1)
    (fun i => (Green44Disproof.mem_props _ (Green44Disproof.p_mem i)).2.2)
    Green44Disproof.p_strictMono
