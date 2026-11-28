import OMAStatements.S_arxiv_1805_03186

namespace OMA.P_arxiv_1805_03186

open OMA.S_arxiv_1805_03186

private lemma exists_valid {n : ℕ} (hn : 0 < n) (g : Cell n → ℕ) :
    ∃ place, Valid g place := by
  have hne : (Finset.univ : Finset (Cell n)).Nonempty :=
    ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  have hEx : ∀ p : ℕ, ∃ c : Cell n, (g c).factorization p = exponent g p := by
    intro p
    obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_sup Finset.univ hne (fun c => (g c).factorization p)
    exact ⟨c, hc.symm⟩
  choose place hplace using hEx
  exact ⟨place, fun p _ => hplace p⟩

private lemma prime_of_mem_primes {n : ℕ} {g : Cell n → ℕ} {p : ℕ} (hp : p ∈ primes g) :
    p.Prime := by
  unfold primes at hp
  rw [Finset.mem_biUnion] at hp
  obtain ⟨c, _, hpc⟩ := hp
  exact Nat.prime_of_mem_primeFactors hpc

private lemma pairwise_coprime_prime_pows {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (e : ℕ → ℕ) :
    Set.Pairwise (s : Set ℕ) (fun p q => Nat.Coprime (p ^ e p) (q ^ e q)) := by
  intro p hp q hq hpq
  have hp' : p.Prime := hs p hp
  have hq' : q.Prime := hs q hq
  exact ((Nat.coprime_primes hp' hq').mpr hpq).pow (e p) (e q)

private lemma prod_dvd_iff_of_pairwise_coprime {s : Finset ℕ} {f : ℕ → ℕ} {m : ℕ}
    (hcop : Set.Pairwise (s : Set ℕ) (fun p q => Nat.Coprime (f p) (f q))) :
    (∏ p ∈ s, f p) ∣ m ↔ ∀ p ∈ s, f p ∣ m := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hcop_s : Set.Pairwise (s : Set ℕ) (fun p q => Nat.Coprime (f p) (f q)) :=
      hcop.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
    have hcop_a : Nat.Coprime (f a) (∏ p ∈ s, f p) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      exact hcop (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hp) (fun h => ha (h ▸ hp))
    have hmul_iff : f a * (∏ p ∈ s, f p) ∣ m ↔ f a ∣ m ∧ (∏ p ∈ s, f p) ∣ m :=
      ⟨fun h => ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩,
       fun ⟨h1, h2⟩ => hcop_a.mul_dvd_of_dvd_of_dvd h1 h2⟩
    rw [hmul_iff, ih hcop_s]
    simp only [Finset.mem_insert, forall_eq_or_imp]

private lemma modEq_prod_iff_of_pairwise_coprime {s : Finset ℕ} {f : ℕ → ℕ} {a b : ℕ}
    (hcop : Set.Pairwise (s : Set ℕ) (fun p q => Nat.Coprime (f p) (f q))) :
    Nat.ModEq (∏ p ∈ s, f p) a b ↔ ∀ p ∈ s, Nat.ModEq (f p) a b := by
  classical
  induction s using Finset.induction with
  | empty => simp [Nat.ModEq, Nat.mod_one]
  | insert x s hx ih =>
    rw [Finset.prod_insert hx]
    have hcop_s : Set.Pairwise (s : Set ℕ) (fun p q => Nat.Coprime (f p) (f q)) :=
      hcop.mono (by intro y hy; exact Finset.mem_insert_of_mem hy)
    have hcop_x : Nat.Coprime (f x) (∏ p ∈ s, f p) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      exact hcop (Finset.mem_insert_self x s) (Finset.mem_insert_of_mem hp) (fun h => hx (h ▸ hp))
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop_x, ih hcop_s]
    simp only [Finset.mem_insert, forall_eq_or_imp]

private lemma dvd_add_iff_modEq {d x u i : ℕ} (hx : d ∣ x + i) :
    d ∣ u + i ↔ Nat.ModEq d u x := by
  constructor
  · intro hu
    have h1 : Nat.ModEq d (u + i) 0 := Nat.modEq_zero_iff_dvd.mpr hu
    have h2 : Nat.ModEq d (x + i) 0 := Nat.modEq_zero_iff_dvd.mpr hx
    exact Nat.ModEq.add_right_cancel' i (h1.trans h2.symm)
  · intro hux
    have h1 : Nat.ModEq d (u + i) (x + i) := hux.add_right i
    have h2 : Nat.ModEq d (x + i) 0 := Nat.modEq_zero_iff_dvd.mpr hx
    exact Nat.modEq_zero_iff_dvd.mp (h1.trans h2)

private lemma coord_iff {n : ℕ} {g : Cell n → ℕ} (_place : ℕ → Cell n)
    (group : ℕ → Fin n) (u x : ℕ)
    (hx_dvd : ∀ p ∈ primes g, p ^ exponent g p ∣ x + (group p).val) :
    (∀ i : Fin n, block g group i ∣ u + i.val) ↔ Nat.ModEq (period g) u x := by
  have hcop_all := pairwise_coprime_prime_pows
    (s := primes g) (fun p hp => prime_of_mem_primes hp) (exponent g)
  rw [period, modEq_prod_iff_of_pairwise_coprime hcop_all]
  constructor
  · intro hblocks p hp
    have hb := hblocks (group p)
    unfold block at hb
    have hcop_sub : Set.Pairwise (((primes g).filter (fun q => group q = group p) : Finset ℕ) : Set ℕ)
        (fun a b => Nat.Coprime (a ^ exponent g a) (b ^ exponent g b)) :=
      hcop_all.mono (by intro q hq; exact (Finset.mem_filter.mp hq).1)
    have hall := (prod_dvd_iff_of_pairwise_coprime hcop_sub).mp hb
    have hpdvd : p ^ exponent g p ∣ u + (group p).val :=
      hall p (Finset.mem_filter.mpr ⟨hp, rfl⟩)
    exact (dvd_add_iff_modEq (hx_dvd p hp)).mp hpdvd
  · intro hmod i
    unfold block
    have hcop_sub : Set.Pairwise (((primes g).filter (fun q => group q = i) : Finset ℕ) : Set ℕ)
        (fun a b => Nat.Coprime (a ^ exponent g a) (b ^ exponent g b)) :=
      hcop_all.mono (by intro q hq; exact (Finset.mem_filter.mp hq).1)
    rw [prod_dvd_iff_of_pairwise_coprime hcop_sub]
    intro p hp
    rw [Finset.mem_filter] at hp
    have hgi : group p = i := hp.2
    rw [← hgi]
    exact (dvd_add_iff_modEq (hx_dvd p hp.1)).mpr (hmod p hp.1)

private theorem prove_main : ∀ {n : ℕ}, 0 < n → ∀ x y : ℕ, 0 < x → 0 < y →
    (∀ c : Cell n, 1 < grid x y c) →
    let g : Cell n → ℕ := grid x y
    (∃ place, Valid g place) ∧
    ∀ place, Valid g place → ∀ u v : ℕ,
      ((∀ i : Fin n, block g (fun p => (place p).1) i ∣ u + i.val) ∧
       (∀ j : Fin n, block g (fun p => (place p).2) j ∣ v + j.val)) ↔
      (Nat.ModEq (period g) u x ∧ Nat.ModEq (period g) v y) := by
  intro n hn x y _ _ _
  dsimp only
  set g : Cell n → ℕ := grid x y
  refine ⟨exists_valid hn g, ?_⟩
  intro place hvalid u v
  have hx_dvd : ∀ p ∈ primes g, p ^ exponent g p ∣ x + (place p).1.val := by
    intro p hp
    have heq : (g (place p)).factorization p = exponent g p := hvalid p hp
    rw [← heq]
    have h1 : p ^ (g (place p)).factorization p ∣ g (place p) := Nat.ordProj_dvd _ _
    have h2 : g (place p) ∣ x + (place p).1.val := Nat.gcd_dvd_left _ _
    exact dvd_trans h1 h2
  have hy_dvd : ∀ p ∈ primes g, p ^ exponent g p ∣ y + (place p).2.val := by
    intro p hp
    have heq : (g (place p)).factorization p = exponent g p := hvalid p hp
    rw [← heq]
    have h1 : p ^ (g (place p)).factorization p ∣ g (place p) := Nat.ordProj_dvd _ _
    have h2 : g (place p) ∣ y + (place p).2.val := Nat.gcd_dvd_right _ _
    exact dvd_trans h1 h2
  exact and_congr (coord_iff place (fun p => (place p).1) u x hx_dvd)
    (coord_iff place (fun p => (place p).2) v y hy_dvd)

end OMA.P_arxiv_1805_03186

theorem OMA.solution : type_of% @OMA.S_arxiv_1805_03186.main :=
  OMA.P_arxiv_1805_03186.prove_main
