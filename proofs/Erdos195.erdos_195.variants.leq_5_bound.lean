import FormalConjectures.ErdosProblems.«195»
import Mathlib.Order.OrderIsoNat

/-! Geneson (arXiv:1803.06334): order integers by base-8 shells via `Nat.clog 8`
and bit-reversal order within each shell. -/

private def revBits : ℕ → ℤ → ℕ
  | 0, _ => 0
  | k + 1, x => (if x % 2 = 0 then 0 else 2 ^ k) + revBits k (x / 2)

private lemma revBits_lt : ∀ (k : ℕ) (x : ℤ), revBits k x < 2 ^ k
  | 0, _ => Nat.zero_lt_one
  | k + 1, x => by have := revBits_lt k (x / 2); simp only [revBits, pow_succ']; split_ifs <;> omega

private lemma revBits_mod {k : ℕ} {a b : ℤ} (h : revBits (k + 1) a ≤ revBits (k + 1) b) :
    a % 2 ≤ b % 2 := by
  have := revBits_lt k (b / 2); simp only [revBits] at h; split_ifs at h <;> omega

private lemma revBits_inj : ∀ {k : ℕ} {a b : ℤ},
    (a - b).natAbs < 2 ^ k → revBits k a = revBits k b → a = b
  | 0, _, _, _, _ => by omega
  | k + 1, a, b, hab, he => by
    have := revBits_mod he.le; have := revBits_mod he.ge
    simp [revBits, show a % 2 = b % 2 by omega] at he
    have := revBits_inj (by rw [pow_succ'] at hab; omega) he; omega

private lemma revBits_no_ap : ∀ {k : ℕ} {a b c : ℤ}, a + c = 2 * b →
    revBits k a < revBits k b → revBits k b < revBits k c → False
  | 0, _, _, _, _, h, _ => Nat.lt_irrefl 0 h
  | k + 1, a, b, c, hap, hab, hbc => by
    have := revBits_mod hab.le; have := revBits_mod hbc.le
    simp [revBits, show a % 2 = c % 2 by omega, show b % 2 = c % 2 by omega] at hab hbc
    exact revBits_no_ap (by omega) hab hbc

private def sh (z : ℤ) : ℕ := Nat.clog 8 (z.natAbs + 1)

private lemma abs_lt_sh (z : ℤ) : z.natAbs < 8 ^ sh z := Nat.le_pow_clog (by decide) _

private def key (z : ℤ) : ℕ := 2 ^ (3 * sh z + 1) + revBits (3 * sh z + 1) z

private lemma key_lt {x y : ℤ} (h : sh x < sh y) : key x < key y := by
  have := revBits_lt (3 * sh x + 1) x
  have : 2 * 2 ^ (3 * sh x + 1) ≤ 2 ^ (3 * sh y + 1) :=
    pow_succ' 2 _ ▸ Nat.pow_le_pow_right (by decide) (by omega)
  simp only [key]; omega

private lemma sh_le {x y : ℤ} (h : key x ≤ key y) : sh x ≤ sh y :=
  le_of_not_gt fun hn => (key_lt hn).not_ge h

private lemma key_inj : Function.Injective key := by
  intro x y he
  have hs : sh x = sh y := le_antisymm (sh_le he.le) (sh_le he.ge)
  simp [key, hs] at he
  have : x.natAbs < 8 ^ sh y := hs ▸ abs_lt_sh x
  have := abs_lt_sh y
  have : 2 ^ (3 * sh y + 1) = 2 * 8 ^ sh y := by rw [pow_succ', pow_mul]; rfl
  exact revBits_inj (by omega) he

theorem OMA.solution : type_of% @Erdos195.erdos_195.variants.leq_5_bound := by
  let : Infinite (Set.range key) := (Set.infinite_range_of_injective key_inj).to_subtype
  let e := Nat.Subtype.orderIsoOfNat (Set.range key)
  let f : ℕ ≃ ℤ := e.toEquiv.trans (Equiv.ofInjective key key_inj).symm
  refine csSup_le' fun k hk => not_lt.mp fun h6 => ?_
  obtain ⟨l, ⟨a, d, hap⟩, hp⟩ := hk f
  obtain ⟨a, d, hl⟩ : ∃ a d : ℤ, l.map f = (List.range k).map fun n : ℕ => a + n • d := by
    rcases hap with h | h
    · exact ⟨a, d, h⟩
    · refine ⟨a + (k - 1 : ℕ) • d, -d, h.trans <| List.ext_getElem (by simp) fun i hi _ => ?_⟩
      simp at hi; simp [Nat.cast_sub (by omega : i ≤ k - 1)]; ring
  have hkeys : (l.map f).Pairwise (key · < key ·) :=
    List.pairwise_map.mpr (hp.imp fun h => by simpa [f, Equiv.apply_ofInjective_symm] using e.strictMono h)
  rw [hl, List.pairwise_iff_getElem] at hkeys
  let t (i : ℕ) : ℤ := a + i * d
  have hlt (i : ℕ) (hi : i < 5 := by omega) : key (t i) < key (t (i + 1)) := by
    simpa [t] using hkeys i (i + 1) (by simp; omega) (by simp; omega) (by omega)
  have same (i : ℕ) (hs : sh (t (i + 2)) ≤ sh (t i)) (hi : i < 4 := by omega) : False := by
    have h1 := hlt i; have h2 : key (t (i + 1)) < key (t (i + 2)) := hlt (i + 1)
    have := sh_le h1.le; have := sh_le h2.le
    simp [key, show sh (t i) = sh (t (i + 2)) by omega,
      show sh (t (i + 1)) = sh (t (i + 2)) by omega] at h1 h2
    exact revBits_no_ap (by dsimp [t]; ring) h1 h2
  have jump (m : ℕ) (hj : sh (t (m + 1)) < sh (t (m + 2))) (hm : m ≤ 1 := by omega) : False := by
    have h0 := sh_le (hlt m).le
    set j := sh (t (m + 2))
    have := (abs_lt_sh (t m)).trans_le (Nat.pow_le_pow_right (by decide) h0)
    have := abs_lt_sh (t (m + 1))
    have : 8 * 8 ^ sh (t (m + 1)) ≤ 8 ^ j := pow_succ' 8 _ ▸ Nat.pow_le_pow_right (by decide) hj
    have : t (m + 2 + 2) = 4 * t (m + 1) - 3 * t m := by dsimp [t]; ring
    exact same (m + 2) (Nat.clog_le_of_le_pow (y := j) (by omega))
  rcases (sh_le (hlt 1).le).lt_or_eq with h1 | h1
  · exact jump 0 h1
  · rcases (sh_le (hlt 2).le).lt_or_eq with h2 | h2
    · exact jump 1 h2
    · exact same 1 (h1.trans h2).ge
