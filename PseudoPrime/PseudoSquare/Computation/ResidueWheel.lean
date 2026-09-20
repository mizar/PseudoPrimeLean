import PseudoPrime.NumberTheory.Jacobi.Prime
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.LegendreSymbol

/-! # Residue interfaces for kernel-checked Jacobi wheels -/

namespace PseudoPrime.PseudoSquare

/-- The Jacobi value at a natural numerator depends only on its residue modulo the denominator. -/
theorem jacobiSym_nat_mod_left' {a b p : ℕ} (h : a % p = b % p) :
    jacobiSym a p = jacobiSym b p := by
  apply jacobiSym.mod_left'
  exact_mod_cast h

/-- The stage predicate of the finite Q-ne-one sieve. -/
def QNeOneSievePasses (primes : Finset ℕ) (n : ℕ) : Prop :=
  ∀ p ∈ primes, jacobiSym n p = 1

/-- A residue-preserving change of numerator preserves every stage of the sieve. -/
theorem qNeOneSievePasses_of_mod_eq {primes : Finset ℕ} {a b : ℕ}
    (hres : ∀ p ∈ primes, a % p = b % p) (ha : QNeOneSievePasses primes a) :
    QNeOneSievePasses primes b := by
  intro p hp
  rw [← jacobiSym_nat_mod_left' (hres p hp)]
  exact ha p hp

/-- The finite candidate set surviving all Jacobi-equal-to-one sieve stages below `B`. -/
noncomputable def qNeOneSieve (primes : Finset ℕ) (B : ℕ) : Finset ℕ := by
  classical exact (Finset.range B).filter (QNeOneSievePasses primes)

/-- Membership in the finite sieve is exactly boundedness plus passing every stage. -/
theorem mem_qNeOneSieve_iff {primes : Finset ℕ} {B n : ℕ} :
    n ∈ qNeOneSieve primes B ↔ n < B ∧ QNeOneSievePasses primes n := by
  classical simp only [qNeOneSieve, Finset.mem_filter, Finset.mem_range]

/-- A number outside the sieve has a concrete prime stage with Jacobi value different from one. -/
theorem exists_ne_one_of_not_mem_qNeOneSieve {primes : Finset ℕ} {B n : ℕ} (hnB : n < B)
    (hnot : n ∉ qNeOneSieve primes B) : ∃ p ∈ primes, jacobiSym n p ≠ 1 := by
  by_contra h
  push Not at h
  have hpass : QNeOneSievePasses primes n := by
    intro p hp
    exact h p hp
  exact hnot (mem_qNeOneSieve_iff.mpr ⟨hnB, hpass⟩)

/-- A non-one sieve witness becomes a negative Jacobi witness when no candidate divides `n`. -/
theorem exists_neg_one_of_not_mem_qNeOneSieve_of_not_dvd {primes : Finset ℕ} {B n : ℕ} (hnB : n < B)
    (hnot : n ∉ qNeOneSieve primes B) (hndvd : ∀ p ∈ primes, ¬p ∣ n)
    (hprime : ∀ p ∈ primes, p.Prime) : ∃ p ∈ primes, jacobiSym n p = -1 := by
  obtain ⟨p, hp, hne⟩ := exists_ne_one_of_not_mem_qNeOneSieve hnB hnot
  refine ⟨p, hp, ?_⟩
  exact NumberTheory.jacobi_eq_neg_one_of_prime_of_not_dvd_of_ne_one (hprime p hp) (hndvd p hp) hne

/-- If no candidate has Jacobi value `-1`, coprimality forces every sieve stage to be `1`. -/
theorem qNeOneSievePasses_of_not_neg_one_of_not_dvd {primes : Finset ℕ} {n : ℕ}
    (hndvd : ∀ p ∈ primes, ¬p ∣ n) (hprime : ∀ p ∈ primes, p.Prime)
    (hneg : ∀ p ∈ primes, jacobiSym n p ≠ -1) : QNeOneSievePasses primes n := by
  intro p hp
  have hcop : Nat.Coprime p n := (hprime p hp).coprime_iff_not_dvd.mpr (hndvd p hp)
  have hgcd : (n : ℤ).gcd p = 1 := by exact_mod_cast hcop.symm.gcd_eq_one
  rcases jacobiSym.eq_one_or_neg_one hgcd with hone | hminus
  · exact hone
  · exact False.elim ((hneg p hp) hminus)

/-- A Jacobi value of one at 3 restricts the numerator to a nonzero square residue. -/
theorem qNeOne_residues_3 {n : ℕ} (h : jacobiSym n 3 = 1) : n % 3 = 1 := by
  have hj : jacobiSym ((n % 3 : ℕ) : ℤ) 3 = 1 := by
    rw [jacobiSym_nat_mod_left' (Nat.mod_mod n 3)]
    exact h
  have hb := Nat.mod_lt n (by decide : 0 < 3)
  interval_cases n % 3 <;> norm_num only [true_or, false_or, or_false] at *

/-- A Jacobi value of one at 5 restricts the numerator to a nonzero square residue. -/
theorem qNeOne_residues_5 {n : ℕ} (h : jacobiSym n 5 = 1) : n % 5 = 1 ∨ n % 5 = 4 := by
  have hj : jacobiSym ((n % 5 : ℕ) : ℤ) 5 = 1 := by
    rw [jacobiSym_nat_mod_left' (Nat.mod_mod n 5)]
    exact h
  have hb := Nat.mod_lt n (by decide : 0 < 5)
  interval_cases n % 5 <;> norm_num only [true_or, false_or, or_false] at *

/-- A Jacobi value of one at 7 restricts the numerator to a nonzero square residue. -/
theorem qNeOne_residues_7 {n : ℕ} (h : jacobiSym n 7 = 1) : n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 4 := by
  have hj : jacobiSym ((n % 7 : ℕ) : ℤ) 7 = 1 := by
    rw [jacobiSym_nat_mod_left' (Nat.mod_mod n 7)]
    exact h
  have hb := Nat.mod_lt n (by decide : 0 < 7)
  interval_cases n % 7 <;> norm_num only [true_or, false_or, or_false] at *

/-- A Jacobi value of one at 11 restricts the numerator to a nonzero square residue. -/
theorem qNeOne_residues_11 {n : ℕ} (h : jacobiSym n 11 = 1) :
    n % 11 = 1 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 9 := by
  have hj : jacobiSym ((n % 11 : ℕ) : ℤ) 11 = 1 := by
    rw [jacobiSym_nat_mod_left' (Nat.mod_mod n 11)]
    exact h
  have hb := Nat.mod_lt n (by decide : 0 < 11)
  interval_cases n % 11 <;> norm_num only [true_or, false_or, or_false] at *

/-- A Jacobi value of one at 13 restricts the numerator to a nonzero square residue. -/
theorem qNeOne_residues_13 {n : ℕ} (h : jacobiSym n 13 = 1) :
    n % 13 = 1 ∨ n % 13 = 3 ∨ n % 13 = 4 ∨ n % 13 = 9 ∨ n % 13 = 10 ∨ n % 13 = 12 := by
  have hj : jacobiSym ((n % 13 : ℕ) : ℤ) 13 = 1 := by
    rw [jacobiSym_nat_mod_left' (Nat.mod_mod n 13)]
    exact h
  have hb := Nat.mod_lt n (by decide : 0 < 13)
  interval_cases n % 13 <;> norm_num only [true_or, false_or, or_false] at *

/-- A Jacobi value of one at 17 restricts the numerator to a nonzero square residue. -/
theorem qNeOne_residues_17 {n : ℕ} (h : jacobiSym n 17 = 1) :
    n % 17 = 1 ∨
      n % 17 = 2 ∨
      n % 17 = 4 ∨ n % 17 = 8 ∨ n % 17 = 9 ∨ n % 17 = 13 ∨ n % 17 = 15 ∨ n % 17 = 16 := by
  have hj : jacobiSym ((n % 17 : ℕ) : ℤ) 17 = 1 := by
    rw [jacobiSym_nat_mod_left' (Nat.mod_mod n 17)]
    exact h
  have hb := Nat.mod_lt n (by decide : 0 < 17)
  interval_cases n % 17 <;> norm_num only [true_or, false_or, or_false] at *

/-- A certified rejecting residue contradicts a passing stage, for every numerator in that class. -/
theorem qNeOne_reject_residue {n p r : ℕ} (hr : n % p = r % p) (hbad : jacobiSym (r : ℤ) p ≠ 1)
    (hpass : jacobiSym n p = 1) : False := by
  exact hbad ((jacobiSym_nat_mod_left' hr).symm.trans hpass)

/-- Combine two certified residues at coprime moduli; CRT is proved once, not searched per node. -/
theorem qNeOne_crt {n M p r a b : ℕ} (hco : M.Coprime p) (hM : n % M = r) (hp : n % p = a)
    (hbM : b % M = r) (hbp : b % p = a) (hb : b < M * p) : n % (M * p) = b := by
  have h₁ : Nat.ModEq M n b := hM.trans hbM.symm
  have h₂ : Nat.ModEq p n b := hp.trans hbp.symm
  have h := (Nat.modEq_and_modEq_iff_modEq_mul hco).mp ⟨h₁, h₂⟩
  exact (show n % (M * p) = b % (M * p) from h).trans (Nat.mod_eq_of_lt hb)

/-- A progression below twice its modulus has at most two representatives. -/
theorem qNeOne_two_lifts {n M r : ℕ} (hn : n < 2 * M) (hr : n % M = r) : n = r ∨ n = r + M := by
  by_cases h : n < M
  · exact Or.inl ((Nat.mod_eq_of_lt h).symm.trans hr)
  · rw [Nat.mod_eq_sub_mod (by omega : M ≤ n), Nat.mod_eq_of_lt (by omega : n - M < M)] at hr
    exact Or.inr (by omega)

/-- A progression below its second representative has only its initial representative. -/
theorem qNeOne_unique_lift {n M r : ℕ} (hn : n < r + M) (hr : n % M = r) : n = r := by
  by_cases h : n < M
  · exact (Nat.mod_eq_of_lt h).symm.trans hr
  · have hle := Nat.mod_le (n - M) M
    rw [← Nat.mod_eq_sub_mod (by omega : M ≤ n)] at hle
    omega

/-- A residue at or above the cutoff cannot represent a smaller natural number. -/
theorem qNeOne_impossible_lift {n M r B : ℕ} (hn : n < B) (hrB : B ≤ r) (hr : n % M = r) :
    False := by
  have hle := Nat.mod_le n M
  omega

end PseudoPrime.PseudoSquare
