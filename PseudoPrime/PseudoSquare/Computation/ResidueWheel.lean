/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Jacobi.Prime
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.LegendreSymbol

/-! # Residue interfaces for kernel-checked Jacobi wheels -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/--
For naturals `a`, `b`, and `p`, equal residues `a % p = b % p` imply equal Jacobi
symbols. No primality or positivity of `p` is assumed. The proof casts the equality
to integers and applies Jacobi periodicity. This transports residue certificates to inputs.
-/
theorem jacobiSym_nat_mod_left' {a b p : ℕ} (h : a % p = b % p) :
    jacobiSym a p = jacobiSym b p := by
  apply jacobiSym.mod_left'
  exact_mod_cast h

/--
The proposition that every denominator `p` in the finite stage set `primes` satisfies
`jacobiSym n p = 1`. The definition imposes no primality on the set members.
Finite CRT certificates use this predicate to prove that odd nonsquares must fail a stage.
-/
def QNeOneSievePasses (primes : Finset ℕ) (n : ℕ) : Prop :=
  ∀ p ∈ primes, jacobiSym n p = 1

/--
Equal residues of `a` and `b` at every listed denominator transfer all passing stages
from `a` to `b`. The proof rewrites each Jacobi symbol by residue invariance and reuses
the corresponding equality. This permits sieving with residue representatives.
-/
theorem qNeOneSievePasses_of_mod_eq {primes : Finset ℕ} {a b : ℕ}
    (hres : ∀ p ∈ primes, a % p = b % p) (ha : QNeOneSievePasses primes a) :
    QNeOneSievePasses primes b := by
  intro p hp
  rw [← jacobiSym_nat_mod_left' (hres p hp)]
  exact ha p hp

/--
The finite set of `n < B` passing all stages in `primes`, obtained by filtering
`Finset.range B` with `QNeOneSievePasses`. It imposes neither oddness nor nonsquareness.
The membership and rejection interfaces use this candidate set.
-/
noncomputable def qNeOneSieve (primes : Finset ℕ) (B : ℕ) : Finset ℕ := by
  classical exact (Finset.range B).filter (QNeOneSievePasses primes)

/--
Membership in `qNeOneSieve primes B` is equivalent to `n < B` and passing every stage.
The proof unfolds filtering and range membership. This separates the finite cutoff
from the Jacobi equalities in subsequent rejection adapters.
-/
theorem mem_qNeOneSieve_iff {primes : Finset ℕ} {B n : ℕ} :
    n ∈ qNeOneSieve primes B ↔ n < B ∧ QNeOneSievePasses primes n := by
  classical simp only [qNeOneSieve, Finset.mem_filter, Finset.mem_range]

/--
If `n < B` but `n` is outside the sieve, some listed denominator `p` satisfies
`jacobiSym n p ≠ 1`. No primality is assumed. The proof argues that equality at every
stage would give sieve membership. Further assumptions refine this to a `-1` witness.
-/
theorem exists_ne_one_of_not_mem_qNeOneSieve {primes : Finset ℕ} {B n : ℕ} (hnB : n < B)
    (hnot : n ∉ qNeOneSieve primes B) : ∃ p ∈ primes, jacobiSym n p ≠ 1 := by
  by_contra h
  push Not at h
  have hpass : QNeOneSievePasses primes n := by
    intro p hp
    exact h p hp
  exact hnot (mem_qNeOneSieve_iff.mpr ⟨hnB, hpass⟩)

/--
If `n < B` is outside the sieve, every listed denominator is prime, and none divides
`n`, some listed stage has Jacobi value `-1`. The proof extracts a non-one stage and
uses primality and nondivisibility to exclude zero. This refines rejection to a negative
witness when all candidates are coprime.
-/
theorem exists_neg_one_of_not_mem_qNeOneSieve_of_not_dvd {primes : Finset ℕ} {B n : ℕ} (hnB : n < B)
    (hnot : n ∉ qNeOneSieve primes B) (hndvd : ∀ p ∈ primes, ¬p ∣ n)
    (hprime : ∀ p ∈ primes, p.Prime) : ∃ p ∈ primes, jacobiSym n p = -1 := by
  obtain ⟨p, hp, hne⟩ := exists_ne_one_of_not_mem_qNeOneSieve hnB hnot
  refine ⟨p, hp, ?_⟩
  exact NumberTheory.jacobi_eq_neg_one_of_prime_of_not_dvd_of_ne_one (hprime p hp) (hndvd p hp) hne

/--
If all listed stages are prime, none divides `n`, and none has Jacobi value `-1`,
then all stages pass. The proof derives coprimality and restricts each Jacobi value
to `1` or `-1`, excluding the latter. This converts absence of negative witnesses
to the all-passing predicate.
-/
theorem qNeOneSievePasses_of_not_neg_one_of_not_dvd {primes : Finset ℕ} {n : ℕ}
    (hndvd : ∀ p ∈ primes, ¬p ∣ n) (hprime : ∀ p ∈ primes, p.Prime)
    (hneg : ∀ p ∈ primes, jacobiSym n p ≠ -1) : QNeOneSievePasses primes n := by
  intro p hp
  have hcop : Nat.Coprime p n := (hprime p hp).coprime_iff_not_dvd.mpr (hndvd p hp)
  have hgcd : (n : ℤ).gcd p = 1 := by exact_mod_cast hcop.symm.gcd_eq_one
  rcases jacobiSym.eq_one_or_neg_one hgcd with hone | hminus
  · exact hone
  · exact False.elim ((hneg p hp) hminus)

/--
If `jacobiSym n 3 = 1`, then `n % 3` is one of the nonzero square residues
`1`. The proof transports the symbol to the remainder, bounds that remainder
by `3`, and enumerates all cases with Jacobi normalization.
This supplies the possible passing residues at the corresponding CRT wheel stage.
-/
theorem qNeOne_residues_3 {n : ℕ} (h : jacobiSym n 3 = 1) : n % 3 = 1 := by
  have hj : jacobiSym ((n % 3 : ℕ) : ℤ) 3 = 1 := by
    rw [jacobiSym_nat_mod_left' (Nat.mod_mod n 3)]
    exact h
  have hb := Nat.mod_lt n (by decide : 0 < 3)
  interval_cases n % 3 <;> norm_num only [true_or, false_or, or_false] at *

/--
If `jacobiSym n 5 = 1`, then `n % 5` is one of the nonzero square residues
`1, 4`. The proof transports the symbol to the remainder, bounds that remainder
by `5`, and enumerates all cases with Jacobi normalization.
This supplies the possible passing residues at the corresponding CRT wheel stage.
-/
theorem qNeOne_residues_5 {n : ℕ} (h : jacobiSym n 5 = 1) : n % 5 = 1 ∨ n % 5 = 4 := by
  have hj : jacobiSym ((n % 5 : ℕ) : ℤ) 5 = 1 := by
    rw [jacobiSym_nat_mod_left' (Nat.mod_mod n 5)]
    exact h
  have hb := Nat.mod_lt n (by decide : 0 < 5)
  interval_cases n % 5 <;> norm_num only [true_or, false_or, or_false] at *

/--
If `jacobiSym n 7 = 1`, then `n % 7` is one of the nonzero square residues
`1, 2, 4`. The proof transports the symbol to the remainder, bounds that remainder
by `7`, and enumerates all cases with Jacobi normalization.
This supplies the possible passing residues at the corresponding CRT wheel stage.
-/
theorem qNeOne_residues_7 {n : ℕ} (h : jacobiSym n 7 = 1) : n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 4 := by
  have hj : jacobiSym ((n % 7 : ℕ) : ℤ) 7 = 1 := by
    rw [jacobiSym_nat_mod_left' (Nat.mod_mod n 7)]
    exact h
  have hb := Nat.mod_lt n (by decide : 0 < 7)
  interval_cases n % 7 <;> norm_num only [true_or, false_or, or_false] at *

/--
If `jacobiSym n 11 = 1`, then `n % 11` is one of the nonzero square residues
`1, 3, 4, 5, 9`. The proof transports the symbol to the remainder, bounds that remainder
by `11`, and enumerates all cases with Jacobi normalization.
This supplies the possible passing residues at the corresponding CRT wheel stage.
-/
theorem qNeOne_residues_11 {n : ℕ} (h : jacobiSym n 11 = 1) :
    n % 11 = 1 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 9 := by
  have hj : jacobiSym ((n % 11 : ℕ) : ℤ) 11 = 1 := by
    rw [jacobiSym_nat_mod_left' (Nat.mod_mod n 11)]
    exact h
  have hb := Nat.mod_lt n (by decide : 0 < 11)
  interval_cases n % 11 <;> norm_num only [true_or, false_or, or_false] at *

/--
If `jacobiSym n 13 = 1`, then `n % 13` is one of the nonzero square residues
`1, 3, 4, 9, 10, 12`. The proof transports the symbol to the remainder, bounds that remainder
by `13`, and enumerates all cases with Jacobi normalization.
This supplies the possible passing residues at the corresponding CRT wheel stage.
-/
theorem qNeOne_residues_13 {n : ℕ} (h : jacobiSym n 13 = 1) :
    n % 13 = 1 ∨ n % 13 = 3 ∨ n % 13 = 4 ∨ n % 13 = 9 ∨ n % 13 = 10 ∨ n % 13 = 12 := by
  have hj : jacobiSym ((n % 13 : ℕ) : ℤ) 13 = 1 := by
    rw [jacobiSym_nat_mod_left' (Nat.mod_mod n 13)]
    exact h
  have hb := Nat.mod_lt n (by decide : 0 < 13)
  interval_cases n % 13 <;> norm_num only [true_or, false_or, or_false] at *

/--
If `jacobiSym n 17 = 1`, then `n % 17` is one of the nonzero square residues
`1, 2, 4, 8, 9, 13, 15, 16`. The proof transports the symbol to the remainder, bounds that remainder
by `17`, and enumerates all cases with Jacobi normalization.
This supplies the possible passing residues at the corresponding CRT wheel stage.
-/
theorem qNeOne_residues_17 {n : ℕ} (h : jacobiSym n 17 = 1) :
    n % 17 = 1 ∨
      n % 17 = 2 ∨
      n % 17 = 4 ∨ n % 17 = 8 ∨ n % 17 = 9 ∨ n % 17 = 13 ∨ n % 17 = 15 ∨ n % 17 = 16 := by
  have hj : jacobiSym ((n % 17 : ℕ) : ℤ) 17 = 1 := by
    rw [jacobiSym_nat_mod_left' (Nat.mod_mod n 17)]
    exact h
  have hb := Nat.mod_lt n (by decide : 0 < 17)
  interval_cases n % 17 <;> norm_num only [true_or, false_or, or_false] at *

/--
Equal residues `n % p = r % p` and a certified value `jacobiSym r p ≠ 1` contradict
`jacobiSym n p = 1`. Jacobi periodicity transports the passing equality to the residue.
No primality or cutoff is needed. This closes generated rejecting-residue leaves.
-/
theorem qNeOne_reject_residue {n p r : ℕ} (hr : n % p = r % p) (hbad : jacobiSym (r : ℤ) p ≠ 1)
    (hpass : jacobiSym n p = 1) : False := by
  exact hbad ((jacobiSym_nat_mod_left' hr).symm.trans hpass)

/--
For coprime `M` and `p`, equal residues of `n` and a certified `b` at both moduli,
together with `b < M * p`, imply `n % (M * p) = b`. The proof combines modular
equalities using CRT and reduces `b` by its size bound. This connects wheel nodes to children.
-/
theorem qNeOne_crt {n M p r a b : ℕ} (hco : M.Coprime p) (hM : n % M = r) (hp : n % p = a)
    (hbM : b % M = r) (hbp : b % p = a) (hb : b < M * p) : n % (M * p) = b := by
  have h₁ : Nat.ModEq M n b := hM.trans hbM.symm
  have h₂ : Nat.ModEq p n b := hp.trans hbp.symm
  have h := (Nat.modEq_and_modEq_iff_modEq_mul hco).mp ⟨h₁, h₂⟩
  exact (show n % (M * p) = b % (M * p) from h).trans (Nat.mod_eq_of_lt hb)

/--
If `n < 2 * M` and `n % M = r`, then `n = r` or `n = r + M`. Below `M`,
remainder reduction gives the first case; otherwise subtracting `M` leaves a value below
`M` and gives the second. This reduces terminal classes to at most two concrete inputs.
-/
theorem qNeOne_two_lifts {n M r : ℕ} (hn : n < 2 * M) (hr : n % M = r) : n = r ∨ n = r + M := by
  by_cases h : n < M
  · exact Or.inl ((Nat.mod_eq_of_lt h).symm.trans hr)
  · have hle : M ≤ n := Nat.le_of_not_gt h
    have hsum : M + (n - M) = n := Nat.add_sub_of_le hle
    have hsublt : n - M < M := by
      have hlt : M + (n - M) < M + M := by
        calc
          M + (n - M) = n := hsum
          _ < 2 * M := hn
          _ = M + M := two_mul M
      exact (Nat.add_lt_add_iff_left).mp hlt
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hsublt] at hr
    right
    calc
      n = M + (n - M) := hsum.symm
      _ = M + r := by rw [hr]
      _ = r + M := Nat.add_comm _ _

/--
If `n < r + M` and `n % M = r`, then `n = r`. Below `M`, the remainder is the
input; otherwise subtracting `M` and using the remainder inequality forces `r + M ≤ n`,
a contradiction. This reduces terminal classes to their sole possible representative.
-/
theorem qNeOne_unique_lift {n M r : ℕ} (hn : n < r + M) (hr : n % M = r) : n = r := by
  by_cases h : n < M
  · exact (Nat.mod_eq_of_lt h).symm.trans hr
  · have hbase : M ≤ n := Nat.le_of_not_gt h
    have hsum : n - M + M = n := Nat.sub_add_cancel hbase
    have hmodle : (n - M) % M ≤ n - M := Nat.mod_le (n - M) M
    rw [← Nat.mod_eq_sub_mod hbase] at hmodle
    rw [hr] at hmodle
    have hge : r + M ≤ n :=
      calc
        r + M ≤ (n - M) + M := Nat.add_le_add_right hmodle M
        _ = n := hsum
    exact False.elim ((Nat.not_lt_of_ge hge) hn)

/--
If `n < B`, `B ≤ r`, and `n % M = r`, derive `False`. Since the remainder is
at most `n`, the residue equality would give `B ≤ n`. This excludes CRT classes whose
initial representative is already at or above the cutoff.
-/
theorem qNeOne_impossible_lift {n M r B : ℕ} (hn : n < B) (hrB : B ≤ r) (hr : n % M = r) :
    False := by
  have hle := Nat.mod_le n M
  have hge : B ≤ n :=
    calc
      B ≤ r := hrB
      _ = n % M := hr.symm
      _ ≤ n := hle
  exact (Nat.not_lt_of_ge hge) hn

end PseudoPrime.PseudoSquare
