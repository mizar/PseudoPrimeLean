/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.SmallestPrimeFactorTable
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite checks for supplied smallest-prime-factor tables

Check divisibility at each index and upper bounds along candidate prime multiples.
The soundness theorem produces the shared smallest-prime-factor certificate.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Check that every table entry from two through the bound is an actual divisor
at least two. This local arithmetic check supplies the first two certificate fields. -/
def smallestPrimeFactorDivisorCheck (bound : ℕ) (factor : ℕ → ℕ) : Bool :=
  @decide (∀ n ∈ Finset.Icc 2 bound, 2 ≤ factor n ∧ factor n ∣ n) Finset.decidableDforallFinset

/-- Check the multiples of every diagonal candidate up to sqrt bound.
For candidate p, visit indices p*k with p at most k at most bound/p and require
the stored factor to be at most p. This avoids testing all pairs of integers. -/
def smallestPrimeFactorMultiplesCheck (bound : ℕ) (factor : ℕ → ℕ) : Bool :=
  decide
    (∀ p ∈ Finset.Icc 2 (Nat.sqrt bound),
      factor p = p → ∀ k ∈ Finset.Icc p (bound / p), factor (p * k) ≤ p)

/-- A passing divisor check supplies a nontrivial divisor at every certified index.
Reflect the bounded Boolean decision and use interval membership.
These facts give the divisor fields of the table certificate. -/
theorem smallestPrimeFactorDivisorCheck_sound {bound : ℕ} {factor : ℕ → ℕ}
    (h : smallestPrimeFactorDivisorCheck bound factor = true) :
    ∀ n, 2 ≤ n → n ≤ bound → 2 ≤ factor n ∧ factor n ∣ n := by
  let : Decidable (∀ n ∈ Finset.Icc 2 bound, 2 ≤ factor n ∧ factor n ∣ n) :=
    Finset.decidableDforallFinset
  have hc : ∀ n ∈ Finset.Icc 2 bound, 2 ≤ factor n ∧ factor n ∣ n := of_decide_eq_true h
  intro n hn hb
  exact hc n (Finset.mem_Icc.mpr ⟨hn, hb⟩)

/-- A passing multiples check bounds every candidate's multiples from its square.
The square bound places the candidate below sqrt bound; divisibility identifies
the multiple with p*(n/p). This supplies the global multiples certificate field. -/
theorem smallestPrimeFactorMultiplesCheck_sound {bound : ℕ} {factor : ℕ → ℕ}
    (h : smallestPrimeFactorMultiplesCheck bound factor = true) {p n : ℕ} (hp : 2 ≤ p)
    (hsq : p ^ 2 ≤ n) (hb : n ≤ bound) (hdiag : factor p = p) (hdvd : p ∣ n) : factor n ≤ p := by
  have hcheck :
    ∀ p ∈ Finset.Icc 2 (Nat.sqrt bound),
      factor p = p → ∀ k ∈ Finset.Icc p (bound / p), factor (p * k) ≤ p :=
    of_decide_eq_true h
  have hps : p ≤ Nat.sqrt bound := Nat.le_sqrt.mpr (by simpa only [pow_two] using hsq.trans hb)
  have hp0 : 0 < p := Nat.zero_lt_two.trans_le hp
  have hklo : p ≤ n / p := (Nat.le_div_iff_mul_le hp0).mpr (by simpa only [pow_two] using hsq)
  have hkhi : n / p ≤ bound / p := Nat.div_le_div_right hb
  have hm := hcheck p (Finset.mem_Icc.mpr ⟨hp, hps⟩) hdiag (n / p) (Finset.mem_Icc.mpr ⟨hklo, hkhi⟩)
  rw [Nat.mul_div_cancel' hdvd] at hm
  exact hm

/-- Check a supplied smallest-prime-factor table by combining divisor checks
with the diagonal candidates' multiples checks. Successful data yield a shared
certificate for prime membership throughout the finite interval. -/
def smallestPrimeFactorTableCheck (bound : ℕ) (factor : ℕ → ℕ) : Bool :=
  smallestPrimeFactorDivisorCheck bound factor && smallestPrimeFactorMultiplesCheck bound factor

/-- A successful combined table check gives a smallest-prime-factor certificate.
Reflect both Boolean components and assemble their divisor and multiples fields.
The certificate then identifies all table entries with Nat.minFac. -/
theorem smallestPrimeFactorTableCheck_sound {bound : ℕ} {factor : ℕ → ℕ}
    (h : smallestPrimeFactorTableCheck bound factor = true) :
    SmallestPrimeFactorTableCertificate bound factor := by
  have hc := Bool.and_eq_true_iff.mp h
  have hf := smallestPrimeFactorDivisorCheck_sound hc.1
  exact
    ⟨fun n hn hb ↦ (hf n hn hb).1, fun n hn hb ↦ (hf n hn hb).2, fun _ _ hp hs hb hd hv ↦
      smallestPrimeFactorMultiplesCheck_sound hc.2 hp hs hb hd hv⟩

/-- Check a selected list of primes by table membership, without trial division.
Each entry must lie in the certified interval and equal its stored factor.
The table certificate supplies the mathematical primality proof separately. -/
def smallestPrimeFactorPrimeListCheck (bound : ℕ) (factor : ℕ → ℕ) (ps : List ℕ) : Bool :=
  ps.all fun p ↦ decide (2 ≤ p ∧ p ≤ bound ∧ factor p = p)

/-- A selected list passing the membership check consists entirely of primes.
Reflect its interval and diagonal conditions and apply the certified table's
prime characterization. This shares the table proof across residue witnesses. -/
theorem smallestPrimeFactorPrimeListCheck_sound {bound : ℕ} {factor : ℕ → ℕ} {ps : List ℕ}
    (ht : SmallestPrimeFactorTableCertificate bound factor)
    (hc : smallestPrimeFactorPrimeListCheck bound factor ps = true) : ∀ p ∈ ps, p.Prime := by
  intro p hp
  have hb : 2 ≤ p ∧ p ≤ bound ∧ factor p = p := of_decide_eq_true ((List.all_eq_true.mp hc) p hp)
  exact (ht.prime_iff_factor_eq_self hb.1 hb.2.1).mpr hb.2.2

end PseudoPrime.NumberTheory
