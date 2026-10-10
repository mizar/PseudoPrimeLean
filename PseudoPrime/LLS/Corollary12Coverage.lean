/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.FiniteBitMasks
public import PseudoPrime.NumberTheory.PrimeResidueCoverage
public import PseudoPrime.LLS.Corollary12Certificates

/-!
# Bit-mask coverage certificates for Corollary 1.2

A list of certified primes is reduced modulo the modulus, with its integer cap
checked before each residue is inserted into a bit mask. Inclusion of the unit
residue mask supplies a bounded prime in each required class, without prime search.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Encode residues of candidate primes not exceeding the supplied integer cap.
Filter by the cap, reduce modulo the modulus, and take the union of their bits.
Primality is established separately when the resulting coverage is reflected. -/
def boundedPrimeResidueMask (q cap : ℕ) (ps : List ℕ) : ℕ :=
  NumberTheory.indicesMask ((ps.filter fun p ↦ p - cap == 0).map fun p ↦ p % q)

/-- Concatenating candidate lists unions their bounded residue masks.
Filtering and reduction modulo `q` preserve concatenation, and index masks combine
by bitwise union. This allows short coverage computations to be checked separately. -/
theorem boundedPrimeResidueMask_append (q cap : ℕ) (xs ys : List ℕ) :
    boundedPrimeResidueMask q cap (xs ++ ys) =
      boundedPrimeResidueMask q cap xs ||| boundedPrimeResidueMask q cap ys := by
  simp only [boundedPrimeResidueMask, List.filter_append, List.map_append,
    NumberTheory.indicesMask_append]

/-- A set residue bit in a certified prime list supplies a bounded prime witness.
Extract membership in the mapped and filtered list and use the supplied prime proofs.
This is the soundness step for the coverage certificate. -/
theorem boundedPrimeResidueMask_exists {q cap a : ℕ} {ps : List ℕ} (hPrime : ∀ p ∈ ps, p.Prime)
    (h : (boundedPrimeResidueMask q cap ps).testBit a = true) :
    ∃ p ∈ ps, p.Prime ∧ p % q = a ∧ p ≤ cap := by
  obtain ⟨p, hp, he⟩ := List.mem_map.mp (NumberTheory.indicesMask_testBit.mp h)
  have hc := List.mem_filter.mp hp
  refine ⟨p, hc.1, hPrime p hc.1, he, ?_⟩
  simpa only [beq_iff_eq, Nat.sub_eq_zero_iff_le] using hc.2

/-- Encode the representatives below the modulus that are coprime to it.
Pack their Boolean coprimality tests directly into successive bits, avoiding
an intermediate filtered list and repeated unions with large single-bit masks. -/
def unitResidueMask (q : ℕ) : ℕ :=
  NumberTheory.predicateMask (fun a ↦ a.gcd q == 1) 0 q

/-- Every coprime representative below the modulus has its unit-mask bit set.
The packed predicate's bit formula reduces the claim to its coprimality test.
This supplies the required bit when a coverage certificate is reflected. -/
theorem unitResidueMask_testBit {q a : ℕ} (ha : a < q) (hc : a.Coprime q) :
    (unitResidueMask q).testBit a = true := by
  rw [unitResidueMask, NumberTheory.predicateMask_testBit _ ha, Nat.zero_add]
  exact beq_iff_eq.mpr (Nat.coprime_iff_gcd_eq_one.mp hc)

/-- Check coverage of every unit residue by supplied primes at most `M`.
Primality is supplied separately; retaining the integer cap allows this coverage
to be transferred to divisors before their real upper bounds are applied. -/
def boundedPrimeResidueCoverageCheck (q M : ℕ) (ps : List ℕ) : Bool :=
  NumberTheory.maskIncludes (boundedPrimeResidueMask q M ps) (unitResidueMask q)

/-- A successful mask check on certified primes yields integer-bounded coverage.
For each unit, extract its covered bit and prime witness and identify its residue
using the injectivity of `ZMod.val`. The supplied cap is retained unchanged. -/
theorem boundedPrimeResidueCoverageCheck_sound {q M : ℕ} [NeZero q] {ps : List ℕ}
    (hPrime : ∀ p ∈ ps, p.Prime) (h : boundedPrimeResidueCoverageCheck q M ps = true) :
    NumberTheory.BoundedPrimeResidueCoverage q M := by
  intro a
  have hr := unitResidueMask_testBit (ZMod.val_lt (a : ZMod q)) (ZMod.val_coe_unit_coprime a)
  have hb := NumberTheory.maskIncludes_testBit h hr
  obtain ⟨p, _, hp, hm, hcap⟩ := boundedPrimeResidueMask_exists hPrime hb
  have ha : (p : ZMod q) = (a : ZMod q) := ZMod.val_injective q ((ZMod.val_natCast q p).trans hm)
  exact ⟨p, hp, ha, hcap⟩

/-- Integer-bounded coverage bounds the least prime when `M` is below the paper's bound.
Minimize the supplied prime witness and convert its natural-number inequality to
the real bound. This connects direct and transferred coverage to Corollary 1.2. -/
theorem exists_least_prime_in_residue_le_of_bounded_coverage {q M : ℕ} [NeZero q]
    (h : NumberTheory.BoundedPrimeResidueCoverage q M)
    (hM : (M : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2) (a : (ZMod q)ˣ) :
    ∃ p : ℕ,
      IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  obtain ⟨p, hp, ha, hcap⟩ := h a
  exact exists_least_prime_in_residue_le a ⟨p, hp, ha, (Nat.cast_le.mpr hcap).trans hM⟩

/-- Coverage modulo a multiple gives the least-prime bound modulo its divisor `q ≥ 4`.
Lift target units and project the prime witnesses with the same integer cap `M`.
The target condition `M ≤ residuePrimeCap q` supplies the real bound, so the source
coverage and its primality proofs can be shared among several target moduli. -/
theorem exists_least_prime_in_residue_le_of_divisor_coverage {q m M : ℕ} [NeZero q] [NeZero m]
    (hq : 4 ≤ q) (hd : q ∣ m) (h : NumberTheory.BoundedPrimeResidueCoverage m M)
    (hM : M ≤ residuePrimeCap q) (a : (ZMod q)ˣ) :
    ∃ p : ℕ,
      IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  exact
    exists_least_prime_in_residue_le_of_bounded_coverage (h.of_dvd hd)
      ((Nat.cast_le.mpr hM).trans (residuePrimeCap_le_totient_log_sq hq)) a

/-- Check that bounded candidate primes cover all unit residue classes.
The cap is the integer bound used for Corollary 1.2. Primality proofs for the candidate
list are supplied separately, allowing them to be shared across many moduli. -/
def residuePrimeCoverageCheck (q : ℕ) (ps : List ℕ) : Bool :=
  NumberTheory.maskIncludes (boundedPrimeResidueMask q (residuePrimeCap q) ps) (unitResidueMask q)

/-- A successful coverage check on certified primes bounds the least prime
in every unit residue class of a nonzero modulus at least four.
Extract its covered bit and a bounded prime witness, identify the residue in ZMod,
then minimize the prime set and convert the integer cap to the paper's real bound.
This proves the same bounded-modulus conclusion as progression certificates. -/
theorem exists_least_prime_in_residue_le_of_coverage {q : ℕ} [NeZero q] {ps : List ℕ} (hq : 4 ≤ q)
    (hPrime : ∀ p ∈ ps, p.Prime) (h : residuePrimeCoverageCheck q ps = true) (a : (ZMod q)ˣ) :
    ∃ p : ℕ,
      IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  exact
    exists_least_prime_in_residue_le_of_bounded_coverage
      (boundedPrimeResidueCoverageCheck_sound hPrime h) (residuePrimeCap_le_totient_log_sq hq) a

/-- Check residue coverage for every modulus in a finite consecutive interval.
The same certified prime list is shared by all moduli. Each individual mask checks
its own integer cap and required unit residues before the interval is reflected. -/
def residuePrimeCoverageRangeCheck (s w : ℕ) (ps : List ℕ) : Bool :=
  (List.range w).all fun k ↦ residuePrimeCoverageCheck (s + k) ps

/-- A checked coverage interval on certified primes gives the least-prime bound
for every modulus in that interval that is at least four.
Select the offset of the queried modulus, extract its finite check, and apply
the single-modulus coverage theorem. This connects generated interval checks
to the bounded part of Corollary 1.2 without progression search. -/
theorem exists_least_prime_in_residue_le_of_coverage_range {q s w : ℕ} [NeZero q] {ps : List ℕ}
    (hPrime : ∀ p ∈ ps, p.Prime) (h : residuePrimeCoverageRangeCheck s w ps = true) (hq : 4 ≤ q)
    (hs : s ≤ q) (hb : q < s + w) (a : (ZMod q)ˣ) :
    ∃ p : ℕ,
      IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  have hk : q - s < w := Nat.sub_lt_left_of_lt_add hs hb
  have hc := List.all_eq_true.mp h (q - s) (List.mem_range.mpr hk)
  rw [Nat.add_sub_of_le hs] at hc
  exact exists_least_prime_in_residue_le_of_coverage hq hPrime hc a

end PseudoPrime.LLS.PaperStatements
