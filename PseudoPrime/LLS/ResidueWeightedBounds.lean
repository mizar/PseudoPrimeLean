/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ResiduePrimePowerComparison
public import PseudoPrime.LLS.OddPrimePowerBounds
public import PseudoPrime.LLS.CosetWeightedComparison
public import PseudoPrime.LLS.CosetNormAverage
public import PseudoPrime.NumberTheory.TotientLowerBounds
public import PseudoPrime.NumberTheory.PrimeFactorPowerBounds

/-!
# Upper bound for a prime-free arithmetic progression

Combine the square-congruence count with the RH bound for odd composite prime powers.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open Classical in
/-- Under RH and `x > 1`, a strict weighted gap bounds the least prime in a unit class.
The inputs separately bound its prime-free Mangoldt sum and the nonprincipal character norms.
Character orthogonality contradicts the gap if the least prime exceeds `x`.
Keeping these upper bounds as parameters allows sharper square and parity estimates
without imposing the cutoff assumptions of a particular numerical majorant. -/
theorem exists_least_prime_in_residue_le_of_weighted_gap {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hRH : RiemannHypothesis) {x U N : ℝ} (hx : 1 < x)
    (hu :
      (∀ p : ℕ, p.Prime → (p : ZMod q) = (a : ZMod q) → ¬(p : ℝ) ≤ x) →
        (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) = (a : ZMod q)),
            AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n) ≤
          U)
    (hn :
      (∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator (⊥ : Subgroup (ZMod q)ˣ)),
          ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.val‖) ≤
        N)
    (hgap : (q.totient : ℝ) * U + N < cosetPrincipalLower q x) :
    ∃ p : ℕ, IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧ (p : ℝ) ≤ x := by
  obtain ⟨p, hp⟩ := exists_least_prime_in_residue a
  refine ⟨p, hp, ?_⟩
  by_contra hpx
  have hno : ∀ r : ℕ, r.Prime → (r : ZMod q) = (a : ZMod q) → ¬(r : ℝ) ≤ x := by
    intro r hr hra hrx
    exact hpx ((Nat.cast_le.mpr (hp.2 ⟨hr, hra⟩)).trans hrx)
  have hi : (⊥ : Subgroup (ZMod q)ˣ).index = q.totient := by
    rw [Subgroup.index_bot, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have ha := principal_logWeightedSum_le_coset_add_nonprincipal_norms (⊥ : Subgroup (ZMod q)ˣ) a x
  rw [cosetLogWeightedSum_bot_eq, hi] at ha
  have hm := mul_le_mul_of_nonneg_left (hu hno) (Nat.cast_nonneg q.totient : (0 : ℝ) ≤ _)
  exact (not_lt_of_ge ((cosetPrincipalLower_le hRH hx).trans (ha.trans (add_le_add hm hn)))) hgap

/-- Under RH, a prime-free unit residue class has its logarithmic sum bounded by
the square majorant and the odd root sum retaining the zeta corrections.
Separate square and nonsquare prime powers, then apply the corrected odd-power bound.
This connects the retained negative terms to the residue-class contradiction argument. -/
theorem residue_logWeightedSum_le_corrected_root_sum_of_no_prime {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x)
    (hno : ∀ p : ℕ, p.Prime → (p : ZMod q) = (a : ZMod q) → ¬(p : ℝ) ≤ x) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) = (a : ZMod q)),
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n) ≤
      (2 : ℝ) ^ q.primeFactors.card * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) +
        (∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
          (k : ℝ) *
            (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20 -
                Real.log (2 * Real.pi) * Real.log (x ^ ((1 : ℝ) / k)) -
                19 / 20 +
              Real.pi ^ 2 / 24)) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hs := AnalyticNumberTheory.Arithmetic.square_residue_sum_le a hx0
  change
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ IsSquare n ∧ (n : ZMod q) = (a : ZMod q)),
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n) ≤
      _ at hs
  have hn :=
    (AnalyticNumberTheory.Arithmetic.nonsquareCompositeLogWeightedSum_le_odd_powers hx0).trans
      (oddPrimePowerLogWeightedSum_le_corrected_root_sum hRH hx)
  exact
    (AnalyticNumberTheory.Arithmetic.residue_logWeightedSum_le_square_add_nonsquare (a : ZMod q) hx0
          hno).trans
      (add_le_add hs hn)

/-- Under GRH, for `q ≥ 64` and `x ≥ 65536`, a strict gap using the corrected
odd root sum bounds the least prime in every unit residue class by `x`.
Combine the corrected prime-free residue bound with the existing character-norm estimate
through the weighted-gap criterion. The logarithmic and constant savings are retained. -/
theorem exists_least_prime_in_residue_le_of_corrected_root_gap {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hq : 64 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 65536 ≤ x)
    (hgap :
      (q.totient : ℝ) *
            ((2 : ℝ) ^ q.primeFactors.card * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) +
              (∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
                (k : ℝ) *
                  (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20 -
                      Real.log (2 * Real.pi) * Real.log (x ^ ((1 : ℝ) / k)) -
                      19 / 20 +
                    Real.pi ^ 2 / 24))) +
          cosetNonprincipalUpper q ⊥ x <
        cosetPrincipalLower q x) :
    ∃ p : ℕ, IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧ (p : ℝ) ≤ x := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only) hx
  exact
    exists_least_prime_in_residue_le_of_weighted_gap a hGRH.riemann hx1
      (residue_logWeightedSum_le_corrected_root_sum_of_no_prime a hGRH.riemann hx1)
      (nonprincipal_logWeightedNorm_sum_le_explicit ⊥ hq hGRH hx) hgap

open Classical in
/-- Under RH, for any cutoff greater than one, a prime-free unit residue class
has logarithmic sum bounded by the square-congruence contribution and a finite
odd root sum. Separate squares and nonsquare composite prime powers and apply
the exponent-wise RH estimate. This keeps the sharper majorant at small cutoffs. -/
theorem residue_logWeightedSum_le_root_sum_of_no_prime {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x)
    (hno : ∀ p : ℕ, p.Prime → (p : ZMod q) = (a : ZMod q) → ¬(p : ℝ) ≤ x) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) = (a : ZMod q)),
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n) ≤
      (2 : ℝ) ^ q.primeFactors.card * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) +
        (∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
          (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hs := AnalyticNumberTheory.Arithmetic.square_residue_sum_le a hx0
  change
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ IsSquare n ∧ (n : ZMod q) = (a : ZMod q)),
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n) ≤
      _ at hs
  have hn :=
    (AnalyticNumberTheory.Arithmetic.nonsquareCompositeLogWeightedSum_le_odd_powers hx0).trans
      (oddPrimePowerLogWeightedSum_le_explicit_root_sum hRH hx)
  exact
    (AnalyticNumberTheory.Arithmetic.residue_logWeightedSum_le_square_add_nonsquare (a : ZMod q) hx0
          hno).trans
      (add_le_add hs hn)

open Classical in
/-- Under GRH, for modulus at least `64` and cutoff at least `65536`, a prime-free
unit residue class forces the principal lower bound below the totient-scaled
square and odd root majorants plus the nonprincipal norm bound. Apply the
identity subgroup's character average and retain the finite root sum.
This is the comparison used to select moduli for direct finite coverage. -/
theorem residue_no_prime_root_sum_sandwich {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) (hq : 64 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 65536 ≤ x)
    (hno : ∀ p : ℕ, p.Prime → (p : ZMod q) = (a : ZMod q) → ¬(p : ℝ) ≤ x) :
    cosetPrincipalLower q x ≤
      (q.totient : ℝ) *
          ((2 : ℝ) ^ q.primeFactors.card * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) +
            (∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
              (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20))) +
        cosetNonprincipalUpper q ⊥ x := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only) hx
  have hi : (⊥ : Subgroup (ZMod q)ˣ).index = q.totient := by
    rw [Subgroup.index_bot, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have ha := principal_logWeightedSum_le_coset_add_nonprincipal_norms (⊥ : Subgroup (ZMod q)ˣ) a x
  rw [cosetLogWeightedSum_bot_eq, hi] at ha
  have hu := residue_logWeightedSum_le_root_sum_of_no_prime a hGRH.riemann hx1 hno
  have hm := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg q.totient : (0 : ℝ) ≤ _)
  have hn := nonprincipal_logWeightedNorm_sum_le_explicit (⊥ : Subgroup (ZMod q)ˣ) hq hGRH hx
  exact (cosetPrincipalLower_le hGRH.riemann hx1).trans (ha.trans (add_le_add hm hn))

open Classical in
/-- Under GRH, for modulus at least `64` and cutoff at least `65536`, a strict
gap between the principal lower bound and the totient-scaled square and odd root
majorants plus the nonprincipal error bounds the least prime in any unit residue.
If that prime exceeded the cutoff, the prime-free sandwich would contradict
the gap. This allows Corollary 1.2 to use analytic estimates for smaller moduli. -/
theorem exists_least_prime_in_residue_le_of_explicit_root_gap {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hq : 64 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 65536 ≤ x)
    (hgap :
      (q.totient : ℝ) *
            ((2 : ℝ) ^ q.primeFactors.card * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) +
              (∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
                (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20))) +
          cosetNonprincipalUpper q ⊥ x <
        cosetPrincipalLower q x) :
    ∃ p : ℕ, IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧ (p : ℝ) ≤ x := by
  obtain ⟨p, hp⟩ := exists_least_prime_in_residue a
  refine ⟨p, hp, ?_⟩
  by_contra hn
  have hno : ∀ r : ℕ, r.Prime → (r : ZMod q) = (a : ZMod q) → ¬(r : ℝ) ≤ x := by
    intro r hr hra hrx
    exact hn ((Nat.cast_le.mpr (hp.2 ⟨hr, hra⟩)).trans hrx)
  exact (not_lt_of_ge (residue_no_prime_root_sum_sandwich a hq hGRH hx hno)) hgap

open Classical in
/-- Under GRH, for modulus at least `64` and cutoff at least `65536`, natural-power
and square inequalities certify the odd root majorant. If this certified sum,
the square-residue contribution and nonprincipal bound lie below the principal
lower bound, every unit residue has its least prime below the cutoff. This
connects finite rational root certificates to Corollary 1.2. -/
theorem exists_least_prime_in_residue_le_of_power_certificates {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hq : 64 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 65536 ≤ x) {K : ℕ} (hK : ⌊Real.log x / Real.log 2⌋₊ ≤ K) (b c : ℕ → ℝ)
    (hb : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ b k)
    (hc : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ c k)
    (hpow : ∀ k ∈ (Finset.Icc 3 K).filter Odd, x ≤ b k ^ k)
    (hsq : ∀ k ∈ (Finset.Icc 3 K).filter Odd, b k ≤ c k ^ 2)
    (hgap :
      (q.totient : ℝ) *
            ((2 : ℝ) ^ q.primeFactors.card * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) +
              ∑ k ∈ (Finset.Icc 3 K).filter Odd, (k : ℝ) * (b k + c k / 20)) +
          cosetNonprincipalUpper q ⊥ x <
        cosetPrincipalLower q x) :
    ∃ p : ℕ, IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧ (p : ℝ) ≤ x := by
  have hx0 : 0 ≤ x := (by norm_num only : (0 : ℝ) ≤ 65536).trans hx
  have hr := oddRootSum_le_of_power_certificates hx0 hK b c hb hc hpow hsq
  have hm :=
    mul_le_mul_of_nonneg_left
      (add_le_add
        (le_refl ((2 : ℝ) ^ q.primeFactors.card * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1))) hr)
      (Nat.cast_nonneg q.totient : (0 : ℝ) ≤ q.totient)
  exact
    exists_least_prime_in_residue_le_of_explicit_root_gap a hq hGRH hx
      (lt_of_le_of_lt (add_le_add hm (le_refl (cosetNonprincipalUpper q ⊥ x))) hgap)

open Classical in
/-- For a nonzero modulus, a unit residue, RH and a cutoff at least one billion,
a progression containing no prime up to the cutoff has logarithmic Mangoldt sum
bounded by the square-congruence contribution plus one seventh of the square root.
Separate square and nonsquare terms; bound the former by the number of square roots
and the latter by odd prime powers. This supplies the upper side of LLS Section 4.1. -/
theorem residue_logWeightedSum_le_of_no_prime {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hRH : RiemannHypothesis) {x : ℝ} (hx : 1000000000 ≤ x)
    (hno : ∀ p : ℕ, p.Prime → (p : ZMod q) = (a : ZMod q) → ¬(p : ℝ) ≤ x) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) = (a : ZMod q)),
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n) ≤
      (2 : ℝ) ^ q.primeFactors.card * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) +
        Real.sqrt x / 7 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hs := AnalyticNumberTheory.Arithmetic.square_residue_sum_le a hx0
  change
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ IsSquare n ∧ (n : ZMod q) = (a : ZMod q)),
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n) ≤
      _ at hs
  have hn :=
    (AnalyticNumberTheory.Arithmetic.nonsquareCompositeLogWeightedSum_le_odd_powers hx0).trans
      (oddPrimePowerLogWeightedSum_le_sqrt_seventh hRH hx)
  exact
    (AnalyticNumberTheory.Arithmetic.residue_logWeightedSum_le_square_add_nonsquare (a : ZMod q) hx0
          hno).trans
      (add_le_add hs hn)

open Classical in
/-- Under GRH, a modulus at least twenty thousand and a cutoff at least one billion,
absence of primes in a unit residue class forces the explicit principal lower bound
below the totient-scaled prime-power upper bound plus the nonprincipal norm majorant.
Use the identity subgroup's character average and its totient index, then insert
the analytic lower and upper estimates. This leaves the arithmetic and real numerical
comparison needed to prove Corollary 1.2. -/
theorem residue_no_prime_sandwich {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) (hq : 20000 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1000000000 ≤ x)
    (hno : ∀ p : ℕ, p.Prime → (p : ZMod q) = (a : ZMod q) → ¬(p : ℝ) ≤ x) :
    cosetPrincipalLower q x ≤
      (q.totient : ℝ) *
          ((2 : ℝ) ^ q.primeFactors.card * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) +
            Real.sqrt x / 7) +
        cosetNonprincipalUpper q ⊥ x := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only) hx
  have hi : (⊥ : Subgroup (ZMod q)ˣ).index = q.totient := by
    rw [Subgroup.index_bot, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have ha := principal_logWeightedSum_le_coset_add_nonprincipal_norms (⊥ : Subgroup (ZMod q)ˣ) a x
  rw [cosetLogWeightedSum_bot_eq, hi] at ha
  have hu := residue_logWeightedSum_le_of_no_prime a hGRH.riemann hx hno
  have hm := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg q.totient : (0 : ℝ) ≤ _)
  have hn :=
    nonprincipal_logWeightedNorm_sum_le_explicit (⊥ : Subgroup (ZMod q)ˣ)
      ((by norm_num only : (64 : ℕ) ≤ 20000).trans hq) hGRH
      ((by norm_num only : (65536 : ℝ) ≤ 1000000000).trans hx)
  exact (cosetPrincipalLower_le hGRH.riemann hx1).trans (ha.trans (add_le_add hm hn))

/-- Under GRH and the large-modulus and cutoff bounds, a strict gap between the
explicit principal lower bound and the totient-scaled square and odd-power estimates,
including the nonprincipal error, bounds the least prime in every unit residue class.
If its least prime exceeded the cutoff, the no-prime sandwich would contradict the gap.
This is the numerical comparison interface for Corollary 1.2. -/
theorem exists_least_prime_in_residue_le_of_explicit_gap {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hq : 20000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1000000000 ≤ x)
    (hgap :
      (q.totient : ℝ) *
            ((2 : ℝ) ^ q.primeFactors.card * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) +
              Real.sqrt x / 7) +
          cosetNonprincipalUpper q ⊥ x <
        cosetPrincipalLower q x) :
    ∃ p : ℕ, IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧ (p : ℝ) ≤ x := by
  obtain ⟨p, hp⟩ := exists_least_prime_in_residue a
  refine ⟨p, hp, ?_⟩
  by_contra hn
  have hno : ∀ r : ℕ, r.Prime → (r : ZMod q) = (a : ZMod q) → ¬(r : ℝ) ≤ x := by
    intro r hr hra hrx
    exact hn ((Nat.cast_le.mpr (hp.2 ⟨hr, hra⟩)).trans hrx)
  exact (not_lt_of_ge (residue_no_prime_sandwich a hq hGRH hx hno)) hgap

/-- For a modulus at least twenty thousand, the corollary's squared totient-logarithm
cutoff is at least one billion. Combine the totient lower bound 4156 with the logarithm
lower bound nine and square their nonnegative product. This discharges the cutoff
premise for the prime-power and character-average estimates of LLS Section 4.1. -/
theorem residue_cutoff_ge_billion {q : ℕ} (hq : 20000 ≤ q) :
    (1000000000 : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  have hqR : (19683 : ℝ) ≤ q := (by norm_num only : (19683 : ℝ) ≤ 20000).trans (Nat.cast_le.mpr hq)
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 19683) hqR
  rw [show (19683 : ℝ) = 3 ^ 9 by norm_num only, Real.log_pow] at hl
  norm_num only at hl
  have hlog : (9 : ℝ) ≤ Real.log q := by linarith only [hl, Real.log_three_gt_d9]
  have hphi : (4156 : ℝ) ≤ q.totient := Nat.cast_le.mpr (NumberTheory.totient_ge_4156 hq)
  have hs : (37404 : ℝ) ≤ (q.totient : ℝ) * Real.log q := by
    have hb := mul_le_mul hphi hlog (by norm_num only : (0 : ℝ) ≤ 9) (Nat.cast_nonneg q.totient)
    norm_num only at hb
    exact hb
  have hb := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 37404) hs 2
  norm_num only at hb
  linarith only [hb]

/-- For a large modulus, replace the square-root count's prime-factor power by the
modulus to three sevenths. The remaining factors are nonnegative for every real cutoff.
This common comparison transports both the residue sum and its prime criterion. -/
private theorem residue_primePower_majorant_le_rpow {q : ℕ} (hq : 20000 ≤ q) (x : ℝ) :
    (2 : ℝ) ^ q.primeFactors.card * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) + Real.sqrt x / 7 ≤
      (q : ℝ) ^ (3 / 7 : ℝ) * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) + Real.sqrt x / 7 := by
  have hc : 0 ≤ (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) :=
    mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num only))
      (add_nonneg (div_nonneg (Real.sqrt_nonneg x) (Nat.cast_nonneg q)) zero_le_one)
  have hb := mul_le_mul_of_nonneg_right (NumberTheory.two_pow_card_primeFactors_le_rpow hq) hc
  have he :
    (2 : ℝ) ^ q.primeFactors.card * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) ≤
      (q : ℝ) ^ (3 / 7 : ℝ) * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) := by
    convert hb using 1 <;> ring
  exact add_le_add he le_rfl

open Classical in
/-- Under RH at a cutoff at least one billion, a prime-free unit residue class for a
modulus at least twenty thousand has the upper bound of LLS Section 4.1.
Insert the unconditional prime-factor power estimate into the square and odd-power
comparison. This removes the prime-factor count from the numerical upper bound. -/
theorem residue_logWeightedSum_le_rpow_of_no_prime {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hq : 20000 ≤ q) (hRH : RiemannHypothesis) {x : ℝ} (hx : 1000000000 ≤ x)
    (hno : ∀ p : ℕ, p.Prime → (p : ZMod q) = (a : ZMod q) → ¬(p : ℝ) ≤ x) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) = (a : ZMod q)),
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n) ≤
      (q : ℝ) ^ (3 / 7 : ℝ) * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) + Real.sqrt x / 7 := by
  exact
    (residue_logWeightedSum_le_of_no_prime a hRH hx hno).trans
      (residue_primePower_majorant_le_rpow hq x)

/-- Under GRH and the large-modulus and cutoff bounds, the modulus-power upper
majorant plus the nonprincipal error being strictly below the principal lower bound
forces the least prime in any unit residue class below the cutoff.
Transport the proved square-root count comparison into the existing prime criterion.
This leaves a real numerical gap, with no extra prime-factor hypothesis. -/
theorem exists_least_prime_in_residue_le_of_rpow_gap {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (hq : 20000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1000000000 ≤ x)
    (hgap :
      (q.totient : ℝ) *
            ((q : ℝ) ^ (3 / 7 : ℝ) * (Real.log x) ^ 2 / 4 * (Real.sqrt x / q + 1) +
              Real.sqrt x / 7) +
          cosetNonprincipalUpper q ⊥ x <
        cosetPrincipalLower q x) :
    ∃ p : ℕ, IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧ (p : ℝ) ≤ x := by
  apply exists_least_prime_in_residue_le_of_explicit_gap a hq hGRH hx
  exact
    (add_le_add
          (mul_le_mul_of_nonneg_left (residue_primePower_majorant_le_rpow hq x)
            (Nat.cast_nonneg q.totient : (0 : ℝ) ≤ _))
          le_rfl).trans_lt
      hgap

end PseudoPrime.LLS.PaperStatements
