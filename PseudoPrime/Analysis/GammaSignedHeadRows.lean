/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSignedEulerTail
public import PseudoPrime.Analysis.GammaEnvelopePrimeRows

/-! # Signed first-term Euler certificates connected to local rows and finite excess sums -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a prime row, an anchor below its squared prime, checked first-term node intervals
and a rational allowance cap. Claim: the actual Euler cost is below the row allowance.
Proof: combine the signed first term and anchored tail. Role: remove the analytic Euler field. -/
theorem GammaLocalPrimeRow.euler_le_of_signed_head (r : GammaLocalPrimeRow) (hp : r.prime.Prime)
    {a : ℕ} (ha : a ∈ gammaDyadicAnchors) (hap : a ≤ r.prime ^ 2)
    (hc : gammaFiniteEulerRatioCheck r.prime r.ratios = true)
    (hcap :
      gammaFiniteEulerUpper r.ratios +
          gammaDyadicAnchorCap a / ((r.prime : ℚ) * ((r.prime : ℚ) - 1)) ≤
        r.eulerUpper) :
    gammaPrimeEulerCost r.prime ≤ (r.eulerUpper : ℝ) := by
  have h := gamma_prime_euler_cost_le_first_term_certificate hp.one_lt ha hap hc
  exact h.trans ((Rat.cast_le (K := ℝ)).mpr hcap)

/-- Input: the same first-term certificate, a checked local cell/row and x in the cell.
Claim: the actual logarithm-weighted positive excess is at most the row allowance.
Proof: pass the certified Euler bound to generic row soundness.
Role: retain signed Euler cancellation in the actual dual cost. -/
theorem GammaLocalPrimeRow.weighted_excess_le_of_signed_head (r : GammaLocalPrimeRow)
    (c : GammaLocalCellData) (hcell : c.check = true) (hp : r.prime.Prime) {a : ℕ}
    (ha : a ∈ gammaDyadicAnchors) (hap : a ≤ r.prime ^ 2)
    (hnodes : gammaFiniteEulerRatioCheck r.prime r.ratios = true)
    (hcap :
      gammaFiniteEulerUpper r.ratios +
          gammaDyadicAnchorCap a / ((r.prime : ℚ) * ((r.prime : ℚ) - 1)) ≤
        r.eulerUpper)
    (hrow : r.envelopeCheck c = true) {x : ℝ} (hlo : (c.lo : ℝ) ≤ x) (hhi : x ≤ (c.hi : ℝ)) :
    Real.log r.prime *
        max (gammaRamifiedSignedCombinedCost r.prime x - gammaRamifiedThetaParameter c.theta x) 0 ≤
      (r.allowance : ℝ) := by
  exact
    r.weighted_excess_le_of_euler_bound c hcell hp hrow
      (r.euler_le_of_signed_head hp ha hap hnodes hcap) hlo hhi

/-- Input: a finite prime set, matching checked rows and first-term/tail certificates for each row.
Claim: the actual finite excess sum is below the sum of rational row allowances.
Proof: derive every Euler upper bound and apply the generic finite-sum interface.
Role: connect signed-head certificates to dual-budget and witness-separation comparisons. -/
theorem gamma_envelope_prime_sum_upper_of_signed_heads (R : Finset ℕ) (r : ℕ → GammaLocalPrimeRow)
    (a : ℕ → ℕ) (c : GammaLocalCellData) (hcell : c.check = true) (hp : ∀ p ∈ R, p.Prime)
    (hi : ∀ p ∈ R, (r p).prime = p) (hrows : ∀ p ∈ R, (r p).envelopeCheck c = true)
    (hheads :
      ∀ p ∈ R,
        a p ∈ gammaDyadicAnchors ∧
          a p ≤ (r p).prime ^ 2 ∧
          gammaFiniteEulerRatioCheck (r p).prime (r p).ratios = true ∧
          gammaFiniteEulerUpper (r p).ratios +
              gammaDyadicAnchorCap (a p) / (((r p).prime : ℚ) * (((r p).prime : ℚ) - 1)) ≤
            (r p).eulerUpper)
    {x : ℝ} (hlo : (c.lo : ℝ) ≤ x) (hhi : x ≤ (c.hi : ℝ)) :
    (∑ p ∈ R,
        Real.log p *
          max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter c.theta x) 0) ≤
      ((∑ p ∈ R, (r p).allowance : ℚ) : ℝ) := by
  apply gamma_envelope_prime_sum_upper R r c hcell hp hi hrows ?_ hlo hhi
  intro p hpr
  have hh := hheads p hpr
  have h := (r p).euler_le_of_signed_head ((hi p hpr).symm ▸ hp p hpr) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  simpa only [hi p hpr] using h

end PseudoPrime.Analysis
