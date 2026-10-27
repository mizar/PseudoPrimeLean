/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaQuadraticPolynomialSeparation
public import PseudoPrime.Analysis.GammaEulerPositiveLowerBound
public import PseudoPrime.LLS.GammaEulerGrowthChebyshev
public import PseudoPrime.LLS.GammaAnchoredDualBudget
public import PseudoPrime.LLS.GammaWindowDualBudget
public import PseudoPrime.LLS.GammaLowerWindowBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaSignedVariationBounds

/-! # Quadratic prime witnesses and finite maxima from a shared polynomial condition -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, the displayed arithmetic and scale bounds, effective prefix
credit, signed dual cap and shared polynomial condition. Claim: an odd-prime witness
is at most (99/40)x. Apply the retained-margin transfer and the existing
witness or maximum interface. Role: expose the polynomial criterion directly. -/
theorem exists_prime_neg_one_witness_of_polynomial {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x C D : ℝ} (hL : 10 ≤ L)
    (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hcredit :
      C + (3 / 4 + D + 7 / 60) / 2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : LLS.gammaScaleSignedDualBudget L x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (L + 7 / 5) x C) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  have hg := LLS.gamma_retained_margin_gt_of_polynomial (by linarith only [hx]) hcredit hdual hpoly
  exact
    exists_prime_neg_one_witness_of_retained_common_factor_free_separation hn hns hGRH hL hlog hx hb
      hbx hg.le

/-- Input: GRH, the displayed arithmetic and scale bounds, effective prefix
credit, signed dual cap and shared polynomial condition. Claim: an odd-prime witness
is at most (99/40)x. Apply the retained-margin transfer and the existing
witness or maximum interface. Role: expose the polynomial criterion directly. -/
theorem exists_prime_ne_one_witness_of_polynomial {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x C D : ℝ} (hL : 10 ≤ L)
    (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hcredit :
      C + (3 / 4 + D + 7 / 60) / 2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : LLS.gammaScaleSignedDualBudget L x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (L + 7 / 5) x C) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hbound, hv⟩ :=
    exists_prime_neg_one_witness_of_polynomial hn hns hGRH hL hlog hx hb hbx hcredit hdual hpoly
  exact
    ⟨p, hp, ho, hbound, by
      rw [hv]; norm_num only⟩

/-- Input: GRH, the displayed arithmetic and scale bounds, effective prefix
credit, signed dual cap and shared polynomial condition. Claim: the least odd-prime witness
is at most (99/40)x. Apply the retained-margin transfer and the existing
witness or maximum interface. Role: expose the polynomial criterion directly. -/
theorem primeNegOneWitness_cast_le_of_polynomial {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x C D : ℝ} (hL : 10 ≤ L)
    (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hcredit :
      C + (3 / 4 + D + 7 / 60) / 2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : LLS.gammaScaleSignedDualBudget L x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (L + 7 / 5) x C)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hbound, hv⟩ :=
    exists_prime_neg_one_witness_of_polynomial hn hns hGRH hL hlog hx hb hbx hcredit hdual hpoly
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hbound

/-- Input: GRH, the displayed arithmetic and scale bounds, effective prefix
credit, signed dual cap and shared polynomial condition. Claim: the least odd-prime witness
is at most (99/40)x. Apply the retained-margin transfer and the existing
witness or maximum interface. Role: expose the polynomial criterion directly. -/
theorem primeNeOneWitness_cast_le_of_polynomial {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x C D : ℝ} (hL : 10 ≤ L)
    (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hcredit :
      C + (3 / 4 + D + 7 / 60) / 2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : LLS.gammaScaleSignedDualBudget L x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (L + 7 / 5) x C)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hbound, hv⟩ :=
    exists_prime_ne_one_witness_of_polynomial hn hns hGRH hL hlog hx hb hbx hcredit hdual hpoly
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hbound

/-- Input: GRH, the displayed arithmetic and scale bounds, effective prefix
credit, signed dual cap and shared polynomial condition. Claim: the full finite maximum
is at most (99/40)x. Apply the retained-margin transfer and the existing
witness or maximum interface. Role: expose the polynomial criterion directly. -/
theorem QNegOne_le_of_polynomial {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x C D : ℝ}
    (hB : 10 ≤ Real.log B) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hcredit :
      C + (3 / 4 + D + 7 / 60) / 2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hg := LLS.gamma_retained_margin_gt_of_polynomial (by linarith only [hx]) hcredit hdual hpoly
  exact QNegOne_le_of_retained_common_factor_free_separation hGRH hB hx hb hbx hg.le

/-- Input: GRH, the displayed arithmetic and scale bounds, effective prefix
credit, signed dual cap and shared polynomial condition. Claim: the full finite maximum
is at most (99/40)x. Apply the retained-margin transfer and the existing
witness or maximum interface. Role: expose the polynomial criterion directly. -/
theorem QNeOne_le_of_polynomial {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x C D : ℝ}
    (hB : 10 ≤ Real.log B) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hcredit :
      C + (3 / 4 + D + 7 / 60) / 2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C) :
    (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  exact
    (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans
      (QNegOne_le_of_polynomial hGRH hB hx hb hbx hcredit hdual hpoly)

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, a>=900, b>=2a, an admissible witness scale and
the displayed initial-credit, dual and polynomial conditions. Claim: both
full quadratic witness maxima are at most (99/40)x. Apply the uniform
analytic block gain before extraction. Role: expose short-block growth
without four auxiliary real endpoints or a finite psi table. -/
theorem Q_witness_maxima_le_of_doubling_block_polynomial {B a b : ℕ} {x C D P : ℝ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hB : 10 ≤ Real.log B)
    (hx : 4096 ≤ x) (ha : 900 ≤ a) (hratio : (2 : ℝ) * a ≤ b) (hbx : (b : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hP : P ≤ ∑ j ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight j)
    (hcredit : C + (3 / 4 + D + 7 / 60) / 2 ≤ P + ((a : ℝ) / 8) * (b : ℝ) ^ (-21 / 20 : ℝ))
    (hdual : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x ∧ (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hg := LLS.gamma_euler_prefix_lower_growth_of_doubling_block hGRH.riemann ha hratio hP
  have hp :
    C + (3 / 4 + D + 7 / 60) / 2 ≤
      ∑ j ∈ Finset.Ioc 0 ⌊(b : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight j := by
    simpa only [Nat.floor_natCast] using hcredit.trans hg
  have haR : (900 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (1 : ℝ) ≤ b := by linarith only [haR, hratio]
  exact
    ⟨QNegOne_le_of_polynomial hGRH hB hx hbR hbx hp hdual hpoly,
      QNeOne_le_of_polynomial hGRH hB hx hbR hbx hp hdual hpoly⟩

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, a>=10000, b>=5a/4, an admissible witness scale and
the displayed initial-credit, dual and polynomial conditions. Claim: both
full quadratic witness maxima are at most (99/40)x. Apply the uniform
analytic block gain before extraction. Role: expose short-block growth
without four auxiliary real endpoints or a finite psi table. -/
theorem Q_witness_maxima_le_of_five_fourths_block_polynomial {B a b : ℕ} {x C D P : ℝ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hB : 10 ≤ Real.log B)
    (hx : 4096 ≤ x) (ha : 10000 ≤ a) (hratio : (5 / 4 : ℝ) * a ≤ b)
    (hbx : (b : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hP : P ≤ ∑ j ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight j)
    (hcredit : C + (3 / 4 + D + 7 / 60) / 2 ≤ P + ((a : ℝ) / 200) * (b : ℝ) ^ (-21 / 20 : ℝ))
    (hdual : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x ∧ (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hg := LLS.gamma_euler_prefix_lower_growth_of_five_fourths_block hGRH.riemann ha hratio hP
  have hp :
    C + (3 / 4 + D + 7 / 60) / 2 ≤
      ∑ j ∈ Finset.Ioc 0 ⌊(b : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight j := by
    simpa only [Nat.floor_natCast] using hcredit.trans hg
  have haR : (10000 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (1 : ℝ) ≤ b := by linarith only [haR, hratio]
  exact
    ⟨QNegOne_le_of_polynomial hGRH hB hx hbR hbx hp hdual hpoly,
      QNeOne_le_of_polynomial hGRH hB hx hbR hbx hp hdual hpoly⟩

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, admissible endpoints and scale, an initial Euler credit,
and the displayed analytic-block, dual and polynomial conditions. Claim:
both full quadratic witness maxima are at most (99/40)x. Use asymmetric
Chebyshev differences before polynomial extraction. Role: remove the fixed
large-scale entrance from the short-block witness interface. -/
theorem Q_witness_maxima_le_of_asymmetric_block_polynomial {B a b : ℕ} {x C D P s t : ℝ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hB : 10 ≤ Real.log B)
    (hx : 4096 ≤ x) (hab : a ≤ b) (hs : 1 < s) (hsb : s < b) (ha : (1 : ℝ) < a) (hat : (a : ℝ) < t)
    (hbx : (b : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hP : P ≤ ∑ j ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight j)
    (hcredit :
      C + (3 / 4 + D + 7 / 60) / 2 ≤
        P + (1 / 2 : ℝ) * (b : ℝ) ^ (-21 / 20 : ℝ) * LLS.psiAsymmetricBlockLower a b s t)
    (hdual : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x ∧ (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hg :=
    LLS.gamma_euler_prefix_lower_growth_of_asymmetric_rh_errors hGRH.riemann hab hs hsb ha hat hP
  have hp :
    C + (3 / 4 + D + 7 / 60) / 2 ≤
      ∑ j ∈ Finset.Ioc 0 ⌊(b : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight j := by
    simpa only [Nat.floor_natCast] using hcredit.trans hg
  have habR : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
  have hbR : (1 : ℝ) ≤ b := (ha.trans_le habR).le
  exact
    ⟨QNegOne_le_of_polynomial hGRH hB hx hbR hbx hp hdual hpoly,
      QNeOne_le_of_polynomial hGRH hB hx hbR hbx hp hdual hpoly⟩

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, admissible common endpoint and scale, a prefix credit at a,
and the displayed grown-credit, dual and polynomial conditions. Claim: both
finite witness maxima are at most (99/40)x. Apply the analytic prefix increment
before the existing polynomial extraction. Role: reuse positivity for both witnesses. -/
theorem Q_witness_maxima_le_of_prefix_growth_polynomial {B a b : ℕ} {x C D P : ℝ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hB : 10 ≤ Real.log B)
    (hx : 4096 ≤ x) (hb : 1 ≤ b) (hab : a ≤ b) (hbx : (b : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hP : P ≤ ∑ k ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight k)
    (hcredit :
      C + (3 / 4 + D + 7 / 60) / 2 ≤
        P + (1 / 2 : ℝ) * (b : ℝ) ^ (-21 / 20 : ℝ) * (Chebyshev.psi b - Chebyshev.psi a))
    (hdual : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x ∧ (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hp :
    C + (3 / 4 + D + 7 / 60) / 2 ≤
      ∑ k ∈ Finset.Ioc 0 ⌊(b : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight k := by
    simpa only [Nat.floor_natCast] using
      hcredit.trans (Analysis.gamma_euler_prefix_lower_growth hab hP)
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  exact
    ⟨QNegOne_le_of_polynomial hGRH hB hx hbR hbx hp hdual hpoly,
      QNeOne_le_of_polynomial hGRH hB hx hbR hbx hp hdual hpoly⟩

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- Input: an old checked cell, a lower endpoint, corrected row cap and
the displayed prefix credit and polynomial condition under GRH.
Claim: both finite witness maxima are at most (99/40)x. Apply the downward
window dual estimate. Role: connect reused rows to witness bounds. -/
theorem Q_witness_maxima_le_of_lowered_window_polynomial (c : Analysis.GammaLocalCellData)
    (rows : ℕ → Analysis.GammaLocalPrimeRow) (hcell : c.check = true) {B : ℕ} {b lo x C E : ℝ}
    (hB : 10 ≤ Real.log B) (hlo : 4096 ≤ lo) (hab : lo ≤ (c.lo : ℝ)) (hlox : lo ≤ x)
    (hxhi : x ≤ (c.hi : ℝ)) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hcheck :
      ∀ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
        (rows p).prime = p ∧ (rows p).envelopeCheck c = true)
    (he :
      ∀ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
        Analysis.gammaPrimeEulerCost p ≤ ((rows p).eulerUpper : ℝ))
    (hrows :
      (∑ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
          Real.log p *
            Analysis.gammaRamifiedWindowExcessBound lo c.hi (rows p).eulerUpper
              (((rows p).rampUpper : ℝ) - 5 / 4 + (9 / 2 : ℝ) * ((c.lo : ℝ) - lo) / lo)) ≤
        E)
    (hcredit :
      C + (3 / 4 + (Analysis.gammaRamifiedDualParameter lo * Real.log B + E) + 7 / 60) / 2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x ∧ (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hd :=
    LLS.gamma_scale_signed_dual_budget_le_lowered_window_rows c rows hcell (by linarith only [hB])
      (by linarith only [hlo]) hab hlox hxhi hcheck he hrows
  have hx := hlo.trans hlox
  exact
    ⟨QNegOne_le_of_polynomial hGRH hB hx hb hbx hcredit hd hpoly,
      QNeOne_le_of_polynomial hGRH hB hx hb hbx hcredit hd hpoly⟩

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- Input: an old checked cell, a lower endpoint, corrected row cap and
the displayed prefix credit and polynomial condition under GRH.
Claim: both finite witness maxima are at most (99/40)x. Apply the downward
window dual estimate with its base-sensitive correction.
Role: connect reused rows to witness bounds. -/
theorem Q_witness_maxima_le_of_lowered_window_polynomial_base_ratio
    (c : Analysis.GammaLocalCellData) (rows : ℕ → Analysis.GammaLocalPrimeRow)
    (hcell : c.check = true) {B : ℕ} {b lo x C E : ℝ} (hB : 10 ≤ Real.log B) (hlo : 4096 ≤ lo)
    (hab : lo ≤ (c.lo : ℝ)) (hlox : lo ≤ x) (hxhi : x ≤ (c.hi : ℝ)) (hb : 1 ≤ b)
    (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hcheck :
      ∀ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
        (rows p).prime = p ∧ (rows p).envelopeCheck c = true)
    (he :
      ∀ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
        Analysis.gammaPrimeEulerCost p ≤ ((rows p).eulerUpper : ℝ))
    (hrows :
      (∑ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
          Real.log p *
            Analysis.gammaRamifiedWindowExcessBound lo c.hi (rows p).eulerUpper
              (((rows p).rampUpper : ℝ) - 5 / 4 +
                (((p : ℝ) + 1) / (p - 1)) * ((c.lo : ℝ) - lo) / lo)) ≤
        E)
    (hcredit :
      C + (3 / 4 + (Analysis.gammaRamifiedDualParameter lo * Real.log B + E) + 7 / 60) / 2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x ∧ (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hd :=
    LLS.gamma_scale_signed_dual_budget_le_lowered_window_rows_base_ratio c rows hcell
      (by linarith only [hB]) (by linarith only [hlo]) hab hlox hxhi hcheck he hrows
  have hx := hlo.trans hlox
  exact
    ⟨QNegOne_le_of_polynomial hGRH hB hx hb hbx hcredit hd hpoly,
      QNeOne_le_of_polynomial hGRH hB hx hb hbx hcredit hd hpoly⟩

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, a common endpoint B, a scale window and endpoint row caps,
plus the displayed prefix credit and polynomial condition. Claim: both finite
witness maxima are at most (99/40)x. Supply the uniform window dual bound to
the existing polynomial interfaces. Role: reuse endpoint data for every scale. -/
theorem Q_witness_maxima_le_of_window_polynomial {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b lo x hi C E : ℝ}
    (hB : 10 ≤ Real.log B) (hlo : 4096 ≤ lo) (hlox : lo ≤ x) (hxhi : x ≤ hi) (hb : 1 ≤ b)
    (hbx : b ≤ (99 / 40 : ℝ) * x) (e N : ℕ → ℝ)
    (he : ∀ p ∈ Analysis.gammaAnchoredWindowPrimeSet hi, Analysis.gammaPrimeEulerCost p ≤ e p)
    (hN :
      ∀ p ∈ Analysis.gammaAnchoredWindowPrimeSet hi,
        Analysis.gammaRamifiedWindowNumerator p lo hi (5 / 4) ≤ N p)
    (hrows :
      (∑ p ∈ Analysis.gammaAnchoredWindowPrimeSet hi,
          Real.log p * Analysis.gammaRamifiedWindowExcessBound lo hi (e p) (N p)) ≤
        E)
    (hcredit :
      C + (3 / 4 + (Analysis.gammaRamifiedDualParameter lo * Real.log B + E) + 7 / 60) / 2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x ∧ (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hd :=
    LLS.gamma_scale_signed_dual_budget_le_window_rows (by linarith only [hB])
      (by linarith only [hlo]) hlox hxhi e N he hN hrows
  have hx := hlo.trans hlox
  exact
    ⟨QNegOne_le_of_polynomial hGRH hB hx hb hbx hcredit hd hpoly,
      QNeOne_le_of_polynomial hGRH hB hx hb hbx hcredit hd hpoly⟩

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, a common endpoint B, admissible scale/prefix, anchored
excess cap E and the displayed effective credit and polynomial condition.
Claim: both full finite maxima are at most (99/40)x. Use the anchored dual
cap and existing polynomial interfaces. Role: avoid larger support tables. -/
theorem Q_witness_maxima_le_of_anchored_polynomial {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x C E : ℝ}
    (hB : 10 ≤ Real.log B) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hrows :
      (∑ p ∈ Analysis.gammaRamifiedCertificatePrimeSet (max 160 (1 + (52 / 25 : ℝ) * Real.sqrt x)),
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
              0) ≤
        E)
    (hcredit :
      C + (3 / 4 + (Analysis.gammaRamifiedDualParameter x * Real.log B + E) + 7 / 60) / 2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x ∧ (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hd :=
    LLS.gamma_scale_signed_dual_budget_le_of_anchored_rows (L := Real.log B) (by linarith only [hx])
      hrows
  exact
    ⟨QNegOne_le_of_polynomial hGRH hB hx hb hbx hcredit hd hpoly,
      QNeOne_le_of_polynomial hGRH hB hx hb hbx hcredit hd hpoly⟩

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- Input: an old checked cell, a lower endpoint, corrected row cap and
the displayed prefix credit and polynomial condition under GRH.
Claim: both finite witness maxima are at most (99/40)x. Apply the downward
window dual estimate with correction coefficient 3. Role: connect reused rows to witness bounds. -/
theorem Q_witness_maxima_le_of_lowered_window_polynomial_three (c : Analysis.GammaLocalCellData)
    (rows : ℕ → Analysis.GammaLocalPrimeRow) (hcell : c.check = true) {B : ℕ} {b lo x C E : ℝ}
    (hB : 10 ≤ Real.log B) (hlo : 4096 ≤ lo) (hab : lo ≤ (c.lo : ℝ)) (hlox : lo ≤ x)
    (hxhi : x ≤ (c.hi : ℝ)) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hcheck :
      ∀ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
        (rows p).prime = p ∧ (rows p).envelopeCheck c = true)
    (he :
      ∀ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
        Analysis.gammaPrimeEulerCost p ≤ ((rows p).eulerUpper : ℝ))
    (hrows :
      (∑ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
          Real.log p *
            Analysis.gammaRamifiedWindowExcessBound lo c.hi (rows p).eulerUpper
              (((rows p).rampUpper : ℝ) - 5 / 4 + (3 : ℝ) * ((c.lo : ℝ) - lo) / lo)) ≤
        E)
    (hcredit :
      C + (3 / 4 + (Analysis.gammaRamifiedDualParameter lo * Real.log B + E) + 7 / 60) / 2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x ∧ (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hd :=
    LLS.gamma_scale_signed_dual_budget_le_lowered_window_rows_three c rows hcell
      (by linarith only [hB]) (by linarith only [hlo]) hab hlox hxhi hcheck he hrows
  have hx := hlo.trans hlox
  exact
    ⟨QNegOne_le_of_polynomial hGRH hB hx hb hbx hcredit hd hpoly,
      QNeOne_le_of_polynomial hGRH hB hx hb hbx hcredit hd hpoly⟩

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, an admissible scale, an initial Euler credit at a>=100000,
a lower bound for the final endpoint power, and the displayed grown-credit,
dual and polynomial conditions. Claim: both full quadratic witness maxima are
at most (99/40)x. Use symbolic doubling before the common polynomial extraction.
Role: connect analytic Euler blocks to both quadratic witness bounds. -/
theorem Q_witness_maxima_le_of_doubling_polynomial {B a k : ℕ} {x C D P r : ℝ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hB : 10 ≤ Real.log B)
    (hx : 4096 ≤ x) (ha : 100000 ≤ a) (hbx : (a * 2 ^ k : ℕ) ≤ (99 / 40 : ℝ) * x)
    (hr : r ≤ (a * 2 ^ k : ℕ) ^ (-1 / 20 : ℝ))
    (hP : P ≤ ∑ j ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight j)
    (hcredit : C + (3 / 4 + D + 7 / 60) / 2 ≤ P + (39 / 200 : ℝ) * r * k)
    (hdual : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D)
    (hpoly : LLS.GammaPairedPolynomialCondition (Real.log B + 7 / 5) x C) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x ∧ (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hg :=
    LLS.gamma_euler_prefix_lower_doublings_of_power_lower hGRH.riemann ha hr hP k
      (le_refl (a * 2 ^ k))
  have hp :
    C + (3 / 4 + D + 7 / 60) / 2 ≤
      ∑ j ∈ Finset.Ioc 0 ⌊((a * 2 ^ k : ℕ) : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight j := by
    simpa only [Nat.floor_natCast] using hcredit.trans hg
  have hpow : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num only : 0 < (2 : ℕ)) _
  have hbN : 1 ≤ a * 2 ^ k := by nlinarith only [ha, hpow]
  have hbR : (1 : ℝ) ≤ (a * 2 ^ k : ℕ) := by exact_mod_cast hbN
  exact
    ⟨QNegOne_le_of_polynomial hGRH hB hx hbR hbx hp hdual hpoly,
      QNeOne_le_of_polynomial hGRH hB hx hbR hbx hp hdual hpoly⟩

end PseudoPrime.PseudoSquare
