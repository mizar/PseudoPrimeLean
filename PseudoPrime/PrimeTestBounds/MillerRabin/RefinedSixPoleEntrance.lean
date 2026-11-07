/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePiecewise

/-! # Entrance ranges for the refined piecewise residual -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `L ≥ 1000`, the selected paper root lies in the linear interval used by
the residual estimates. The three stated logarithmic entrances give the corresponding
numerical lower endpoints by the same root bound. -/
theorem refined_selected_entrance {L : ℝ} (hL : 1000 ≤ L) :
    (261 / 500 : ℝ) * L ≤ refinedPaperRoot L (refinedPaperAllowance L) ^ 2 ∧
      refinedPaperRoot L (refinedPaperAllowance L) ^ 2 ≤ (57 / 100 : ℝ) * L ∧
      (522 : ℝ) ≤ refinedPaperRoot L (refinedPaperAllowance L) ^ 2 ∧
      (3000 ≤ L → (1566 : ℝ) ≤ refinedPaperRoot L (refinedPaperAllowance L) ^ 2) ∧
      (10000 ≤ L → (5220 : ℝ) ≤ refinedPaperRoot L (refinedPaperAllowance L) ^ 2) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hK := refined_allowance_range L
  have hlo := refined_root_lower hL0 hK.1
  have hhi := refined_root_upper hL hK.1 hK.2
  refine ⟨hlo, hhi, ?_, ?_, ?_⟩
  · linarith only [hlo, hL]
  · intro h
    linarith only [hlo, h]
  · intro h
    linarith only [hlo, h]

/-- Three residual estimates on their respective half-lines imply the residual bound
at the root selected by the piecewise coefficient. Apply the root range and select the
appropriate allowance at each threshold. The three estimates remain explicit hypotheses. -/
theorem refined_selected_residual {L : ℝ} (hL : 1000 ≤ L)
    (h3 :
      ∀ (L R : ℝ),
        1000 ≤ L →
          (261 / 500 : ℝ) * L ≤ R →
          R ≤ (57 / 100 : ℝ) * L → refinedPaperResidual L R ≤ (27 / 25 : ℝ) ^ 5 * 3)
    (h1 :
      ∀ (L R : ℝ),
        3000 ≤ L →
          (261 / 500 : ℝ) * L ≤ R →
          R ≤ (57 / 100 : ℝ) * L → refinedPaperResidual L R ≤ (27 / 25 : ℝ) ^ 5 * 1)
    (h0 :
      ∀ (L R : ℝ),
        10000 ≤ L →
          (261 / 500 : ℝ) * L ≤ R →
          R ≤ (57 / 100 : ℝ) * L → refinedPaperResidual L R ≤ (27 / 25 : ℝ) ^ 5 * 0) :
    refinedPaperResidual L (refinedPaperRoot L (refinedPaperAllowance L) ^ 2) ≤
      (27 / 25 : ℝ) ^ 5 * refinedPaperAllowance L := by
  have h := refined_selected_entrance hL
  by_cases hl3 : L < 3000
  · have ha : refinedPaperAllowance L = 3 := by rw [refinedPaperAllowance, ite_eq_left hl3]
    rw [ha] at h ⊢
    exact h3 L _ hL h.1 h.2.1
  · have hl3' : 3000 ≤ L := le_of_not_gt hl3
    by_cases hl10 : L < 10000
    · have ha : refinedPaperAllowance L = 1 := by
        rw [refinedPaperAllowance, ite_eq_right hl3, ite_eq_left hl10]
      rw [ha] at h ⊢
      exact h1 L _ hl3' h.1 h.2.1
    · have hl10' : 10000 ≤ L := le_of_not_gt hl10
      have ha : refinedPaperAllowance L = 0 := by
        rw [refinedPaperAllowance, ite_eq_right hl3, ite_eq_right hl10]
      rw [ha] at h ⊢
      exact h0 L _ hl10' h.1 h.2.1

/-- The one-variable residual envelope obtained from the lower root constraint
`(261/500)L ≤ R`. It bounds the full residual because the only `L`-dependent
term has a nonnegative coefficient in the required range. -/
noncomputable def refinedResidualEnvelope (R : ℝ) : ℝ :=
  refinedPaperResidual ((500 / 261 : ℝ) * R) R

/-- For `R ≥ 522` and `(261/500)L ≤ R`, the actual scalar residual is at most
its one-variable envelope. Bound the conductor term using nonnegativity of its
kernel coefficient and leave every other term unchanged. -/
theorem refined_residual_le_envelope {L R : ℝ} (hR : 522 ≤ R) (hLR : (261 / 500 : ℝ) * L ≤ R) :
    refinedPaperResidual L R ≤ refinedResidualEnvelope R := by
  have hR1 : (1 : ℝ) ≤ R ^ 2 := by nlinarith only [hR]
  have hlog : 0 ≤ Real.log (R ^ 2) := Real.log_nonneg hR1
  have hc :
    0 ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
        (R ^ 2) ^ (-(27 / 25 : ℝ)) *
        ((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5) := by
    positivity
  have hL : L ≤ (500 / 261 : ℝ) * R := by linarith only [hLR]
  have hm :=
    mul_le_mul_of_nonneg_right (show 2 * L ≤ 2 * ((500 / 261 : ℝ) * R) by linarith only [hL]) hc
  dsimp only [refinedResidualEnvelope, refinedPaperResidual]
  linarith only [hm]

/-- Three one-variable envelope estimates at the numerical entrance radii imply
the selected residual certificate at the paper root. This reduces the remaining
half-line verification to radii at least `522`, `1566`, and `5220`. -/
theorem refined_selected_residual_of_envelopes {L : ℝ} (hL : 1000 ≤ L)
    (h3 : ∀ R : ℝ, 522 ≤ R → refinedResidualEnvelope R ≤ (27 / 25 : ℝ) ^ 5 * 3)
    (h1 : ∀ R : ℝ, 1566 ≤ R → refinedResidualEnvelope R ≤ (27 / 25 : ℝ) ^ 5 * 1)
    (h0 : ∀ R : ℝ, 5220 ≤ R → refinedResidualEnvelope R ≤ (27 / 25 : ℝ) ^ 5 * 0) :
    refinedPaperResidual L (refinedPaperRoot L (refinedPaperAllowance L) ^ 2) ≤
      (27 / 25 : ℝ) ^ 5 * refinedPaperAllowance L := by
  have h := refined_selected_entrance hL
  have hb := refined_residual_le_envelope h.2.2.1 h.1
  by_cases hl3 : L < 3000
  · have ha : refinedPaperAllowance L = 3 := by rw [refinedPaperAllowance, ite_eq_left hl3]
    rw [ha] at h hb ⊢
    exact hb.trans (h3 _ h.2.2.1)
  · have hl3' : 3000 ≤ L := le_of_not_gt hl3
    by_cases hl10 : L < 10000
    · have ha : refinedPaperAllowance L = 1 := by
        rw [refinedPaperAllowance, ite_eq_right hl3, ite_eq_left hl10]
      rw [ha] at h hb ⊢
      exact hb.trans (h1 _ (h.2.2.2.1 hl3'))
    · have hl10' : 10000 ≤ L := le_of_not_gt hl10
      have ha : refinedPaperAllowance L = 0 := by
        rw [refinedPaperAllowance, ite_eq_right hl3, ite_eq_right hl10]
      rw [ha] at h hb ⊢
      exact hb.trans (h0 _ (h.2.2.2.2 hl10'))

/-- Under GRH, the three one-variable envelope estimates imply the selected
piecewise witness bound for a uniform three-prime Korselt product. Transfer the
entrance certificates to the root and apply the conditional witness theorem. -/
theorem refined_pair_envelope_witness {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : 1000 ≤ Real.log n)
    (h3 : ∀ R : ℝ, 522 ≤ R → refinedResidualEnvelope R ≤ (27 / 25 : ℝ) ^ 5 * 3)
    (h1 : ∀ R : ℝ, 1566 ≤ R → refinedResidualEnvelope R ≤ (27 / 25 : ℝ) ^ 5 * 1)
    (h0 : ∀ R : ℝ, 5220 ≤ R → refinedResidualEnvelope R ≤ (27 / 25 : ℝ) ^ 5 * 0) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ refinedPaperCoefficient (Real.log n) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    refined_pair_piecewise_witness hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK
      hrK hvq hvr hL
  exact refined_selected_residual_of_envelopes hL h3 h1 h0

end PseudoPrime.PrimeTestBounds.MillerRabin
