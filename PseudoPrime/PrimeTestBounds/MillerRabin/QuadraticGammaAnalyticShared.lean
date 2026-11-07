/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaAnalytic100Witness

/-! # Shared analytic-cell inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every Euler prefix beginning at cutoff 3000 has the same certified
lower bound. Extend the checked finite prefix by nonnegative summands. This
allows all later analytic cells to reuse a single Euler certificate. -/
theorem gamma_euler_prefix_ge_47 {B : ℕ} (hB : 3000 ≤ B) :
    (47 / 10 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) B, Analysis.gammaResolventMangoldtWeight n := by
  apply gamma_analytic100_euler.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc le_rfl hB)
  intro n hn hnot
  exact Analysis.gammaResolventMangoldtWeight_nonneg n

/-- Under GRH, any analytic scale at least two and cutoff at least 142 satisfying the
Gamma gap and the `3/10` cutoff yield a rejecting prime for an odd composite.
Uniform Korselt triples use the Gamma transfer; the established nonuniform
case supplies the remaining inputs. This is the common witness interface for
all subsequent analytic cells. -/
theorem reject_03_of_gamma_gap {n B : ℕ} {x : ℝ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hx : 2 ≤ x) (hB : 142 ≤ B) (hcut : (B : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2)
    (hgap :
      (∑' k : ℕ, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) +
              2 * (11783423 / 25000000 : ℝ) * Real.log n -
            477 / 100 +
          ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
            4 * ∑ k ∈ Finset.Ioc (0 : ℕ) B, Analysis.gammaResolventMangoldtWeight k) +
          ((7 / 3 : ℝ) * Real.log n + 12) / Real.sqrt x +
          (105 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
          3 / (x * Real.sqrt x) <
        4 *
          ∑ k ∈ Finset.Ioc (0 : ℕ) B,
            Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · obtain ⟨l, hl, hb, hf⟩ :=
      uniformKorselt_reject_gamma hn ho hu hGRH (X := (B : ℝ)) (x := x) hx (Finset.Ioc 0 B)
        (by
          intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
        (by exact_mod_cast hB) hgap
    exact ⟨l, hl, hb.trans hcut, hf⟩
  · exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

/-- Under GRH, one analytic cell's scalar caps produce a rejecting prime
for any odd composite whose logarithm lies below the cell endpoint and whose
`3/10` cutoff contains the cell's finite prefix. The Euler lower bound and
its total-mass upper bound are shared by all cutoffs at least 3000. -/
theorem reject_03_of_analytic_caps {n B : ℕ} {x H R W F U : ℝ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8 : ℝ) ≤ Real.log n) (hx : 2 ≤ x) (hB : 3000 ≤ B)
    (hcut : (B : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2) (hR : 0 < R) (hRs : R ^ 2 ≤ x) (hH : 0 ≤ H)
    (hLH : Real.log n ≤ H) (hW : x ^ (-9 / 16 : ℝ) ≤ W)
    (hF :
      F ≤
        ∑ k ∈ Finset.Ioc (0 : ℕ) B,
          Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x)
    (hU : (∑' k : ℕ, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) ≤ U)
    (hnum :
      U + 2 * (11783423 / 25000000 : ℝ) * H - 477 / 100 + (3093 / 250 - 4 * (47 / 10)) +
          ((7 / 3 : ℝ) * H + 12) / R +
          (105 / 2 : ℝ) * W +
          3 / (x * R) <
        4 * F) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply reject_03_of_gamma_gap hn ho hc hGRH hL hx (le_trans (by decide : 142 ≤ 3000) hB) hcut
  exact
    gamma_gap_of_cell_caps (Finset.Ioc 0 B) x (Real.log n) H R W F U (47 / 10)
      (by linarith only [hx]) hR hRs hH hLH hW hF hU (gamma_euler_prefix_ge_47 hB)
      (euler_mass_le_12372 hGRH.riemann) hnum

/-- Under GRH, the first analytic certificate remains valid through 100.21.
The same finite cutoff and already checked scalar bounds extend the earlier
endpoint by direct arithmetic, with no new finite Euler evaluation. -/
theorem exists_reject_03_analytic10021 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (10021 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hprev : Real.log n ≤ (1001 / 10 : ℝ)
  · exact exists_reject_03_analytic100 hn ho hc hGRH hL hprev
  · have hlo : (100 : ℝ) ≤ Real.log n := by linarith only [le_of_not_ge hprev]
    have hcut : (3000 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
      nlinarith only [hlo, sq_nonneg (Real.log n - 100)]
    apply
      reject_03_of_analytic_caps (B := 3000) (x := 60000 / 37) (H := 10021 / 100) (R :=
        402693 / 10000) (W := 313 / 20000) (F := 32711 / 1000) (U := 813 / 20) hn ho hc hGRH hL
        (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
        hU gamma_analytic100_power (gamma_analytic100_main hGRH.riemann)
        (gamma_analytic100_principal hGRH.riemann)
    norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
