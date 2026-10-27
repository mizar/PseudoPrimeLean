/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointCutoffMonotonicity
public import PseudoPrime.PseudoSquare.Bounds.ExcludedEndpointJacobi

/-! # Negative Jacobi witnesses after eliminating a fixed-cost cutoff search -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

open AnalyticNumberTheory.Arithmetic in
/-- For odd nonsquare n under GRH, costs valid at x and endpoint success at
some Y in [64,x] give an odd negative Jacobi prime through x, when the conductor
log is at least log pi. First replace Y by x using fixed-cost monotonicity.
The cost premises are at x; Y-dependent bounds must not be substituted here. -/
theorem exists_prime_neg_one_of_fixed_cost_cutoff_search {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x c D : ℝ} (hx : 64 ≤ x)
    (hc : 0 ≤ c)
    (hq : Real.log Real.pi ≤ Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor)
    (hC :
      excludedCharacterDefect (NumberTheory.primitiveQuadraticCharacter n hn) (4 * n)
          (Finset.Ioc 0 ⌊x⌋₊) (reciprocalWeightedMangoldtTerm x) ≤
        c)
    (hD :
      excludedCharacterDefect (NumberTheory.primitiveQuadraticCharacter n hn) (4 * n)
          (Finset.Ioc 0 ⌊x⌋₊) (logWeightedMangoldtTerm x) ≤
        D)
    (hsearch :
      ∃ Y : ℝ,
        64 ≤ Y ∧
          Y ≤ x ∧
          LLS.PaperStatements.oddEndpointTwoCostLimit
              (NumberTheory.complexQuadraticCharacter n hn).conductor x Y c D <
            0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p n ∧ jacobiSym n p = -1 := by
  have hlim :=
    (LLS.PaperStatements.oddEndpointTwoCostLimit_exists_cutoff_iff
          (NumberTheory.complexQuadraticCharacter n hn).conductor hq hx hc).mp
      hsearch
  exact
    exists_odd_prime_jacobi_neg_one_of_excluded_endpoint hn hns hGRH (by linarith only [hx]) hx
      le_rfl hC hD hlim

open AnalyticNumberTheory.Arithmetic in
/-- Under GRH, fixed uniform costs at x and a successful cutoff search at
level 4B bound the full negative-witness maximum by x. Eliminate the search
variable and invoke the uniform excluded-support consumer. The local bounds
cover every admissible n<=B and do not rely on finite input enumeration. -/
theorem QNegOne_le_of_fixed_cost_cutoff_search {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x c D : ℝ} (hx : 64 ≤ x)
    (hc : 0 ≤ c) (hq : Real.log Real.pi ≤ Real.log (4 * B : ℕ))
    (hlocal :
      ∀ n ∈ NumberTheory.admissibleFinset B,
        ∀ hn : Odd n,
          excludedCharacterDefect (NumberTheory.primitiveQuadraticCharacter n hn) (4 * n)
                (Finset.Ioc 0 ⌊x⌋₊) (reciprocalWeightedMangoldtTerm x) ≤
              c ∧
            excludedCharacterDefect (NumberTheory.primitiveQuadraticCharacter n hn) (4 * n)
                (Finset.Ioc 0 ⌊x⌋₊) (logWeightedMangoldtTerm x) ≤
              D)
    (hsearch :
      ∃ Y : ℝ, 64 ≤ Y ∧ Y ≤ x ∧ LLS.PaperStatements.oddEndpointTwoCostLimit (4 * B) x Y c D < 0) :
    (QNegOne B : ℝ) ≤ x := by
  have hlim :=
    (LLS.PaperStatements.oddEndpointTwoCostLimit_exists_cutoff_iff (4 * B) hq hx hc).mp hsearch
  exact QNegOne_cast_le_of_excluded_endpoint hGRH (by linarith only [hx]) hx le_rfl hlocal hlim

end PseudoPrime.PseudoSquare
