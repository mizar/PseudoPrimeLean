/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaCharacterUpperBounds
public import PseudoPrime.LLS.GammaPrincipalUpperBounds
public import PseudoPrime.LLS.ConductorSumComparison

/-! # Numerical conductor-sensitive Gamma subgroup comparison

The signed primitive average and explicit principal/nonprincipal bounds give
a finite-cutoff contradiction inequality with every error constant specified.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH at level q≥20000 and scale x≥1, a primitive Gamma average
over a finite character subgroup has principal upper error 13x^(1/4),
leading conductor-log sum coefficient 11783423/25000000 and explicit error
39+(10002log(q)+10004)/sqrt(x) for each nonprincipal character.
Separate the identity and sum the individual numerical upper bounds. -/
private theorem gamma_primitive_average_re_le_explicit {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] [DecidableEq S]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    (∑ χ : S, ∑' n : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x n).re ≤
      Real.sqrt x + 13 * x ^ (1 / 4 : ℝ) +
        (11783423 / 25000000 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Fintype.card S - 1 : ℕ) : ℝ) * (39 + (10002 * Real.log q + 10004) / Real.sqrt x) := by
  classical
  let F := fun χ : S ↦ (∑' n : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x n).re
  have h1 : F 1 ≤ Real.sqrt x + 13 * x ^ (1 / 4 : ℝ) := by
    simpa only [F, Subgroup.coe_one] using
      gamma_primitive_principal_sum_upper_thirteen hGRH.riemann (zero_lt_one.trans_le hx)
  have hrest :
    ∑ χ ∈ Finset.univ.erase (1 : S), F χ ≤
      (11783423 / 25000000 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Finset.univ.erase (1 : S)).card : ℝ) *
          (39 + (10002 * Real.log q + 10004) / Real.sqrt x) := by
    calc
      _ ≤
          ∑ χ ∈ Finset.univ.erase (1 : S),
            ((11783423 / 25000000 : ℝ) * Real.log χ.val.conductor +
              (39 + (10002 * Real.log q + 10004) / Real.sqrt x)) :=
        by
        apply Finset.sum_le_sum
        intro χ hχ
        have hn : χ.val ≠ 1 := fun he ↦ (Finset.mem_erase.mp hχ).1 (Subtype.ext he)
        have h := gamma_primitiveCharacter_sum_re_le_explicit hq χ.val hn hGRH hx
        change F χ ≤ _ at h
        exact h.trans_eq (by ring)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : S)), Finset.card_univ] at hrest
  have he := Finset.sum_erase_eq_sub (f := F) (Finset.mem_univ (1 : S))
  change
    Complex.reCLM (∑ χ : S, ∑' n : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x n) ≤ _
  rw [map_sum]
  change (∑ χ : S, F χ) ≤ _
  linarith only [h1, hrest, he]

/-- If every eligible prime below X lies in H, GRH at q≥20000 and x≥1 bounds
the subgroup-index multiple of the principal finite Gamma sum by the numerical
primitive average, retaining the exact nonprincipal conductor-log sum.
Use the signed no-small-prime comparison and annihilator cardinality.
This is the analytic upper side of the finite-cutoff contradiction. -/
theorem gamma_principal_sum_le_conductor_bound_of_noSmallPrimes {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x X : ℝ} (hx : 1 ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re ≤
      Real.sqrt x + 13 * x ^ (1 / 4 : ℝ) + (11783423 / 25000000 : ℝ) * subgroupConductorLogSum H +
        ((H.index - 1 : ℕ) : ℝ) * (39 + (10002 * Real.log q + 10004) / Real.sqrt x) := by
  classical
  have hu := gamma_primitive_average_re_le_explicit hq (NumberTheory.subgroupAnnihilator H) hGRH hx
  rw [NumberTheory.card_subgroupAnnihilator] at hu
  change
    Complex.reCLM
        (∑ χ : NumberTheory.subgroupAnnihilator H,
          ∑' n : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x n) ≤
      _ at hu
  rw [map_sum] at hu
  exact
    (MellinKernel.principal_sum_le_primitive_average_of_noSmallPrimes gammaMellinKernel H
          (zero_lt_one.trans_le hx) hsmall).trans
      hu

/-- Under GRH and the no-small-prime condition at X=lambda*x, with q≥20000,
x≥1, lambda≥0 and X≥1, the displayed main-term coefficient times sqrt(x)
is bounded by the exact conductor cost and explicit numerical errors.
Combine the principal finite lower bound with the primitive-average upper
bound. The remaining modulus loss is stated explicitly for later local refinements. -/
theorem gamma_noSmallPrimes_explicit_inequality {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x lambda : ℝ} (hx : 1 ≤ x) (hl : 0 ≤ lambda) (hcut : 1 ≤ lambda * x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → residueInSubgroup q H p) :
    ((H.index : ℝ) * (1 - Real.exp (-lambda)) - 1) * Real.sqrt x ≤
      (11783423 / 25000000 : ℝ) * subgroupConductorLogSum H +
        13 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
        ((H.index - 1 : ℕ) : ℝ) * (39 + (10002 * Real.log q + 10004) / Real.sqrt x) +
        (H.index : ℝ) * (Real.log q * Real.log (lambda * x) / (Real.log 2 * Real.sqrt x)) := by
  have hlo :=
    gamma_principal_sum_lower_thirteen (q := q) hGRH.riemann (zero_lt_one.trans_le hx) hl hcut
  have hm := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg H.index)
  have hhi := gamma_principal_sum_le_conductor_bound_of_noSmallPrimes hq H hGRH hx hsmall
  have he : Finset.Icc 1 ⌊lambda * x⌋₊ = Finset.Ioc 0 ⌊lambda * x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  rw [he] at hhi
  nlinarith only [hm, hhi]

/-- Under GRH at q≥20000, x≥1 and lambda≥0, suppose every eligible prime
below lambda*x lies in H and every prime divisor exceeds its natural cutoff.
The main Gamma comparison then has no finite modulus-loss term.
Replace the principal finite sum by level one and combine its lower bound
with the conductor-sensitive primitive upper bound.
This is the numerical contradiction inequality for the Miller–Rabin branch. -/
theorem gamma_noSmallPrimes_explicit_inequality_of_no_small_divisor {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x lambda : ℝ} (hx : 1 ≤ x)
    (hl : 0 ≤ lambda) (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊lambda * x⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → residueInSubgroup q H p) :
    ((H.index : ℝ) * (1 - Real.exp (-lambda)) - 1) * Real.sqrt x ≤
      (11783423 / 25000000 : ℝ) * subgroupConductorLogSum H +
        13 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
        ((H.index - 1 : ℕ) : ℝ) * (39 + (10002 * Real.log q + 10004) / Real.sqrt x) := by
  have hlo := gamma_level_one_sum_lower_thirteen hGRH.riemann (zero_lt_one.trans_le hx) hl
  have hm := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg H.index)
  have hhi := gamma_principal_sum_le_conductor_bound_of_noSmallPrimes hq H hGRH hx hsmall
  have he : Finset.Icc 1 ⌊lambda * x⌋₊ = Finset.Ioc 0 ⌊lambda * x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  rw [he, ← Complex.re_sum,
    MellinKernel.principal_sum_eq_level_one_of_no_small_prime_divisor gammaMellinKernel (q := q) x
      hdiv,
    Complex.re_sum] at hhi
  nlinarith only [hm, hhi]

end PseudoPrime.LLS.PaperStatements
