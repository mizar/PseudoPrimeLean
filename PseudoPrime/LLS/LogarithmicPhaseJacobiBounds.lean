/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.LogarithmicPhaseCharacterBounds
public import PseudoPrime.LLS.Phase64JacobiLocalComparison

/-! # Jacobi witness extraction from a transported spectral anchor -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The original signed Jacobi prefix/local budget plus the explicit
scale-transport zero cost delta*(log(conductor)+76/5), pole and contour costs.
Inputs are actual Jacobi data, ambient modulus, target scale, prefix and anchor nodes.
The original Euler and local data are retained unchanged. -/
noncomputable def logarithmicPhaseJacobiLocalBudget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (q : ℕ) (x b : ℝ)
    (l : List (ℚ × ℚ)) (δ : ℚ) : ℝ :=
  AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget bridge.character l
        (Finset.Ioc 0 ⌊b⌋₊) -
      (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊,
        (1 - (bridge.character k).re) * Analysis.finiteSignedMangoldtWeight l k) +
    (∑ p ∈ (4 * n).primeFactors,
      Analysis.finiteSignedActualPrimeLocalCost l bridge.character p
        (AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b p) x) +
    (δ : ℝ) * (Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 76 / 5) +
    ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
    43 * x ^ (-9 / 16 : ℝ)

open AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH, admissible nonnegative anchor Euler weights and a proved
anchor phase majorant, absence of negative odd-prime witnesses through 99*x/40
forces ramp-minus-principal below the transported budget. Combine the transported
primitive-character bound with the exact ambient prime-prefix identity. -/
theorem jacobi_no_negative_logarithmic_phase_comparison {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x y b : ℝ} (hx : 2 ≤ x)
    (hy : 0 < y) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x) (l : List (ℚ × ℚ))
    (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) (δ : ℚ) (hd : |Real.log x - Real.log y| ≤ (δ : ℝ))
    (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ Analysis.finiteSignedEulerWeight l u)
    (hyphase :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (y : ℂ) ^ (Complex.I * t)).re ≤
          Analysis.finiteSignedResolvent l t)
    (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1) :
    2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re ≤
      logarithmicPhaseJacobiLocalBudget bridge q x b l δ := by
  let : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    ⟨(lt_of_lt_of_le (by norm_num only : (0 : ℕ) < 3) (gamma_jacobi_modulus_ge_three bridge)).ne'⟩
  have hinv : bridge.character⁻¹ ≠ 1 := by
    rw [bridge.character_quadratic.inv]
    exact bridge.character_ne_one
  have hc :=
    PaperStatements.gamma_primitive_sum_re_le_anchor_prefix hq
      (gamma_jacobi_modulus_ge_three bridge) hmq hGRH bridge.character_primitive
      bridge.character_ne_one hinv hx hy l hl δ hd hW (Finset.Ioc 0 ⌊b⌋₊) hyphase
  have ha := gamma_jacobi_no_negative_ramp_comparison bridge (by linarith only [hx]) hno
  have he :=
    finiteSigned_character_prefix_add_ambient_ramp_eq_local_cost l bridge.character
      (Nat.mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos) hb
      (gamma_jacobi_no_negative_prefix_prime_one bridge
        (fun p hp ho hpb ↦ hno p hp ho (hpb.trans hbx)))
      x
  dsimp only [logarithmicPhaseJacobiLocalBudget]
  linarith only [hc, ha, he]

/-- Under the transported-phase hypotheses, a strict gap between the explicit
local budget and the actual ramp-minus-principal quantity gives a negative odd-prime
Jacobi witness through 99*x/40. Contradict the proved no-witness comparison. -/
theorem exists_odd_prime_negative_of_logarithmic_phase_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x y b : ℝ} (hx : 2 ≤ x)
    (hy : 0 < y) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x) (l : List (ℚ × ℚ))
    (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) (δ : ℚ) (hd : |Real.log x - Real.log y| ≤ (δ : ℝ))
    (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ Analysis.finiteSignedEulerWeight l u)
    (hyphase :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (y : ℂ) ^ (Complex.I * t)).re ≤
          Analysis.finiteSignedResolvent l t)
    (hgap :
      logarithmicPhaseJacobiLocalBudget bridge q x b l δ <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  apply Classical.byContradiction
  intro h
  have hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1 :=
    fun p hp ho hpb hj ↦ h ⟨p, hp, ho, hpb, hj⟩
  exact
    (not_lt_of_ge
        (jacobi_no_negative_logarithmic_phase_comparison bridge hGRH hq hmq hx hy hb hbx l hl δ hd
          hW hyphase hno))
      hgap

/-- A known phase64 anchor in the certified first level cell transports to
any positive target scale with the displayed log-distance cap. Under GRH and a strict
transported-budget gap, obtain a negative odd-prime witness through 99*x/40.
The spectral comparison at the new scale needs no new grid certificate. -/
theorem exists_odd_prime_negative_of_transported_phase64_gap {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x b L : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x) (hlo : 64 ≤ L) (hhi : L ≤ 64001 / 1000) (δ : ℚ)
    (hd : |Real.log x - Real.log (L ^ 2 / (99 / 40))| ≤ (δ : ℝ))
    (hgap :
      logarithmicPhaseJacobiLocalBudget bridge q x b Analysis.phaseResolvent64Coefficients δ <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  have hl := (Analysis.finiteSignedPhaseNodeCheck_sound _ Analysis.phaseResolvent64_node_check).1
  have hy : (0 : ℝ) < L ^ 2 / (99 / 40) :=
    (by norm_num only : (0 : ℝ) < 163840 / 99).trans_le (Analysis.scale64_cell_of_level hlo hhi).1
  exact
    exists_odd_prime_negative_of_logarithmic_phase_gap bridge hGRH hq hmq hx hy hb hbx
      Analysis.phaseResolvent64Coefficients hl δ hd
      (fun u hu ↦ Analysis.phaseResolvent64_euler_nonneg hu)
      (fun t ↦ Analysis.phaseCell64_full_phase_of_level hlo hhi t) hgap

end PseudoPrime.LLS
