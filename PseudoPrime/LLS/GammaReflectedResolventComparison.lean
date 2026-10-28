/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaReflectedArchimedeanBounds
public import PseudoPrime.LLS.GammaSignedPrefixCharacterBounds
public import PseudoPrime.LLS.GammaConductorFreeSubgroupBounds

/-! # Reflected remainder bounds retaining the signed Euler prefix -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, primitive nonprincipal conductor 3<=m<=q, q>=20000 and x>=2,
the actual Gamma arithmetic sum is bounded by its signed resolvent mass,
pole and reflected tail. Retain the nonpositive conductor contribution
when combining the improved remainder with the oscillating-zero norm. -/
theorem gamma_sum_le_reflected_resolvent {q m : ℕ} [NeZero m] (hq : 20000 ≤ q) (hm : 3 ≤ m)
    (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            Analysis.gammaResolventMajorant ρ.im) +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        (35 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
        1 / (x * Real.sqrt x) := by
  have hr := re_gamma_primitive_remainder_le_reflected_split hq hm hmq hp hne hinv hGRH hx
  have hz :=
    norm_gamma_oscillatingZeroSum_le_resolvent (le_trans (by norm_num only : (2 : ℕ) ≤ 3) hm)
      (hGRH m χ hp) hp hne hinv (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx)
  have hn := Complex.re_le_norm (-(∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ))
  simp only [Complex.neg_re, norm_neg] at hn
  simp only [Complex.add_re] at hr
  have ha :=
    Analysis.gammaNegativeConductorTerm_nonpos (Real.log_natCast_nonneg m)
      (by linarith only [hx] : (0 : ℝ) < x)
  linarith only [hr, hz, hn, ha]

/-- Under GRH with ambient Q>=max(20000,q), x>=2 and prime triviality through
b>=0, combine a primitive signed Gamma-factor cap with the exact Euler prefix.
Transfer to the primitive conductor, cancel its prefix loss and retain the
reflected tail; no old contour-budget assumption is introduced. -/
theorem gamma_primitive_reflected_cap {q Q : ℕ} [NeZero q] (hQ : 20000 ≤ Q) (hqQ : q ≤ Q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 0 ≤ b) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → χ p = 1) {A : ℝ}
    (hgamma : gammaSignedGammaCost χ.primitiveCharacter.gammaFactor ≤ A) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log q + A +
            (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
        (35 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
        1 / (x * Real.sqrt x) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hz :=
    AnalyticNumberTheory.DirichletLFunction.gammaResolvent_zeroMass_le_signed_prefix
      (le_trans (by norm_num only : (2 : ℕ) ≤ 3) hm) (hGRH _ χ.primitiveCharacter hp) hp hnp
      (inv_ne_one.mpr hnp) (Finset.Ioc 0 ⌊b⌋₊)
  have he :=
    gamma_character_prefix_loss_eq_zero_of_prime_one χ.primitiveCharacter hb
      (fun p hp hpb ↦ primitiveCharacter_apply_one_of_apply_one χ (hsmall p hp hpb))
  rw [he, add_zero] at hz
  have hu :=
    gamma_sum_le_reflected_resolvent hQ hm (hmq.trans hqQ) hGRH hp hnp (inv_ne_one.mpr hnp) hx
  have hf : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hmqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hmq
  have hlead :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hf hmqR)
      (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  dsimp only [gammaSignedGammaCost] at hgamma
  linarith only [hz, hgamma, hu, hlead]

/-- For an even nonprincipal character under the reflected-prefix assumptions,
use the exact even Gamma-factor cost. Primitive normalization preserves evenness,
so the generic reflected cap applies without a parity maximum. -/
theorem gamma_even_reflected_prefix {q Q : ℕ} [NeZero q] (hQ : 20000 ≤ Q) (hqQ : q ≤ Q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 0 ≤ b) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → χ p = 1) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log q + gammaSignedGammaCost Complex.Gammaℝ +
            (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
        (35 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
        1 / (x * Real.sqrt x) := by
  have hp := (NumberTheory.primitiveCharacter_even_iff χ).mpr heven
  have hf : χ.primitiveCharacter.gammaFactor = Complex.Gammaℝ := funext hp.gammaFactor_def
  apply gamma_primitive_reflected_cap hQ hqQ χ hne hGRH hx hb hsmall
  rw [hf]

/-- Under GRH, x>=2 and prime membership through b>=0 in a subgroup whose
annihilator characters are even, bound the actual primitive average by its
exact principal sum plus the reflected common budget for the remaining
characters. This supplies the index-four MR comparison. -/
theorem gamma_even_reflected_average {q Q : ℕ} [NeZero q] (hQ : 20000 ≤ Q) (hqQ : q ≤ Q)
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (heven : ∀ χ : NumberTheory.subgroupAnnihilator H, χ.val.Even) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 0 ≤ b) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → residueInSubgroup q H p) :
    (∑ χ : NumberTheory.subgroupAnnihilator H,
        (∑' k : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x k).re) ≤
      (∑' k : ℕ, gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re +
        ((H.index : ℝ) - 1) *
          ((11783423 / 25000000 : ℝ) * Real.log q + gammaSignedGammaCost Complex.Gammaℝ +
                (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
              2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
            ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
            (35 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
            1 / (x * Real.sqrt x)) := by
  let F := fun χ : NumberTheory.subgroupAnnihilator H ↦
    (∑' k : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x k).re
  have h1 : F 1 ≤ (∑' k : ℕ, gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
    dsimp only [F]
    rw [Subgroup.coe_one,
      tsum_congr
        (MellinKernel.principal_primitive_summand_eq_level_one gammaMellinKernel (q := q) x)]
  have hrest :
    ∀ χ : NumberTheory.subgroupAnnihilator H,
      χ ≠ 1 →
        F χ ≤
          (11783423 / 25000000 : ℝ) * Real.log q + gammaSignedGammaCost Complex.Gammaℝ +
                (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
              2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
            ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
            (35 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
            1 / (x * Real.sqrt x) := by
    intro χ hχ
    exact
      gamma_even_reflected_prefix hQ hqQ χ.val (fun he ↦ hχ (Subtype.ext he)) (heven χ) hGRH hx hb
        (by
          intro p hp hpb
          obtain ⟨u, hu, he⟩ := hsmall p hp hpb
          rw [← he]
          exact (NumberTheory.mem_subgroupAnnihilator_iff H χ.val).mp χ.property u hu)
  have h := sum_le_distinguished_and_common (1 : NumberTheory.subgroupAnnihilator H) F h1 hrest
  rw [NumberTheory.card_subgroupAnnihilator] at h
  exact h

end PseudoPrime.LLS.PaperStatements
