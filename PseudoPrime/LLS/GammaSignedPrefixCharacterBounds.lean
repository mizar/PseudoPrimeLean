/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeCharacterComparison
public import PseudoPrime.NumberTheory.DirichletCharacterParity

/-! # Signed Gamma parity and Euler-prefix character bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The signed Gamma-factor contribution of a complex function F at the fixed
resolvent nodes. Retain coefficient signs before taking the finite real sum.
Its use below is restricted to the even or odd archimedean Gamma factors. -/
noncomputable def gammaSignedGammaCost (F : ℂ → ℂ) : ℝ :=
  (Analysis.gammaResolventCoefficients.map
      (fun ab ↦ (ab.2 : ℝ) * (logDeriv F (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum

/-- The larger of the two exact signed Gamma costs for even and odd parity.
The finite expressions are retained without an absolute coefficient envelope.
It bounds every complex Dirichlet character's Gamma contribution. -/
noncomputable def gammaSignedParityUpper : ℝ :=
  max (gammaSignedGammaCost Complex.Gammaℝ)
    (gammaSignedGammaCost (fun z : ℂ ↦ Complex.Gammaℝ (z + 1)))

/-- The zero-mass upper budget with ambient level q and real prefix endpoint b.
It is M log q plus the exact parity upper bound and total nonnegative Euler
weight minus twice its finite prefix. The theorem below supplies the character
triviality assumptions needed to remove the prefix correction. -/
noncomputable def gammaSignedPrefixBudget (q : ℕ) (b : ℝ) : ℝ :=
  (11783423 / 25000000 : ℝ) * Real.log q + gammaSignedParityUpper +
      (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
    2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)

/-- Every Dirichlet Gamma factor is one of the two parity functions,
so its signed resolvent contribution is at most their exact maximum.
Use function equality before logarithmic differentiation. No RH is needed. -/
theorem gammaSignedGammaCost_le_parity_upper {q : ℕ} (χ : DirichletCharacter ℂ q) :
    gammaSignedGammaCost χ.gammaFactor ≤ gammaSignedParityUpper := by
  rcases χ.even_or_odd with he | ho
  · have hf : χ.gammaFactor = Complex.Gammaℝ := funext he.gammaFactor_def
    rw [hf]
    exact le_max_left _ _
  · have hf : χ.gammaFactor = (fun z : ℂ ↦ Complex.Gammaℝ (z + 1)) := funext ho.gammaFactor_def
    rw [hf]
    exact le_max_right _ _

/-- A character value one at a natural residue transfers to its primitive source.
Value one implies a unit at the original level, where induction agrees.
No primality or nonprincipal hypothesis is required. -/
theorem primitiveCharacter_apply_one_of_apply_one {q k : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ k = 1) : χ.primitiveCharacter k = 1 := by
  have hu : IsUnit (k : ZMod q) :=
    MulChar.apply_ne_zero_iff.mp
      (by
        rw [hχ]; exact one_ne_zero)
  have hc := (ZMod.isUnit_iff_coprime k q).mp hu
  have he := AnalyticNumberTheory.Arithmetic.apply_eq_primitiveCharacter_or_zero χ (n := k)
  rw [ite_eq_left hc] at he
  exact he.symm.trans hχ

/-- If a character is one at every prime through b ≥ 0, its nonnegative
Mangoldt-weighted prefix correction is zero. Zero Mangoldt terms vanish;
each remaining index is a prime power, whose character value is one.
This removes all prefix losses without dropping the signed common weight. -/
theorem gamma_character_prefix_loss_eq_zero_of_prime_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    {b : ℝ} (hb : 0 ≤ b) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → χ p = 1) :
    (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, (1 - (χ k).re) * Analysis.gammaResolventMangoldtWeight k) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hΛ : ArithmeticFunction.vonMangoldt k = 0
  · simp only [Analysis.gammaResolventMangoldtWeight, hΛ, zero_mul, mul_zero]
  · obtain ⟨p, r, hp, hr, rfl⟩ :=
      (isPrimePow_nat_iff (n := k)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hpb : (p : ℝ) ≤ b :=
      (show (p : ℝ) ≤ (p ^ r : ℕ) by exact_mod_cast Nat.le_pow hr).trans
        ((Nat.cast_le.mpr (Finset.mem_Ioc.mp hk).2).trans (Nat.floor_le hb))
    simp only [Nat.cast_pow, map_pow, hsmall p hp hpb, one_pow, Complex.one_re, sub_self, zero_mul]

/-- Any certified upper cap A for the primitive signed Gamma-factor cost can
be combined with prime triviality, the common Euler prefix and the signed remainder.
The ambient pole level Q is independent of the original level q.
This is the parity-independent common implementation for sharper parity caps. -/
theorem gamma_primitiveCharacter_sum_re_le_signed_prefix_gamma_cap {q Q : ℕ} [NeZero q]
    (hQ : 20000 ≤ Q) (hqQ : q ≤ Q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 0 ≤ b) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → χ p = 1) {A : ℝ}
    (hgamma : gammaSignedGammaCost χ.primitiveCharacter.gammaFactor ≤ A) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log q + A +
            (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
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
    gamma_primitive_sum_re_le_resolvent_conductor_free hQ hm (hmq.trans hqQ) hGRH hp hnp
      (inv_ne_one.mpr hnp) hx
  have hf : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hmqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hmq
  have hlead :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hf hmqR)
      (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  dsimp only [gammaSignedGammaCost] at hgamma
  linarith only [hz, hgamma, hu, hlead]

/-- With nonprincipal level q, independent ambient pole level Q ≥ max(20000,q),
GRH, x ≥ 2 and prime triviality through b ≥ 0, the signed prefix budget
retains log q while the pole uses log Q. This includes small original levels.
Apply the actual primitive-conductor bound at Q before prefix cancellation. -/
theorem gamma_primitiveCharacter_sum_re_le_signed_prime_prefix_ambient {q Q : ℕ} [NeZero q]
    (hQ : 20000 ≤ Q) (hqQ : q ≤ Q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 0 ≤ b) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → χ p = 1) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      gammaSignedPrefixBudget q b + ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  simpa only [gammaSignedPrefixBudget] using
    gamma_primitiveCharacter_sum_re_le_signed_prefix_gamma_cap hQ hqQ χ hne hGRH hx hb hsmall
      (gammaSignedGammaCost_le_parity_upper χ.primitiveCharacter)

/-- Under GRH for nonprincipal q ≥ 20000 and x ≥ 2, if all primes through b ≥ 0
have character value one, the primitive Gamma arithmetic sum is bounded by the
signed parity/Euler-prefix budget plus the pole and conductor-free left costs.
Transfer to the primitive character, cancel its prefix loss exactly, and apply
the actual resolvent zero bound. No logarithmic lower entrance is imposed. -/
theorem gamma_primitiveCharacter_sum_re_le_signed_prime_prefix {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 0 ≤ b) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → χ p = 1) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      gammaSignedPrefixBudget q b + ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  exact
    gamma_primitiveCharacter_sum_re_le_signed_prime_prefix_ambient hq (le_refl _) χ hne hGRH hx hb
      hsmall

/-- For an even nonprincipal character, use the exact even signed Gamma cost
instead of the parity maximum in the arbitrary-scale prefix comparison.
Primitive normalization preserves evenness, and equality of Gamma factors
supplies the generic cap. This sharper bound is used by Miller-Rabin annihilators. -/
theorem gamma_primitiveCharacter_sum_re_le_even_signed_prime_prefix {q Q : ℕ} [NeZero q]
    (hQ : 20000 ≤ Q) (hqQ : q ≤ Q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 0 ≤ b) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → χ p = 1) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log q + gammaSignedGammaCost Complex.Gammaℝ +
            (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hp := (NumberTheory.primitiveCharacter_even_iff χ).mpr heven
  have hf : χ.primitiveCharacter.gammaFactor = Complex.Gammaℝ := funext hp.gammaFactor_def
  apply gamma_primitiveCharacter_sum_re_le_signed_prefix_gamma_cap hQ hqQ χ hne hGRH hx hb hsmall
  rw [hf]

end PseudoPrime.LLS.PaperStatements
