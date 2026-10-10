/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelAmbientZeroMass
public import PseudoPrime.LLS.SmoothedSubgroupBounds
public import PseudoPrime.LLS.MellinKernelPrimitiveComparison
public import PseudoPrime.LLS.MellinKernelPrincipalBounds

/-! # Preparatory bounds retaining individual conductors

The sharp primitive zero-mass estimate and the coarse estimate at bounded
conductors retain the exact leading term `K.mass * log m`, with an arbitrarily
small additive allowance in `log q`. A separate finite-sum lemma retains the
individual nonprincipal upper bounds in the subgroup annihilator average.
No complete conductor-sum kernel comparison or least-prime bound is asserted.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- Under GRH, for every positive ambient allowance, the absolute zero mass
of each primitive nonprincipal character of conductor `m` between two and `q`
is eventually at most `K.mass * log m + η * log q`, uniformly in the conductor
and character. For large `m`, use relative error `η / K.mass` in the sharp
bound. For bounded `m`, absorb the coarse bound into the ambient allowance.
The leading conductor term is retained even when `m` stays bounded. -/
theorem exists_uniform_kernelZeroSum_le_conductor_add_ambient (K : MellinKernel)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∀ η : ℝ,
      0 < η →
        ∃ Q : ℕ,
          2 ≤ Q ∧
            ∀ (q m : ℕ) [NeZero m],
              Q ≤ q →
                2 ≤ m →
                m ≤ q →
                ∀ (χ : DirichletCharacter ℂ m),
                  χ.IsPrimitive →
                    χ ≠ 1 →
                    χ⁻¹ ≠ 1 →
                    (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤ K.mass * Real.log m + η * Real.log q := by
  intro η hη
  have hM : 0 < K.mass := mass_pos K
  obtain ⟨N, _, hb⟩ := exists_uniform_kernelZeroSum_le_mass K hGRH (η / K.mass) (div_pos hη hM)
  obtain ⟨D, B, hD, _, hc⟩ := exists_uniform_kernelZeroSum_le_log_add K
  have hl :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      ((D * Real.log N + B) / η)
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hl
  refine ⟨max 2 R, Nat.le_max_left _ _, ?_⟩
  intro q m _ hq hm hmq χ hp hne hinv
  have hmp : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num only : 0 < 2) hm)
  have hmasslog : 0 ≤ K.mass * Real.log m := mul_nonneg hM.le (Real.log_natCast_nonneg m)
  by_cases hNm : N ≤ m
  · have hsharp := hb m hNm χ hp hne hinv
    have hfactor : (1 + η / K.mass) * K.mass = K.mass + η := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ hM.ne']
    rw [hfactor, add_mul] at hsharp
    have hlog :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hmp (show (m : ℝ) ≤ (q : ℝ) by exact_mod_cast hmq))
        hη.le
    exact hsharp.trans (add_le_add (le_refl (K.mass * Real.log m)) hlog)
  · have hmN : m ≤ N := Nat.le_of_not_ge hNm
    have hml :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hmp (show (m : ℝ) ≤ (N : ℝ) by exact_mod_cast hmN))
        hD
    have hsmall := hc m hm χ (hGRH m χ hp) hp hne hinv
    have hlarge := (div_le_iff₀ hη).mp (hR q ((Nat.le_max_right 2 R).trans hq))
    simp only [Function.comp_apply] at hlarge
    calc
      (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤ D * Real.log m + B := hsmall
      _ ≤ D * Real.log N + B := add_le_add hml (le_refl B)
      _ ≤ η * Real.log q := by simpa only [mul_comm] using hlarge
      _ ≤ K.mass * Real.log m + η * Real.log q := le_add_of_nonneg_left hmasslog

/-- A finite family with one distinguished main term and individual upper
bounds elsewhere has total at most the main term, the sum of the individual
bounds away from that point, and one error for every element. No positivity
of the individual bounds or common error is needed. -/
private theorem sum_le_of_distinguished_pointwise {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    (f B : ι → ℝ) {A E : ℝ} (ha : f a ≤ A + E) (hb : ∀ i, i ≠ a → f i ≤ B i + E) :
    ∑ i, f i ≤ A + (∑ i ∈ Finset.univ.erase a, B i) + (Fintype.card ι : ℝ) * E := by
  have he : (∑ i ∈ Finset.univ.erase a, f i) ≤ ∑ i ∈ Finset.univ.erase a, (B i + E) :=
    Finset.sum_le_sum (fun i hi ↦ hb i (Finset.mem_erase.mp hi).1)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at he
  have hcard : ((Finset.univ.erase a).card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
    simpa only [Nat.cast_one] using
      (Nat.cast_sub (R := ℝ)
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨a⟩))))
  rw [hcard] at he
  have hs := Finset.sum_erase_add (Finset.univ : Finset ι) f (Finset.mem_univ a)
  calc
    ∑ i, f i = (∑ i ∈ Finset.univ.erase a, f i) + f a := hs.symm
    _ ≤ (∑ i ∈ Finset.univ.erase a, B i) + ((Fintype.card ι : ℝ) - 1) * E + (A + E) :=
      add_le_add he ha
    _ = A + (∑ i ∈ Finset.univ.erase a, B i) + (Fintype.card ι : ℝ) * E := by ring

open Classical in
/-- Pointwise real upper bounds for smoothed character sums retain the sum
of the nonprincipal contributions in the annihilator average. The principal
bound has main term `A`; each of the `H.index` characters has common error `E`.
One may later take `A = Re K(1/2) * sqrt x` and let `B χ` depend on its conductor.
This lemma itself assumes only the stated scalar inequalities. -/
theorem average_le_of_pointwise_smoothed_estimates {q : ℕ} [NeZero q] (K : MellinKernel)
    (H : Subgroup (ZMod q)ˣ) (x A E : ℝ) (B : NumberTheory.subgroupAnnihilator H → ℝ)
    (hp : (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ q) x n).re ≤ A + E)
    (hn :
      ∀ χ : NumberTheory.subgroupAnnihilator H,
        χ.val ≠ 1 → (∑' n : ℕ, K.summand χ.val x n).re ≤ B χ + E) :
    ∑ χ : NumberTheory.subgroupAnnihilator H, (∑' n : ℕ, K.summand χ.val x n).re ≤
      A + (∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H), B χ) +
        (H.index : ℝ) * E := by
  classical
  have he :=
    sum_le_of_distinguished_pointwise (1 : NumberTheory.subgroupAnnihilator H)
      (fun χ ↦ (∑' n : ℕ, K.summand χ.val x n).re) B hp
      (fun χ hχ ↦ hn χ (fun heq ↦ hχ (Subtype.ext heq)))
  simpa only [NumberTheory.card_subgroupAnnihilator] using he

/-- Under GRH, retain the exact primitive conductor in each nonprincipal
smoothed character sum. The common remainder is uniform in the ambient level
and scale. Combine the primitive explicit formula with the additive ambient
zero-mass bound; its coefficient has absolute value at most one. -/
theorem exists_uniform_nonprincipal_summand_le_conductor (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ η : ℝ,
          0 < η →
            ∃ Q : ℕ,
              20000 ≤ Q ∧
                ∀ (q : ℕ) [NeZero q],
                  Q ≤ q →
                    ∀ (χ : DirichletCharacter ℂ q),
                      χ ≠ 1 →
                        ∀ (x : ℝ),
                          2 ≤ x →
                            (∑' n : ℕ, K.summand χ x n).re ≤
                              K.mass * Real.log χ.conductor + η * Real.log q +
                                C * (1 + Real.log q * Real.log x / Real.sqrt x) := by
  obtain ⟨C, hC, hf⟩ := exists_real_summand_formula_primitive_zeroMass K
  refine ⟨C, hC, ?_⟩
  intro η hη
  obtain ⟨Q, _, hz⟩ := exists_uniform_kernelZeroSum_le_conductor_add_ambient K hg η hη
  refine ⟨max 20000 Q, Nat.le_max_left _ _, ?_⟩
  intro q _ hq χ hχ x hx
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hn := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hχ
  have hm : 2 ≤ χ.conductor :=
    (by norm_num only : 2 ≤ 3).trans (NumberTheory.three_le_conductor_of_ne_one χ hχ)
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hb :=
    hz q χ.conductor ((Nat.le_max_right _ _).trans hq) hm hmq χ.primitiveCharacter
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hn (inv_ne_one.mpr hn)
  obtain ⟨θ, r, hθ, hr, he⟩ := hf ((Nat.le_max_left _ _).trans hq) χ hχ hg hx
  have hzero : 0 ≤ ∑' ρ : ℂ, ‖K.kernelZeroTerm χ.primitiveCharacter ρ‖ :=
    tsum_nonneg (fun _ ↦ norm_nonneg _)
  have ht := mul_le_mul_of_nonneg_right ((le_abs_self θ).trans hθ) hzero
  rw [one_mul] at ht
  rw [he]
  exact add_le_add (ht.trans hb) ((le_abs_self r).trans hr)

open Classical in
/-- The nonprincipal explicit estimates retain the sum of conductor logarithms
over the annihilator. A principal upper bound with the same common remainder
gives one remainder per character and one ambient allowance per nonprincipal
character. This is the conductor-sensitive upper side of the kernel comparison. -/
theorem exists_uniform_average_le_conductor_sum (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ η : ℝ,
          0 < η →
            ∃ Q : ℕ,
              20000 ≤ Q ∧
                ∀ (q : ℕ) [NeZero q],
                  Q ≤ q →
                    ∀ (H : Subgroup (ZMod q)ˣ) (x A : ℝ),
                      2 ≤ x →
                        (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ q) x n).re ≤
                          A + C * (1 + Real.log q * Real.log x / Real.sqrt x) →
                        ∑ χ : NumberTheory.subgroupAnnihilator H,
                            (∑' n : ℕ, K.summand χ.val x n).re ≤
                          A +
                            K.mass *
                              (∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
                                Real.log χ.val.conductor) +
                            ((H.index : ℝ) - 1) * (η * Real.log q) +
                            H.index * (C * (1 + Real.log q * Real.log x / Real.sqrt x)) := by
  classical
  obtain ⟨C, hC, hb⟩ := exists_uniform_nonprincipal_summand_le_conductor K hg
  refine ⟨C, hC, ?_⟩
  intro η hη
  obtain ⟨Q, hQ, hq⟩ := hb η hη
  refine ⟨Q, hQ, ?_⟩
  intro q _ hlevel H x A hx hp
  have hu :=
    average_le_of_pointwise_smoothed_estimates K H x A
      (C * (1 + Real.log q * Real.log x / Real.sqrt x))
      (fun χ ↦ K.mass * Real.log χ.val.conductor + η * Real.log q) hp
      (fun χ hχ ↦ hq q hlevel χ.val hχ x hx)
  have hcard :
    ((Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H)).card : ℝ) =
      (H.index : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨1⟩))),
      Nat.cast_one, NumberTheory.card_subgroupAnnihilator]
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcard,
    add_assoc, mul_left_comm] using hu

open Classical in
/-- Under GRH, the full annihilator average has an exact conductor-logarithm
main bound, one ambient allowance for each nonprincipal character, and a
uniform analytic remainder. The principal explicit formula supplies the main
term; the remaining character estimates retain their primitive conductors. -/
theorem exists_uniform_smoothed_average_le_conductor_sum (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ η : ℝ,
          0 < η →
            ∃ Q : ℕ,
              20000 ≤ Q ∧
                ∀ (q : ℕ) [NeZero q],
                  Q ≤ q →
                    ∀ (H : Subgroup (ZMod q)ˣ) (x : ℝ),
                      2 ≤ x →
                        ∑ χ : NumberTheory.subgroupAnnihilator H,
                            (∑' n : ℕ, K.summand χ.val x n).re ≤
                          (K.function (1 / 2)).re * Real.sqrt x +
                            K.mass *
                              (∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
                                Real.log χ.val.conductor) +
                            ((H.index : ℝ) - 1) * (η * Real.log q) +
                            H.index * (C * (1 + Real.log q * Real.log x / Real.sqrt x)) := by
  classical
  obtain ⟨Ca, hCa, ha⟩ := exists_uniform_average_le_conductor_sum K hg
  obtain ⟨Cp, hCp, hp⟩ := exists_principal_summand_remainder_le K hg.riemann
  refine ⟨Ca + Cp, add_pos hCa hCp, ?_⟩
  intro η hη
  obtain ⟨Q, hQ, hb⟩ := ha η hη
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq H x hx
  let V : ℝ := 1 + Real.log q * Real.log x / Real.sqrt x
  have hV : 0 ≤ V :=
    add_nonneg (by norm_num only)
      (div_nonneg
        (mul_nonneg (Real.log_natCast_nonneg q)
          (Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 2).trans hx)))
        (Real.sqrt_nonneg x))
  have hpr := (Complex.re_le_norm _).trans (hp (q := q) hx)
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero] at hpr
  have hu :=
    hb q hq H x ((K.function (1 / 2)).re * Real.sqrt x + Cp * V) hx
      (by
        dsimp only [V]; linarith only [hpr, mul_nonneg hCa.le hV])
  have he : (H.index : ℝ) * (Ca * V) + Cp * V ≤ (H.index : ℝ) * ((Ca + Cp) * V) := by
    have hh : (1 : ℝ) ≤ H.index := by
      rw [← NumberTheory.card_subgroupAnnihilator H]
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨1⟩
    have hs := mul_le_mul_of_nonneg_right hh (mul_nonneg hCp.le hV)
    nlinarith only [hs]
  dsimp only [V] at hu he
  linarith only [hu, he]

open Classical in
/-- If every eligible prime up to X lies in the subgroup, the finite principal
sum satisfies the conductor-sensitive averaged upper bound under GRH.
Combine the arithmetic orthogonality comparison with the proved full-series
estimate. This preserves the no-small-outside-prime hypothesis required to
turn the estimate into a cutting-point bound. -/
theorem exists_uniform_principal_sum_le_conductor_sum_of_noSmallPrimes (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ η : ℝ,
          0 < η →
            ∃ Q : ℕ,
              20000 ≤ Q ∧
                ∀ (q : ℕ) [NeZero q],
                  Q ≤ q →
                    ∀ (H : Subgroup (ZMod q)ˣ) (x X : ℝ),
                      2 ≤ x →
                        (∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) →
                        (H.index : ℝ) *
                            ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
                              (K.summand (1 : DirichletCharacter ℂ q) x n).re ≤
                          (K.function (1 / 2)).re * Real.sqrt x +
                            K.mass *
                              (∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
                                Real.log χ.val.conductor) +
                            ((H.index : ℝ) - 1) * (η * Real.log q) +
                            H.index * (C * (1 + Real.log q * Real.log x / Real.sqrt x)) := by
  obtain ⟨C, hC, ha⟩ := exists_uniform_smoothed_average_le_conductor_sum K hg
  refine ⟨C, hC, ?_⟩
  intro η hη
  obtain ⟨Q, hQ, hb⟩ := ha η hη
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq H x X hx hsmall
  exact
    (principal_sum_le_average_of_noSmallPrimes K H
          (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx) hsmall).trans
      (hb q hq H x hx)

end PseudoPrime.LLS.PaperStatements.MellinKernel
