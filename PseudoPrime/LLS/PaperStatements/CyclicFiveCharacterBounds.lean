/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.WeightedEndpointReduction
public import PseudoPrime.LLS.PaperStatements.WeightedCyclicEndpoints
public import PseudoPrime.NumberTheory.CharacterTracePenalty
public import PseudoPrime.NumberTheory.CharacterKernelPowers

/-! # The actual cyclic-five uniform endpoint

All nonprincipal powers of an order-five character have the same conductor. The generic
finite trace barrier forces penalty at least one quarter for every normalized weight
function with an actual trace certificate, and the uniform profile attains that penalty.
The actual principal-prefix comparison therefore reduces every such profile to the uniform
endpoint. The strict analytic gap remains explicit in the least-prime criteria.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The four nonprincipal powers selected for an order-five character family.
Input: a character; output: the finite image of positive exponents below five. Consuming
theorems impose exact order five, ensuring distinctness and nonprincipality.
This is the actual finite family used for uniform trace and conductor comparison. -/
noncomputable def cyclicFiveFamily {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Finset (DirichletCharacter ℂ q) :=
  letI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  (Finset.range 4).image (fun k : ℕ ↦ χ ^ (k + 1))

/-- The four selected positive powers are distinct at exact order five.
Input: exact order five. Use injectivity below the order and cancel successor exponents.
This validates actual family reindexing. -/
private theorem five_powers_inj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 5) : Set.InjOn (fun k : ℕ ↦ χ ^ (k + 1)) (Finset.range 4 : Set ℕ) :=
  fun _ hi _ hj he ↦
  Nat.succ_injective
    (pow_injOn_Iio_orderOf (ho.symm ▸ Nat.succ_lt_succ (Finset.mem_range.mp hi))
      (ho.symm ▸ Nat.succ_lt_succ (Finset.mem_range.mp hj)) he)

/-- A sum over the cyclic-five family expands into its four selected powers.
Input: exact order five and any additive summand. Reindex the injective power map and
expand the finite range. This supplies actual weight, cost and trace sums. -/
private theorem sum_five_family {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 5)
    {A : Type*} [AddCommMonoid A] (f : DirichletCharacter ℂ q → A) :
    (∑ ψ ∈ cyclicFiveFamily χ, f ψ) = f χ + f (χ ^ 2) + f (χ ^ 3) + f (χ ^ 4) := by
  classical
  rw [cyclicFiveFamily, Finset.sum_image (five_powers_inj χ ho)]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_one, zero_add]

/-- Every actual cyclic-five family member is nonprincipal.
Input: exact order five and family membership. A positive power below the order cannot
be one. This supplies both finite trace orthogonality and the analytic prime criterion. -/
private theorem five_family_nonprincipal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 5) : ∀ ψ ∈ cyclicFiveFamily χ, ψ ≠ 1 :=
  letI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  fun _ hψ ↦
  Exists.elim (Finset.mem_image.mp hψ) fun i hi ↦
    hi.2 ▸
      pow_ne_one_of_lt_orderOf (Nat.succ_ne_zero i)
        (ho.symm ▸ Nat.succ_lt_succ (Finset.mem_range.mp hi.1))

/-- Every selected cyclic-five power annihilates its generator's unit kernel.
Input: an actual family member. The kernel annihilator is the cyclic power subgroup.
This supplies the exact subgroup comparison for every normalized weight function. -/
private theorem five_family_annihilates {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∀ ψ ∈ cyclicFiveFamily χ, ψ ∈ NumberTheory.subgroupAnnihilator χ.toUnitHom.ker :=
  letI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  fun _ hψ ↦
  Exists.elim (Finset.mem_image.mp hψ) fun i hi ↦
    hi.2 ▸
      (NumberTheory.kernel_annihilator_zpowers χ).symm ▸
      (Subgroup.zpowers χ).pow_mem (Subgroup.mem_zpowers χ) (i + 1)

/-- Every normalized cyclic-five weight function has the generator conductor cost.
Input: exact order five and actual total weight one. Each nonprincipal exponent is coprime
to five, so its conductor equals the generator's. Expand the four weighted terms.
This proves that changing weights cannot save conductor cost. -/
theorem cyclic_five_weight_cost {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 5)
    (w : DirichletCharacter ℂ q → ℝ)
    (hW : NumberTheory.characterWeightTotal (cyclicFiveFamily χ) w = 1) :
    NumberTheory.weightedConductorLogSum (cyclicFiveFamily χ) w = Real.log χ.conductor := by
  have h2 :=
    NumberTheory.conductor_pow_coprime χ
      (ho.symm ▸ (show Nat.Coprime 2 5 from of_decide_eq_true rfl))
  have h3 :=
    NumberTheory.conductor_pow_coprime χ
      (ho.symm ▸ (show Nat.Coprime 3 5 from of_decide_eq_true rfl))
  have h4 :=
    NumberTheory.conductor_pow_coprime χ
      (ho.symm ▸ (show Nat.Coprime 4 5 from of_decide_eq_true rfl))
  have hn : w χ + w (χ ^ 2) + w (χ ^ 3) + w (χ ^ 4) = 1 := (sum_five_family χ ho w).symm.trans hW
  rw [NumberTheory.weightedConductorLogSum, sum_five_family χ ho, h2, h3, h4]
  nlinarith only [congrArg (fun v : ℝ ↦ v * Real.log χ.conductor) hn]

/-- Every normalized actual cyclic-five trace certificate has penalty at least one quarter.
Input: actual total one and a global trace lower bound. Apply the general finite Fourier
index barrier to the index-five kernel. No nonnegative-weight assumption is needed. -/
theorem cyclic_five_penalty {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 5)
    (w : DirichletCharacter ℂ q → ℝ)
    (hW : NumberTheory.characterWeightTotal (cyclicFiveFamily χ) w = 1) {m : ℝ}
    (htrace : ∀ z : ZMod q, -m ≤ NumberTheory.weightedCharacterTrace (cyclicFiveFamily χ) w z) :
    1 / 4 ≤ m := by
  have hb :=
    NumberTheory.normalized_trace_penalty χ.toUnitHom.ker (cyclicFiveFamily χ) w
      (five_family_nonprincipal χ ho) (five_family_annihilates χ) hW htrace
  rw [NumberTheory.index_kernel_eq_order, ho, Nat.cast_ofNat] at hb
  linarith only [hb]

/-- The four uniform weights of one quarter have total one.
Input: exact order five. Expand the actual four-character sum and evaluate its constants.
This certifies the normalization of the optimal endpoint profile. -/
theorem cyclic_five_uniform_total {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 5) :
    NumberTheory.characterWeightTotal (cyclicFiveFamily χ) (fun _ ↦ (1 / 4 : ℝ)) = 1 := by
  rw [NumberTheory.characterWeightTotal, sum_five_family χ ho]
  norm_num only

/-- A kernel-annihilator character sum has nonnegative real part at every unit.
Input: a character and unit. Subgroup orthogonality makes the sum either the subgroup
index or zero. This supplies the uniform trace bound without numerical sampling. -/
private theorem kernel_unit_sum_re_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (u : (ZMod q)ˣ) :
    0 ≤ (∑ ψ : NumberTheory.subgroupAnnihilator χ.toUnitHom.ker, ψ.val (u : ZMod q)).re :=
  Or.elim (Classical.em (u ∈ χ.toUnitHom.ker))
    (fun hu ↦
      (congrArg Complex.re
            (NumberTheory.sum_subgroupAnnihilator_eq_index χ.toUnitHom.ker hu)).symm ▸
        (show 0 ≤ (χ.toUnitHom.ker.index : ℝ) from Nat.cast_nonneg _))
    (fun hu ↦
      (congrArg Complex.re (NumberTheory.sum_subgroupAnnihilator_eq_zero χ.toUnitHom.ker hu)).symm ▸
        (le_refl (0 : ℝ)))

/-- The uniform cyclic-five trace is at least minus one quarter at every unit.
Input: exact order five and a unit. Expand the full cyclic annihilator sum, remove its
principal term and use its nonnegative real part. This certifies the optimal endpoint. -/
private theorem five_uniform_unit_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 5) (u : (ZMod q)ˣ) :
    -(1 / 4 : ℝ) ≤
      NumberTheory.weightedCharacterTrace (cyclicFiveFamily χ) (fun _ ↦ (1 / 4 : ℝ)) u := by
  have hp := NumberTheory.sum_kernel_characters χ (fun ψ : DirichletCharacter ℂ q ↦ ψ (u : ZMod q))
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ (χ ^ k) (u : ZMod q)) (orderOf χ), ho] at hp
  have hr := congrArg Complex.re hp
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    MulChar.one_apply_coe, Complex.add_re, Complex.one_re, zero_add] at hr
  rw [NumberTheory.weightedCharacterTrace, sum_five_family χ ho]
  nlinarith only [kernel_unit_sum_re_nonneg χ u, hr]

/-- The actual uniform cyclic-five trace has penalty one quarter on every residue.
Input: exact order five and any residue. Use subgroup orthogonality at units; nonunit
character values vanish. This supplies the proved trace certificate for the prime criterion. -/
theorem cyclic_five_uniform_trace {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ho : orderOf χ = 5) (z : ZMod q) :
    -(1 / 4 : ℝ) ≤
      NumberTheory.weightedCharacterTrace (cyclicFiveFamily χ) (fun _ ↦ (1 / 4 : ℝ)) z := by
  by_cases hu : IsUnit z
  · rcases hu with ⟨u, rfl⟩
    exact five_uniform_unit_lower χ ho u
  · rw [NumberTheory.weightedCharacterTrace, sum_five_family χ ho]
    norm_num only [χ.map_nonunit hu, (χ ^ 2).map_nonunit hu, (χ ^ 3).map_nonunit hu,
      (χ ^ 4).map_nonunit hu, Complex.zero_re, mul_zero, add_zero]

/-- The uniform endpoint dominates every normalized actual cyclic-five prefix deficit.
Input: any real normalized weights, an actual trace certificate and a positive scale.
The conductor cost is fixed, its penalty is at least one quarter, and the actual principal
tail is nonnegative. Thus continuous weight search cannot improve this common-kernel endpoint. -/
theorem cyclic_five_prefix_endpoint (K : MellinKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ho : orderOf χ = 5) (w : DirichletCharacter ℂ q → ℝ)
    (hW : NumberTheory.characterWeightTotal (cyclicFiveFamily χ) w = 1) {m x : ℝ}
    (htrace : ∀ z : ZMod q, -m ≤ NumberTheory.weightedCharacterTrace (cyclicFiveFamily χ) w z)
    (hx : 0 < x) (E : ℝ) (T : Finset ℕ) :
    let P := ∑ n ∈ T, (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
    let F := (∑' n : ℕ, MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
    K.mass * Real.log χ.conductor + E - P + (F - P) / 4 ≤
      K.mass * NumberTheory.weightedConductorLogSum (cyclicFiveFamily χ) w + E - P +
        m * (F - P) := by
  dsimp only
  rw [cyclic_five_weight_cost χ ho w hW]
  exact
    cyclic_five_endpoint (principal_tail_nonneg K (q := q) hx T)
      (cyclic_five_penalty χ ho w hW htrace)

/-- A negative uniform cyclic-five deficit yields an actual least outside prime under GRH.
Input: an order-five character and supported principal prefix. The four uniform weights
have total one, exact generator cost and proved penalty one quarter; apply the common
weighted criterion. Constants and thresholds are uniform and the strict gap remains explicit. -/
theorem cyclic_five_least_criterion (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ η : ℝ,
          0 < η →
            ∃ Q : ℕ,
              20000 ≤ Q ∧
                ∀ (q : ℕ) [NeZero q],
                  Q ≤ q →
                    ∀ χ : DirichletCharacter ℂ q,
                      orderOf χ = 5 →
                        ∀ X x : ℝ,
                          2 ≤ x →
                            ∀ T : Finset ℕ,
                              (∀ n ∈ T, (n : ℝ) ≤ X) →
                                let P :=
                                  ∑ n ∈ T,
                                    (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
                                let F :=
                                  (∑' n : ℕ,
                                      MellinKernel.summand K (1 : DirichletCharacter ℂ q) x n).re
                                let E :=
                                  η * Real.log q + C * (1 + Real.log q * Real.log x / Real.sqrt x)
                                K.mass * Real.log χ.conductor + E - P + (F - P) / 4 < 0 →
                                  ∃ p : ℕ,
                                    IsLeast (NumberTheory.primesOutside q χ.toUnitHom.ker) p ∧
                                      (p : ℝ) ≤ X := by
  obtain ⟨C, hC, hb⟩ := weighted_least_prime_criterion K hg
  refine ⟨C, hC, fun η hη ↦ ?_⟩
  obtain ⟨Q, hQ, hb⟩ := hb η hη
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq χ ho X x hx T hT P F E hgap
  apply
    hb q hq χ.toUnitHom.ker (cyclicFiveFamily χ) (fun _ ↦ (1 / 4 : ℝ)) (fun _ _ ↦ by norm_num only)
      (five_family_nonprincipal χ ho) (five_family_annihilates χ) (1 / 4) X x hx
      (cyclic_five_uniform_trace χ ho) T hT
  rw [cyclic_five_uniform_total χ ho, mul_one,
    cyclic_five_weight_cost χ ho (fun _ ↦ (1 / 4 : ℝ)) (cyclic_five_uniform_total χ ho)]
  change K.mass * Real.log χ.conductor + E < (1 + (1 / 4 : ℝ)) * P - (1 / 4 : ℝ) * F
  nlinarith only [hgap]

/-- Any normalized cyclic-five profile satisfying an actual strict gap gives a least prime.
Input: arbitrary real weights of total one, an actual trace certificate and supported prefix.
The uniform endpoint has no larger deficit, so apply its least-prime criterion. The proof
includes the weight optimization; no affine penalty hypothesis or conductor saving is assumed. -/
theorem cyclic_five_optimal_criterion (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ η : ℝ,
          0 < η →
            ∃ Q : ℕ,
              20000 ≤ Q ∧
                ∀ (q : ℕ) [NeZero q],
                  Q ≤ q →
                    ∀ χ : DirichletCharacter ℂ q,
                      orderOf χ = 5 →
                        ∀ w : DirichletCharacter ℂ q → ℝ,
                          NumberTheory.characterWeightTotal (cyclicFiveFamily χ) w = 1 →
                            ∀ m : ℝ,
                              (∀ z : ZMod q,
                                  -m ≤
                                    NumberTheory.weightedCharacterTrace (cyclicFiveFamily χ) w z) →
                                ∀ X x : ℝ,
                                  2 ≤ x →
                                    ∀ T : Finset ℕ,
                                      (∀ n ∈ T, (n : ℝ) ≤ X) →
                                        let P :=
                                          ∑ n ∈ T,
                                            (MellinKernel.summand K (1 : DirichletCharacter ℂ q) x
                                                n).re
                                        let F :=
                                          (∑' n : ℕ,
                                              MellinKernel.summand K (1 : DirichletCharacter ℂ q) x
                                                n).re
                                        let E :=
                                          η * Real.log q +
                                            C * (1 + Real.log q * Real.log x / Real.sqrt x)
                                        K.mass *
                                                    NumberTheory.weightedConductorLogSum
                                                      (cyclicFiveFamily χ) w +
                                                  E -
                                                P +
                                              m * (F - P) <
                                            0 →
                                          ∃ p : ℕ,
                                            IsLeast (NumberTheory.primesOutside q χ.toUnitHom.ker)
                                                p ∧
                                              (p : ℝ) ≤ X :=
  Exists.elim (cyclic_five_least_criterion K hg) fun C hC ↦
    ⟨C, hC.1, fun η hη ↦
      Exists.elim (hC.2 η hη) fun Q hQ ↦
        ⟨Q, hQ.1, fun q _ hq χ ho w hW _m htrace X x hx T hT hgap ↦
          hQ.2 q hq χ ho X x hx T hT
            ((cyclic_five_prefix_endpoint K χ ho w hW htrace
                  ((show (0 : ℝ) < 2 from zero_lt_two).trans_le hx)
                  (η * Real.log q + C * (1 + Real.log q * Real.log x / Real.sqrt x)) T).trans_lt
              hgap)⟩⟩

end PseudoPrime.LLS.PaperStatements
