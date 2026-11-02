/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.PartialCyclicConductorBounds
public import PseudoPrime.NumberTheory.SmallIndexCharacters
public import PseudoPrime.LLS.PaperStatements.ThreeConductorSum

/-! # Biquadratic conductor envelopes and arbitrary index-four subgroups

The three single-character bounds and the full-family bound refer to the same ambient
modulus. Their allowance remains proportional to the ambient log, including when some
primitive conductors are small. Finite duality also supplies a cyclic or biquadratic input
for every index-four subgroup; no CRT or primitivity hypothesis is imposed.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Kernel containment places a character in a subgroup annihilator.
Input: a subgroup inside the character's unit kernel. Convert unit equality to the defining
character-value equality. This supplies the actual biquadratic annihilator members. -/
private theorem annihilator_of_le_kernel {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (χ : DirichletCharacter ℂ q) (hH : H ≤ χ.toUnitHom.ker) :
    χ ∈ NumberTheory.subgroupAnnihilator H :=
  (NumberTheory.mem_subgroupAnnihilator_iff H χ).mpr fun u hu ↦
    (MulChar.coe_toUnitHom χ u).symm.trans (congrArg Units.val (MonoidHom.mem_ker.mp (hH hu)))

/-- Distinct quadratic characters have a quadratic product.
Input: two characters of order two and their distinctness. Their product squares to one;
a trivial product would identify them because a quadratic character is self-inverse.
This supplies the third nonprincipal character of a biquadratic quotient. -/
private theorem quadratic_product_order {q : ℕ} [NeZero q] (a b : DirichletCharacter ℂ q)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) : orderOf (a * b) = 2 :=
  let ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  let hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  orderOf_eq_prime_iff.mpr
    ⟨(mul_pow a b 2).trans ((congrArg₂ (fun u v ↦ u * v) ha2 hb2).trans (one_mul 1)), fun h ↦
      hab ((eq_inv_iff_mul_eq_one.mpr h).trans (eq_inv_iff_mul_eq_one.mpr (pow_two b ▸ hb2)).symm)⟩

/-- Three distinct nonprincipal annihilator members at index four give the full cost.
Input: membership, distinctness and the subgroup index. Reuse the existing exact enumeration
and expand its three terms. This isolates finite counting from conductor arithmetic. -/
private theorem three_log_cost {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (hi : H.index = 4)
    (a b c : NumberTheory.subgroupAnnihilator H) (ha : a ≠ 1) (hb : b ≠ 1) (hc : c ≠ 1)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    subgroupConductorLogSum H =
      Real.log a.val.conductor + Real.log b.val.conductor + Real.log c.val.conductor :=
  letI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  let hA : a ∉ ({b, c} : Finset (NumberTheory.subgroupAnnihilator H)) := fun h ↦
    Or.elim (Finset.mem_insert.mp h) hab (fun h' ↦ hac (Finset.mem_singleton.mp h'))
  let hB : b ∉ ({c} : Finset (NumberTheory.subgroupAnnihilator H)) := fun h ↦
    hbc (Finset.mem_singleton.mp h)
  let f : NumberTheory.subgroupAnnihilator H → ℝ := fun ψ ↦ Real.log ψ.val.conductor
  show (∑ ψ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H), f ψ) = f a + f b + f c
    from
    (nonprincipal_annihilator_eq_three_of_index_four H hi a b c ha hb hc hab hac hbc).symm ▸
      (Finset.sum_insert (f := f) hA).trans
        ((congrArg (fun v ↦ f a + v)
              ((Finset.sum_insert hB).trans
                (congrArg (fun v ↦ f b + v) (Finset.sum_singleton f c)))).trans
          (add_assoc (f a) (f b) (f c)).symm)

/-- The full biquadratic cost is the sum of its three nonprincipal conductor logs.
Input: distinct quadratic characters at one nonzero level. Their common kernel has index four.
The two characters and their product exhaust its nonprincipal annihilator by finite duality.
This supplies the full endpoint cost without a CRT or primitive-conductor assumption. -/
theorem biquadratic_kernel_conductor_sum {q : ℕ} [NeZero q] (a b : DirichletCharacter ℂ q)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) :
    subgroupConductorLogSum (a.toUnitHom.ker ⊓ b.toUnitHom.ker) =
      Real.log a.conductor + Real.log b.conductor + Real.log (a * b).conductor :=
  let H := a.toUnitHom.ker ⊓ b.toUnitHom.ker
  let A : NumberTheory.subgroupAnnihilator H := ⟨a, annihilator_of_le_kernel H a inf_le_left⟩
  let B : NumberTheory.subgroupAnnihilator H := ⟨b, annihilator_of_le_kernel H b inf_le_right⟩
  let ha1 : a ≠ 1 := (orderOf_eq_prime_iff.mp ha).2
  let hb1 : b ≠ 1 := (orderOf_eq_prime_iff.mp hb).2
  let hc1 : a * b ≠ 1 := (orderOf_eq_prime_iff.mp (quadratic_product_order a b ha hb hab)).2
  three_log_cost H (NumberTheory.quadratic_kernel_inf_index a b ha hb hab) A B (A * B)
    (fun h ↦ ha1 (congrArg Subtype.val h)) (fun h ↦ hb1 (congrArg Subtype.val h))
    (fun h ↦ hc1 (congrArg Subtype.val h)) (fun h ↦ hab (congrArg Subtype.val h))
    (fun h ↦ (left_ne_mul.mpr hb1) (congrArg Subtype.val h))
    (fun h ↦ (right_ne_mul.mpr ha1) (congrArg Subtype.val h))

/-- Under GRH, a biquadratic kernel satisfies all three single and full-family radii.
Input: distinct quadratic characters and positive ambient allowance. Substitute the exact
three-character conductor cost into the same-modulus least-prime minimum theorem.
The result certifies an actual least outside prime without assuming a scalar gap. -/
theorem biquadratic_min_radius (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ a b : DirichletCharacter ℂ q,
              orderOf a = 2 →
                orderOf b = 2 →
                a ≠ b →
                ∃ p : ℕ,
                  IsLeast (NumberTheory.primesOutside q (a.toUnitHom.ker ⊓ b.toUnitHom.ker)) p ∧
                    (p : ℝ) ≤
                      min
                        (min ((Real.sqrt (777 / 1000) * Real.log a.conductor + ε * Real.log q) ^ 2)
                          ((Real.sqrt (777 / 1000) * Real.log b.conductor + ε * Real.log q) ^ 2))
                        (min
                          ((Real.sqrt (777 / 1000) * Real.log (a * b).conductor + ε * Real.log q) ^
                            2)
                          ((Real.sqrt (623 / 1000) / ((4 : ℝ) - 1) *
                                (Real.log a.conductor + Real.log b.conductor +
                                  Real.log (a * b).conductor) +
                              ε * Real.log q) ^
                            2)) :=
  Exists.elim (quadratic_triple_full_radius hg hε) fun Q hQ ↦
    ⟨Q, hQ.1, fun q _ hq a b ha hb hab ↦
      let H := a.toUnitHom.ker ⊓ b.toUnitHom.ker
      let hA := annihilator_of_le_kernel H a inf_le_left
      let hB := annihilator_of_le_kernel H b inf_le_right
      biquadratic_kernel_conductor_sum a b ha hb hab ▸
        hQ.2 q hq H a b (a * b) (NumberTheory.quadratic_kernel_inf_index a b ha hb hab) ha hb
          (quadratic_product_order a b ha hb hab) inf_le_left inf_le_right
          (NumberTheory.le_kernel_of_annihilator H (a * b)
            ((NumberTheory.subgroupAnnihilator H).mul_mem hA hB))⟩

/-- Every index-four subgroup has a cyclic or biquadratic actual least-prime envelope.
Input: GRH, positive ambient allowance and any subgroup of index four. Classify its annihilator
at the same modulus and apply the corresponding exact conductor envelope. Take the maximum
of the two uniform thresholds. This exposes all partial-family branches for arbitrary subgroups. -/
theorem index_four_radius_cases (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ H : Subgroup (ZMod q)ˣ,
              H.index = 4 →
                (∃ χ : DirichletCharacter ℂ q,
                    orderOf χ = 4 ∧
                      H = χ.toUnitHom.ker ∧
                      ∃ p : ℕ,
                        IsLeast (NumberTheory.primesOutside q H) p ∧
                          (p : ℝ) ≤
                            min
                              ((Real.sqrt (777 / 1000) * Real.log (χ ^ 2).conductor +
                                  ε * Real.log q) ^
                                2)
                              ((Real.sqrt (623 / 1000) / ((4 : ℝ) - 1) *
                                    (2 * Real.log χ.conductor + Real.log (χ ^ 2).conductor) +
                                  ε * Real.log q) ^
                                2)) ∨
                  (∃ a b : DirichletCharacter ℂ q,
                    orderOf a = 2 ∧
                      orderOf b = 2 ∧
                      a ≠ b ∧
                      H = a.toUnitHom.ker ⊓ b.toUnitHom.ker ∧
                      ∃ p : ℕ,
                        IsLeast (NumberTheory.primesOutside q H) p ∧
                          (p : ℝ) ≤
                            min
                              (min
                                ((Real.sqrt (777 / 1000) * Real.log a.conductor + ε * Real.log q) ^
                                  2)
                                ((Real.sqrt (777 / 1000) * Real.log b.conductor + ε * Real.log q) ^
                                  2))
                              (min
                                ((Real.sqrt (777 / 1000) * Real.log (a * b).conductor +
                                    ε * Real.log q) ^
                                  2)
                                ((Real.sqrt (623 / 1000) / ((4 : ℝ) - 1) *
                                      (Real.log a.conductor + Real.log b.conductor +
                                        Real.log (a * b).conductor) +
                                    ε * Real.log q) ^
                                  2))) :=
  Exists.elim (cyclic_four_min_radius hg hε) fun Qc hc ↦
    Exists.elim (biquadratic_min_radius hg hε) fun Qb hb ↦
      ⟨max Qc Qb, hc.1.trans (le_max_left _ _), fun q _ hq H hi ↦
        Or.elim (NumberTheory.index_four_character_cases H hi)
          (fun h ↦
            Or.inl
              (Exists.elim h fun χ hχ ↦
                ⟨χ, hχ.1, hχ.2, hχ.2.symm ▸ hc.2 q ((le_max_left _ _).trans hq) χ hχ.1⟩))
          (fun h ↦
            Or.inr
              (Exists.elim h fun a ha ↦
                Exists.elim ha fun b hχ ↦
                  ⟨a, b, hχ.1, hχ.2.1, hχ.2.2.1, hχ.2.2.2,
                    hχ.2.2.2.symm ▸
                      hb.2 q ((le_max_right _ _).trans hq) a b hχ.1 hχ.2.1 hχ.2.2.1⟩))⟩

end PseudoPrime.LLS.PaperStatements
