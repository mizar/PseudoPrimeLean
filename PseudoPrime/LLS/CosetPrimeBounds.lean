/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements
public import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Least primes in reduced residue classes and subgroup cosets

Dirichlet's theorem supplies existence without GRH. Minimization transfers any
quantitative witness bound to the least prime required in the paper statements.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A prime in the residue class of a unit also lies in its coset of any subgroup.
Use the unit itself as witness and the subgroup identity. This transfers residue-class
existence to the coset formulation of Theorem 1.4. -/
theorem mem_primesInCoset_of_eq {q : ℕ} (H : Subgroup (ZMod q)ˣ) (a : (ZMod q)ˣ) {p : ℕ}
    (hp : p.Prime) (ha : (p : ZMod q) = (a : ZMod q)) : p ∈ primesInCoset q H a := by
  exact ⟨hp, a, inv_mul_cancel a ▸ H.one_mem, ha.symm⟩

/-- For a nonzero modulus, every unit residue class contains a least prime.
Dirichlet's theorem provides a prime and natural-number minimization provides the least
one. This discharges the existence component of Corollary 1.2 without GRH. -/
theorem exists_least_prime_in_residue {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) :
    ∃ p : ℕ, IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p := by
  classical
  obtain ⟨p, _, hp⟩ := Nat.forall_exists_prime_gt_and_eq_mod a.isUnit 0
  have hex : ∃ r : ℕ, r.Prime ∧ (r : ZMod q) = (a : ZMod q) := ⟨p, hp⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun _ hr ↦ Nat.find_min' hex hr⟩

/-- For a nonzero modulus, every coset of a subgroup of units contains a least prime.
Apply Dirichlet's theorem to its representative, then minimize the coset prime set.
This establishes existence in Theorem 1.4 independently of its quantitative bound. -/
theorem exists_least_prime_in_coset {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (a : (ZMod q)ˣ) :
    ∃ p : ℕ, IsLeast (primesInCoset q H a) p := by
  classical
  obtain ⟨p, _, hp, ha⟩ := Nat.forall_exists_prime_gt_and_eq_mod a.isUnit 0
  have hex : ∃ r : ℕ, r ∈ primesInCoset q H a := ⟨p, mem_primesInCoset_of_eq H a hp ha⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun _ hr ↦ Nat.find_min' hex hr⟩

/-- For a nonzero modulus, a bounded prime witness in a unit residue class bounds
its least prime. Combine unconditional existence with the least-element inequality.
This reduces the quantitative part of Corollary 1.2 to a witness estimate. -/
theorem exists_least_prime_in_residue_le {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) {B : ℝ}
    (hb : ∃ r : ℕ, r.Prime ∧ (r : ZMod q) = (a : ZMod q) ∧ (r : ℝ) ≤ B) :
    ∃ p : ℕ, IsLeast {r : ℕ | r.Prime ∧ (r : ZMod q) = (a : ZMod q)} p ∧ (p : ℝ) ≤ B := by
  obtain ⟨p, hp⟩ := exists_least_prime_in_residue a
  obtain ⟨r, hr, ha, hB⟩ := hb
  exact ⟨p, hp, (Nat.cast_le.mpr (hp.2 ⟨hr, ha⟩)).trans hB⟩

/-- For a nonzero modulus, a coset prime below either of two real bounds gives
the same alternative for the least coset prime. Minimize using Dirichlet existence
and transfer the witness bound. This preserves the alternative in Theorem 1.4. -/
theorem exists_least_prime_in_coset_le_or {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (a : (ZMod q)ˣ) {A B : ℝ}
    (hb : ∃ r : ℕ, r ∈ primesInCoset q H a ∧ ((r : ℝ) ≤ A ∨ (r : ℝ) ≤ B)) :
    ∃ p : ℕ, IsLeast (primesInCoset q H a) p ∧ ((p : ℝ) ≤ A ∨ (p : ℝ) ≤ B) := by
  obtain ⟨p, hp⟩ := exists_least_prime_in_coset H a
  obtain ⟨r, hr, hB⟩ := hb
  exact ⟨p, hp, hB.imp ((Nat.cast_le.mpr (hp.2 hr)).trans) ((Nat.cast_le.mpr (hp.2 hr)).trans)⟩

/-- For a nonzero modulus every proper subgroup has a least eligible prime outside it.
Choose a unit outside the subgroup and apply Dirichlet's theorem to its residue class.
Natural-number minimization then preserves minimality among all eligible primes.
This supplies unconditional existence for the theoretical prime bounds. -/
theorem exists_least_prime_outside {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ, IsLeast (primesOutside q H) p := by
  classical
  have hexu : ∃ u : (ZMod q)ˣ, u ∉ H := by
    by_contra hn
    apply hH
    apply le_antisymm le_top
    intro u _
    by_contra hu
    exact hn ⟨u, hu⟩
  obtain ⟨u, hu⟩ := hexu
  obtain ⟨p, _, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod u.isUnit 0
  have hunit : IsUnit (p : ZMod q) := by
    rw [hpa]; exact u.isUnit
  have hcop := (ZMod.isUnit_iff_coprime p q).mp hunit
  have hmem : p ∈ primesOutside q H := by
    refine ⟨hp, hp.coprime_iff_not_dvd.mp hcop, ?_⟩
    rintro ⟨v, hv, hvp⟩
    have he : v = u := Units.val_injective (hvp.trans hpa)
    exact hu (he ▸ hv)
  have hex : ∃ p : ℕ, p ∈ primesOutside q H := ⟨p, hmem⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun _ hr ↦ Nat.find_min' hex hr⟩

/-- For a proper subgroup, a nonnegative uniform cutoff bound transfers
 to its least outside prime. Dirichlet's theorem supplies the least prime;
 if it exceeded the bound, the midpoint would have all eligible primes
 inside the subgroup and contradict the cutoff inequality.
 This turns Mellin-kernel endpoint bounds into prime bounds. -/
theorem exists_least_prime_outside_le_of_cutoff_bound {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) {A : ℝ} (hA : 0 ≤ A)
    (hc :
      ∀ X : ℝ,
        0 < X → (∀ r : ℕ, r.Prime → ¬r ∣ q → (r : ℝ) ≤ X → residueInSubgroup q H r) → X ≤ A) :
    ∃ p : ℕ, IsLeast (primesOutside q H) p ∧ (p : ℝ) ≤ A := by
  obtain ⟨p, hp⟩ := exists_least_prime_outside H hH
  refine ⟨p, hp, ?_⟩
  by_contra hn
  have hAp : A < (p : ℝ) := lt_of_not_ge hn
  let X := (A + (p : ℝ)) / 2
  have hX : 0 < X := by
    dsimp only [X]; linarith only [hA, hAp]
  have hXp : X < (p : ℝ) := by
    dsimp only [X]; linarith only [hAp]
  have hAX : A < X := by
    dsimp only [X]; linarith only [hAp]
  have hpr : ∀ r : ℕ, r.Prime → ¬r ∣ q → (r : ℝ) ≤ X → residueInSubgroup q H r := by
    intro r hr hrd hrX
    by_contra hrH
    have hmin : p ≤ r := hp.2 ⟨hr, hrd, hrH⟩
    have hminR : (p : ℝ) ≤ r := by exact_mod_cast hmin
    exact (not_le_of_gt hXp) (hminR.trans hrX)
  exact (not_lt_of_ge (hc X hX hpr)) hAX

/-- For moduli between one and a fixed bound, there is a common bound on
the least prime outside every proper subgroup. Choose the least primes using
Dirichlet existence and take a maximum over the finite family of moduli and
subgroups. No explicit prime table or numerical enumeration is required.
This handles reduced moduli below an analytic threshold. -/
theorem exists_uniform_least_prime_bound_of_modulus_le (Q : ℕ) :
    ∃ B : ℕ,
      ∀ (m : ℕ) [NeZero m],
        m ≤ Q →
          ∀ H : Subgroup (ZMod m)ˣ, H ≠ ⊤ → ∃ p : ℕ, IsLeast (primesOutside m H) p ∧ p ≤ B := by
  classical
  let I := Σ q : Fin Q, { H : Subgroup (ZMod (q.val + 1))ˣ // H ≠ ⊤ }
  have hex (i : I) : ∃ p : ℕ, IsLeast (primesOutside (i.1.val + 1) i.2.val) p :=
    exists_least_prime_outside i.2.val i.2.property
  let f : I → ℕ := fun i ↦ Classical.choose (hex i)
  refine ⟨Finset.univ.sup f, ?_⟩
  intro m _ hm H hH
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  let i : I := ⟨⟨n, Nat.lt_of_succ_le hm⟩, ⟨H, hH⟩⟩
  exact ⟨f i, Classical.choose_spec (hex i), Finset.le_sup (Finset.mem_univ i)⟩

end PseudoPrime.LLS.PaperStatements
