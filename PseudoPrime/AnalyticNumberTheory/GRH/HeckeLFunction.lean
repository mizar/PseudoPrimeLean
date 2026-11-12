/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.WeakFEPairSum
public import PseudoPrime.AnalyticNumberTheory.GRH.HeckeThetaPair
public import PseudoPrime.AnalyticNumberTheory.GRH.HeckeQuasiRiemannHypothesis

/-! # The Hecke lattice L-function and its quasi-Riemann hypothesis -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.GRH

/-- Form the weighted sum of the parity pairs for the lattice of period `N`.
The weights are indexed by the two residue coordinates and are repeated for
the two parity classes. -/
noncomputable def heckeLatticePair {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) : WeakFEPair ℂ :=
  Analysis.sumWeakFEPair
    (fun p : (Fin N × Fin N) × Fin 2 ↦
      heckeParityPair p.1.1 p.1.2 N (Nat.cast_pos.mpr (NeZero.pos N)) p.2)
    (fun p ↦ heckeParityPair_k _ _ _ _ p.2) (fun p ↦ w p.1)

/-- The completed lattice function associated to periodic weights `w` is the
Mellin continuation of their finite sum of theta pairs. -/
noncomputable def heckeLatticeCompleted {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) : ℂ → ℂ :=
  (heckeLatticePair w).Λ

/-- Remove the gamma and pi factors from the completed lattice function.
This is the lattice continuation used by the Hecke seven-eighths statement. -/
noncomputable def heckeLatticeL {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ * heckeLatticeCompleted w s

/-- The lattice L-function of the given Hecke character, normalized by the
six units of the third cyclotomic integer ring. -/
noncomputable def HeckeCharacter.LFunction (χ : HeckeCharacter) (s : ℂ) : ℂ :=
  heckeLatticeL χ.coefficients s / 6

/-- The seven-eighths nonvanishing assertion for the concrete Hecke lattice
L-function, with the principal-character point `s = 1` excluded. This is the
proposition stated in the HeckeSevenEighths comparator challenge. -/
def HeckeLQuasiRiemannHypothesis : Prop :=
  HeckeQuasiRiemannHypothesis HeckeCharacter.LFunction

end PseudoPrime.AnalyticNumberTheory.GRH
