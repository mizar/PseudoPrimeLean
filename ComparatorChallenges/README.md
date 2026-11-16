# Comparator challenges

Run the challenges from the project root with Lean 4.35's built-in comparator on Linux
with `bwrap` available. Each criterion and its solution repeat the same declarations in
separate modules. The comparator checks them in separate environments; the solution does not
import the criterion. The criterion's `sorry` declarations are comparison placeholders.

The allowed axioms are `propext`, `Quot.sound`, and `Classical.choice`. GRH is an explicit
assumption in the statement, not an allowed axiom. The configuration contains no definition
holes: the definitions used in the statement are part of the fixed challenge.

The stronger base-nine logarithm criterion has a separate challenge and solution:

```sh
lake comparator --config=ComparatorChallenges/PrimeMillerRabinWitness/PrimeMillerRabinWitnessCriterion.json
```

Its solution uses the base-nine and three-tenths rejecting-prime bounds and the four-ninths
prime acceptance result. The [slides](PrimeMillerRabinWitness/PrimeMillerRabinWitnessCriterion.md) display both criteria and GRH.
Each challenge and solution pair has its own namespace and repeats the GRH definitions locally.
Import `ComparatorChallenges` to use all completed solution modules together.

The two GRH-conditional odd-prime quadratic witness bounds use the same arrangement. Run both
comparisons together with:

```sh
lake comparator --config=ComparatorChallenges/PrimeQuadraticWitness/PrimeQuadraticWitnessCriterion.json
```

The solution applies `exists_prime_ne_one_witness_of_grh` in `PseudoSquare/Bounds/PointwiseWitness.lean`
and `exists_negOneWitness_le_refined_elementary` in `PseudoSquare/Bounds/RefinedElementaryBounds.lean`.
The first bound concerns a Jacobi symbol different from one for positive odd nonsquares; the second
concerns a symbol equal to negative one for odd nonsquares at least three. Both use the same explicit
GRH assumption and permitted axioms as the Miller–Rabin challenge.
The [quadratic witness slides](PrimeQuadraticWitness/PrimeQuadraticWitnessCriterion.md) show the statements and the
GRH definition used by the solution.

The extended LLS S1 subgroup bound and S2 nonprincipal-character bound are compared with:

```sh
lake comparator --config=ComparatorChallenges/LLSWitness/LLSWitnessCriterion.json
```

The S1 statement fixes the original correction term and starts at modulus three. The S2 statement
starts at modulus five, allows character value zero, and does not require the witness to be coprime
to the modulus. The [LLS slides](LLSWitness/LLSWitnessCriterion.md) display both statements and GRH.

The Chebyshev ψ and θ challenges are split by the status of their solutions. Compare the
completed ψ bounds and lower-endpoint counterexamples with:

```sh
lake comparator --config=ComparatorChallenges/Chebyshev/ChebyshevCriterion.json
```

The solution applies `psi_lee_nosal_of_RH` from
`PseudoPrime/AnalyticNumberTheory/RiemannZeta/ChebyshevPsiSign100RH.lean`.
The θ statement and other open challenges have separate criterion and solution files and
a separate comparison configuration:

```sh
lake comparator --config=ComparatorChallenges/Chebyshev/ChebyshevOpenCriterion.json
```

The Lee–Nosal θ bound assumes RH and holds for real `x ≥ 2657`; its solution remains `sorry`.
The same challenge also states the unconditional ψ error bound `4 / 5` on
`[1423, 36076580711678]` and a strict counterexample at `36076580711678.75`.
Their solution proofs remain `sorry`. The bound on `[1423, 1000000]` is stated separately
and proved using the existing finite certificate.
It also states the unconditional ψ error bound `81 / 100` on `[17, 36076729684088]`
and a strict counterexample at `36076729684088.75`; these proofs remain `sorry`.
The strict counterexamples at `1422.99` and `16.99` are in the completed files. Their proofs
use kernel-checked integer comparisons for least common multiples and rational analytic bounds.
The open challenges also include Büthe's unconditional bound
`|ψ(x) - x| / √x ≤ 47 / 50` for `11 ≤ x ≤ 10^19`.
