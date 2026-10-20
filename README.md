# Lean code corresponding to work on SSP bounds for Runge–Kutta methods

## paper: A stability order barrier and SSP bound for Runge–Kutta methods
with non-negative coefficients: AI assisted proofs

---

## Installing Lean and building the code

### Prerequisites

This project uses **Lean 4** (`leanprover/lean4:v4.32.0-rc1`) and depends on
[Mathlib](https://github.com/leanprover-community/mathlib4).  The recommended
way to install Lean is via **elan**, the Lean version manager.

#### Install elan

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Follow the on-screen prompts, then open a new shell (or run `source ~/.profile`)
so that `elan` and `lake` are on your `PATH`.

The correct Lean version is pinned in `lean-toolchain`; elan will download it
automatically the first time you build.

### Building

```bash
# Clone the repository (if you haven't already)
git clone <repo-url>
cd Lean-Files

# Download Mathlib and all other dependencies
lake exe cache get

# Build the project
LEAN_NUM_THREADS=1 lake build
```

`lake exe cache get` fetches pre-compiled Mathlib `.olean` files so you do not
have to recompile Mathlib from source (which can take hours).

We suggest setting `LEAN_NUM_THREADS=1` when building, as building some files requires lots of memory and using the default parallel build may cause your machine to run out of memory.


### Editor support

[VS Code](https://code.visualstudio.com/) with the
[lean4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
is the most common editor setup.  The extension calls `elan` and `lake`
automatically, so opening the repository folder is sufficient to get
interactive proof checking.

Emacs users can use [lean4-mode](https://github.com/leanprover/lean4-mode).

## Short renewal proof of Conjecture 1 at k = 2

The improved proof in `phase_type_moment_inequality.tex` is formalized in:

- `SSPLean/K2ShortQuadratic.lean`: the two-variable quadratic lemma, its convex
  quadrant reduction, terminal-edge threshold, and the exceptional cases
  `n = 2, 3, 4`.
- `SSPLean/K2ShortRenewal.lean`: the compact renewal identities, normalization,
  and the improved renewal inequality. The return second moment only needs
  nonnegativity; its Aldous--Shepp lower bound is not used. Both zero-return
  probability and zero terminal mean are included.
- `SSPLean/K2ShortProof.lean`: the concrete conditioned-excursion construction
  for every `n ≥ 2`, strong induction starting only at `n = 1`, mixture closure,
  the ratio form of Conjecture 1, and Erlang/atom-at-zero sharpness.

The main theorem is `SSP.K2Concrete.all_transient_initial_laws_short`:
`(s + 2) m₂² ≤ (s + 1) m₁ m₃` for every finite transient substochastic model
with a subprobability initial vector. Cycles and missing initial mass at zero
are allowed. `SSP.K2Concrete.conjecture_one_k2_short` gives the corresponding
ratio inequality for positive mean. `all_absorption_initial_laws_short` gives
the result for the repository's concrete absorption-time measure moments.
These theorems have no canonical-representation or renewal-certificate premise.
The general transient chart defines raw moments by their standard resolvent
formulas; the concrete absorption chart identifies them with measure integrals.
Sharpness is proved; this new proof does not add a distribution-level equality
classification beyond the sharpness statement in the source paper.

`SSP.MainRevised.hierarchy_k2` now uses this shorter proof, so
`SSP.MainRevised.order3_bound_unconditional` derives
`r ≤ s - 1 + sqrt (s² - 1)` through the improved argument.
The older direct proof remains available in `K2S3Direct.lean`.

To build and inspect the theorem dependencies:

```bash
lake build SSPLean.K2ShortProof SSPLean.MainRevised
lake env lean CheckK2Short.lean
```

The axiom audit checks the quadratic, normalization, concrete induction,
sharpness, conjecture, and matrix-bound endpoints. Only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` axioms are used.

## Two-by-two matrix conjecture

`SSPLean/MatrixTwoLogConvex.lean` proves Conjecture 2 (the matrix statement) for every entrywise
nonnegative real `2 × 2` matrix and nonnegative endpoint vectors. The theorem
`SSP.MatrixTwo.conjecture_two_two_by_two` states convexity of
`log (uᵀ exp(tA) v / t)` on positive times when the pairing is not identically
zero. `scalar_pos` establishes the required positivity; `matrix_curvature_nonneg`
proves the corrected curvature inequality even for the identically zero pairing.
The implication from this matrix statement to Conjecture 1's all-`k`
phase-type moment inequality is now formalized in
`SSPLean/MatrixMomentReduction.lean`, with the analytic step in
`SSPLean/LogConvexMomentReduction.lean`.

The module can be checked directly, without building the entire project:

```bash
lake env lean SSPLean/MatrixTwoLogConvex.lean
```

## Conjecture 2 implies the moment inequality of Conjecture 1

`SSP.MatrixMomentReduction.matrixConjecture_implies_momentConjecture` proves
this implication at every positive state dimension. It covers every `k ≥ 1`,
cyclic chains, zero scalar pairings, and a nonnegative atom at zero.
`SSP.MatrixMomentReduction.momentConjecture_two` combines the implication
with the two-by-two matrix proof and has no conjecture assumption.

The phase-type density is represented in uniformized form
`uᵀ exp(t • (rate • (P - I))) v`, where `P` is nonnegative, its complex
spectral radius is below one, and `rate > 0`. Endpoint vectors are nonnegative;
normalization is unnecessary because the inequality is homogeneous.
`rawMoment` adds the atom only to the zeroth integral moment.
`hierarchy_for_raw_moments` exposes the same result for any sequence defined
by those raw-moment integrals. The sharp inequality is

```
((s+k)/(s+k-1)) * m_k^2 ≤ m_(k-1) * m_(k+1).
```

The proof derives positivity from the exponential series and exponential
decay from spectral stability. Polynomial integrability and all integration
boundary limits are proved rather than assumed. It then integrates the
increasing logarithmic derivative against `(t-a) * t^(r+1) * f(t)`, with
`a = m_(r+2)/m_(r+1)`, and applies integration by parts twice. This proves
the same implication as the Fisher-information argument in the TeX document.
The equality characterization is not part of these theorems.

Targeted checks (no complete Lake build):

```bash
lake env lean -o .lake/build/lib/lean/SSPLean/LogConvexMomentReduction.olean SSPLean/LogConvexMomentReduction.lean
lake env lean -o .lake/build/lib/lean/SSPLean/MatrixMomentReduction.olean SSPLean/MatrixMomentReduction.lean
```

The final implication and the unconditional two-state theorem depend only
on `propext`, `Classical.choice`, and `Quot.sound`; there are no custom axioms
or unfinished proof terms in the new modules.

## Three-by-three matrix conjectures

`SSPLean/ThreeStateConjectures.lean` closes the three-state moment inequality
without a canonical-representation hypothesis. The principal theorems are:

- `SSP.MatrixMomentReduction.conjecture_two_three_by_three`: convexity of
  `log (uᵀ exp(tA) v / t²)` for every nonnegative real `3 × 3` matrix and
  nonnegative endpoint vectors, when the scalar pairing is not identically zero.
- `SSP.MatrixMomentReduction.momentConjecture_three`: Conjecture 1's inequality
  for every stable uniformized three-state law, every `k ≥ 1`, and any
  nonnegative atom at zero.
- `SSP.MatrixMomentReduction.conjecture_one_three_state`: the explicit inequality
  `((3+k)/(3+k-1)) * m_k² ≤ m_(k-1) * m_(k+1)`.

The representation is constructed directly. Subtracting the smallest diagonal
produces a nonnegative matrix with a zero diagonal. A further nonnegative
scalar shift gives a cubic `M³ = (a+b)M² - abM + QI` with
`0 ≤ a ≤ b`, `Q ≥ 0`, and `M²-aM ≥ 0` entrywise. Cubic ODE uniqueness then
identifies the actual scalar exponential with a nonnegative combination of
the three canonical coordinates. Scalar shifts preserve logarithmic convexity.
The completed real and complex canonical analysis, followed by the existing
moment reduction, proves the result for every matrix and every moment index.
This construction includes zero coefficients and repeated roots.

There are no unfinished proof terms or conjectural representation axioms.
`#print axioms` reports the standard axioms plus the existing `native_decide`
certificate axioms in the complex-root coefficient proofs. Consequently the
final three-state result trusts Lean's native computation in addition to the
kernel; the new representation construction itself uses only `propext`,
`Classical.choice`, and `Quot.sound`. The equality characterization in the
original conjecture remains outside these theorems.

Targeted checks, without a complete Lake build:

```bash
lake env lean SSPLean/ThreeStateConjectures.lean
lake env lean CheckThreeState.lean
```

`CheckThreeState.lean` checks the final theorem signatures and prints their
axiom dependencies. Imports must already have their `.olean` files available;
the new modules can be compiled individually with `lake env lean FILE -o OUTPUT`.

## Block-triangular closure

`SSP.BlockTriangular.block_triangular_closure` in
`SSPLean/BlockTriangularClosure.lean` formalizes Proposition “Block-triangular
closure” of `cyclic_all_k_fisher_reduction.tex`. For positive dimensions `p,q`,
Conjecture 2 in each diagonal block dimension implies logarithmic convexity
with exponent `p+q-1` for `A = [B C; 0 E]`, with arbitrary nonnegative blocks
and endpoint vectors. The zero pairing and zero individual entries are included.
`upperBlock B C E` uses the standard `Fin (p+q)` index order.

`SSPLean/BlockTriangularExponential.lean` proves the actual exponential block
identities and Duhamel's formula; no semigroup representation is assumed.
`SSPLean/LogConvexNonnegative.lean` provides convolution and finite-sum
closure with identically zero summands. `entriesLogConvex_fromBlocks` also
allows concrete block properties to be composed repeatedly, and
`EntriesLogConvex.reindex` handles arbitrary index relabeling.

`SSP.BlockTriangular.conjecture_one_block_triangular` in
`SSPLean/BlockTriangularMoments.lean` gives the resulting Conjecture 1 inequality
for every `k ≥ 1`, assuming stability of the full uniformized matrix and allowing
a nonnegative atom at zero. It has the same two block-dimension Conjecture 2
hypotheses as the TeX proposition.
`conjecture_one_two_by_two_blocks` discharges those hypotheses using the
unconditional two-state theorem, proving the four-state case consisting of two
2×2 diagonal blocks and any nonnegative coupling block.

These closure and moment theorems depend only on `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`, `native_decide`, or custom axioms.
The separate graph-theoretic corollary about strongly connected components is
not formalized here; the closure theorem itself can be applied repeatedly.
Equality characterization is outside these statements.

Targeted checks (no complete Lake build):

```bash
lake env lean SSPLean/BlockTriangularMoments.lean
lake env lean CheckBlockTriangular.lean
```

## Targeted compilation memory

`CubicBernsteinClosure.lean` and `K3AllStagesPositiveSlopeLargeCubic.lean`
provide kernel-checked cubic interpolation lemmas. The large-chart B1 and B2
modules use them without expanding the chart parameters. Their `.olean`
files dropped from approximately 968/999 MiB to 50 KiB each, with unchanged
definitions and theorem statements. Targeted compilations measured about
5.2 GiB peak RSS each; imported proof objects still account for much of this.
The remaining positivity certificates are still expensive.

The working tree includes `python/profiling/profile_lean_memory.py` and
`lean/memory-profiles/REPORT.md` for profiling one module at a time without
a complete Lake build. macOS VSZ includes reserved address space; use RSS
to assess actual RAM pressure.

## Arbitrarily many blocks of size at most three

`SSPLean/SmallBlockTriangular.lean` combines the one-, two-, and three-state
results with repeated block-triangular closure. There is no bound on the
number of blocks or the total dimension. `SmallBlockTriangular` is a
structural predicate generated by nonnegative blocks of dimensions 1–3,
nonnegative upper couplings, and permutations of state indices. It contains
no conjectural analytic hypothesis.

`SSPLean/SmallBlockTriangularPartition.lean` supplies the ordinary partition
interface: `UpperTriangularBlocks sizes A` says that the entries below
each consecutive diagonal block are zero. For any nonempty list of block
sizes in `{1,2,3}`, `conjecture_two_blocks_le_three` proves convexity of
`log (uᵀ exp(tA) v / t^(s-1))`, where `s = sizes.sum`, for nonnegative
matrices and endpoint vectors. Identically zero pairings are included.
`smallBlockTriangular_of_reindexed_partition` permits a partition after any
permutation, and the `small_lower_blocks` theorems cover lower triangular
matrices by transposition.

`conjecture_one_blocks_le_three` gives
`((s+k)/(s+k-1)) * m_k² ≤ m_(k-1) * m_(k+1)` for every `k ≥ 1`,
under the usual spectral stability and positive-rate hypotheses, allowing
a nonnegative atom at zero. This proves the inequality part of Conjecture 1;
the equality characterization remains outside these statements.

The new proofs add no axioms or unfinished terms. The final theorems inherit
the existing 19 `native_decide` certificate axioms from the three-state
result, along with the standard Lean axioms.

Targeted verification (no complete Lake build):

```sh
lake env lean SSPLean/SmallBlockTriangular.lean -o .lake/build/lib/lean/SSPLean/SmallBlockTriangular.olean
lake env lean SSPLean/SmallBlockTriangularPartition.lean -o .lake/build/lib/lean/SSPLean/SmallBlockTriangularPartition.olean
lake env lean CheckSmallBlockTriangular.lean
```
