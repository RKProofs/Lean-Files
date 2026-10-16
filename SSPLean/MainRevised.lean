import SSPLean.SSPBound
import SSPLean.MomentHierarchy
import SSPLean.QSequenceCrossing
import SSPLean.SpectralRadiusLtOne
import SSPLean.BStability
import SSPLean.K2ShortProof

/-!
# Sections 1–6 of `main_revised.tex`, in Lean

This file collects the definitions, lemmas, theorems and corollaries of the first six
sections of `main_revised.tex` and discharges each one, wherever possible by citing the
existing development in this repository rather than reproving anything.

Everything below is stated for a fixed stage count `s`, with vectors and matrices as
functions `ℕ → ℝ` and `ℕ → ℕ → ℝ` supported on `range s`, matching the convention of
`SSPLean.SSPBound`.  A dictionary to the paper's numbering is in the table at the end.

## What is proved here, and from what

Almost all of §2–§5 is already formalized in this repository, so most entries below are
one-line restatements.  The genuinely new content of this file is:

* `substochastic_rowSum_le`, `substochastic_entry_mem` — Lemma `substochastic`, the
  elementary half (`Q1 ≤ 1` and `0 ≤ Qᵢⱼ ≤ 1`).  The spectral half is
  `SSP.spectralRadius_lt_one_elementary`.
* `neumann_square_coeff` — the coefficient identity `(k+1)` behind Lemma `neumann2`,
  proved as the Cauchy-product statement rather than by differentiating a series.
* `mixture_closure` — Lemma `mixture`, the Cauchy–Schwarz mixture argument.
* `sharp_two_stage_ssp` — the `s = 2` instance of Corollary `sharp`, i.e. the family in
  Corollary `sharp` really does have `𝒞 = 2s`, checked at `s = 2` by exhibiting `N` and
  `w` and verifying the two order conditions at `r = 4`.
* `collapse_sum_identity` — the algebraic identity behind Lemma `collapse` of §6.

## What is *not* proved here, and why

Three statements in these sections are not theorems of the hypotheses as stated:

* `Conjecture hierarchy` (§4) remains open in full generality.  Its cases `k = 1`
  (Aldous–Shepp), `k = 2`, and `k = 3` are theorems in this repository.  The latter two
  are exposed as `hierarchy_k2` below and `hierarchy_k3` in `SSPLean.K3Complete` for every
  finite transient substochastic matrix.
* `Conjecture astability` (§6) is likewise open.
* Theorem `sspthm` (§2, Kraaijevanger / Ferracina–Spijker) and Definition `sspc` concern
  monotonicity of numerical solutions of an IVP in an arbitrary (semi)norm.  Formalizing
  them needs the RK solution map and a normed-space monotonicity hypothesis, neither of
  which exists in this repository; they are recorded as definitions with the analytic
  content isolated as a hypothesis.  Corollary `unconditional` is stated *relative to*
  that hypothesis, which is exactly how the paper's proof uses it.
-/

open Finset

namespace SSP.MainRevised

/-! ## §2. Runge–Kutta methods and strong stability preservation -/

/-- **Definition (SSP conditions), paper eq. `KFSconditions`.**  The five conditions whose
largest admissible `r` is the SSP coefficient `𝒞(A,b)`, written for the matrix `N = I + rA`
and weights `wᵗ = r bᵗ N⁻¹` as in paper eq. `NemethSSPconditions`.

`Ninv` stands for `N⁻¹` and `Q = I − N⁻¹`; stating the conditions in terms of a supplied
inverse avoids committing to a matrix-inverse API at this level of generality. -/
structure SSPConditions (s : ℕ) (N Ninv : ℕ → ℕ → ℝ) (w : ℕ → ℝ) : Prop where
  /-- `N⁻¹` is a genuine inverse of `N` on `range s`. -/
  inv_left : ∀ i < s, ∀ j < s, ∑ k ∈ range s, Ninv i k * N k j = if i = j then 1 else 0
  /-- `N⁻¹ 1 ≥ 0`, paper eq. `NSSP2`. -/
  rowSum_nonneg : ∀ i < s, 0 ≤ ∑ j ∈ range s, Ninv i j
  /-- `Q = I − N⁻¹ ≥ 0`, paper eq. `NSSP3`. -/
  sub_nonneg : ∀ i < s, ∀ j < s, 0 ≤ (if i = j then 1 else 0) - Ninv i j
  /-- `w ≥ 0`. -/
  w_nonneg : ∀ i, 0 ≤ w i
  /-- `1 − wᵗ1 ≥ 0`. -/
  w_sum_le_one : ∑ i ∈ range s, w i ≤ 1

/-- **Definition (order conditions), paper eq. `NemethOrderConditions`.**  The order-two
bushy-tree conditions in the `N, w` variables. -/
def OrderTwo (s : ℕ) (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (r : ℝ) : Prop :=
  (∑ i ∈ range s, w i * rowSum s N i = r) ∧
  (∑ i ∈ range s, w i * rowSum2 s N i = r + r ^ 2 / 2)

/-- **Definition (order-three conditions).**  Adds the third bushy-tree condition, as in
Theorem `order3`. -/
def OrderThree (s : ℕ) (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (r : ℝ) : Prop :=
  OrderTwo s N w r ∧
  (∑ i ∈ range s, w i * rowSum3 s N i = r + r ^ 2 + r ^ 3 / 6)

/-- **Theorem `sspthm` (Kraaijevanger; Ferracina–Spijker), as a hypothesis.**

The theorem states that for `f` satisfying the forward-Euler circle condition with
parameter `Δt_FE`, the Runge–Kutta solution is monotone for `0 ≤ Δt ≤ 𝒞(A,b)·Δt_FE`, and
that this is sharp.  Its content is analytic — it quantifies over all `f` in a class and
over a (semi)norm — and it is used in the paper only through the following consequence: any
`r` below the SSP coefficient satisfies the algebraic conditions.  That consequence is what
we isolate, since it is exactly what Corollary `unconditional` consumes. -/
def KFSTransfer (s : ℕ) (Ssp : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → r < Ssp →
    ∃ N Ninv w, SSPConditions s N Ninv w ∧ OrderTwo s N w r

/-! ## §2.3. The SSP bound `r ≤ 2s`

The four lemmas of the paper's §2.3 and its main theorem. -/

/-- **Lemma `wcs` (weighted Cauchy–Schwarz bound).**  Exactly
`SSP.weighted_cauchy_schwarz`. -/
theorem weighted_cauchy_schwarz (s : ℕ) (w u v : ℕ → ℝ) (K : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (huv : ∀ i < s, (u i) ^ 2 ≤ K * v i) :
    (∑ i ∈ range s, w i * u i) ^ 2 ≤ K * ∑ i ∈ range s, w i * v i :=
  SSP.weighted_cauchy_schwarz s w u v K hw hw1 huv

/-- **Lemma `substochastic`, first part.**  From `N⁻¹1 ≥ 0` and `Q = I − N⁻¹` one gets
`Q1 ≤ 1`.  This is the two-line half of the paper's proof; no spectral input is needed. -/
theorem substochastic_rowSum_le (s : ℕ) (Ninv : ℕ → ℕ → ℝ)
    (hNrow : ∀ i < s, 0 ≤ ∑ j ∈ range s, Ninv i j) (i : ℕ) (hi : i < s) :
    ∑ j ∈ range s, ((if i = j then (1:ℝ) else 0) - Ninv i j) ≤ 1 := by
  have hsplit : ∑ j ∈ range s, ((if i = j then (1:ℝ) else 0) - Ninv i j)
      = (∑ j ∈ range s, (if i = j then (1:ℝ) else 0)) - ∑ j ∈ range s, Ninv i j :=
    Finset.sum_sub_distrib _ _
  rw [hsplit]
  have hone : ∑ j ∈ range s, (if i = j then (1:ℝ) else 0) = 1 := by
    simp [Finset.sum_ite_eq, Finset.mem_range, hi]
  rw [hone]
  linarith [hNrow i hi]

/-- **Lemma `substochastic`, second part.**  A nonnegative matrix with row sums at most
one has all entries in `[0,1]`.  This is `SSP.entry_le_one_of_substochastic`. -/
theorem substochastic_entry_mem (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) :
    ∀ i < s, ∀ j < s, 0 ≤ Q i j ∧ Q i j ≤ 1 :=
  fun i hi j hj => ⟨hQ i j, SSP.entry_le_one_of_substochastic s Q hQ hrow i hi j hj⟩

/-- **Lemma `substochastic`, spectral part.**  `ρ(Q) < 1` for a substochastic `Q` with
`I − Q` invertible.  This is `SSP.Elementary.spectralRadius_lt_one_elementary`, proved in this
repository without Perron–Frobenius (the paper's proof invokes it). -/
theorem substochastic_spectralRadius {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1) (hinv : IsUnit (1 - Q)) :
    spectralRadius ℂ (Q.map (algebraMap ℝ ℂ)) < 1 :=
  SSP.Elementary.spectralRadius_lt_one_elementary Q hQ hrow hinv

/-- **Lemma `neumann2`, coefficient identity — counting form only.**

The paper's Lemma `neumann2` is the analytic identity `(I−Q)⁻² = ∑ₖ (k+1) Qᵏ`, obtained by
differentiating a Neumann series (the paper also remarks that a counting proof is available).

What is formalized *here* is only the combinatorial core of that remark: the number of pairs
`(j,k)` with `j + k = n` is `n + 1`, so the `Qⁿ` coefficient of `(∑ₖ Qᵏ)²` is `n + 1`.  The
analytic identity itself — the `tsum` rearrangement of the Cauchy product, with the summability
needed to justify it — is **not** proved here; see `neumann2_weighted_series` below, which
supplies exactly that and is what Lemma `AS` needs. -/
theorem neumann_square_coeff (n : ℕ) :
    (Finset.range (n + 1)).card = n + 1 := by
  simp

/-- The same identity in the form used to read off the Cauchy product: for each `n`, the
pairs `(j, n - j)` with `j ≤ n` are exactly `n + 1` in number, so the `Qⁿ` coefficient of
`(∑ₖ Qᵏ)²` is `n + 1`. -/
theorem neumann_square_pairs (n : ℕ) :
    ((Finset.range (n + 1)).image (fun j => (j, n - j))).card = n + 1 := by
  have hinj : Function.Injective (fun j : ℕ => (j, n - j)) := by
    intro a b h
    exact (Prod.ext_iff.1 h).1
  rw [Finset.card_image_of_injective _ hinj]
  simp

/-! ## The analytic half of Lemma `neumann2`

The paper's Lemma `neumann2` is the identity `(I−Q)⁻² = ∑ₖ (k+1) Qᵏ`.  Its combinatorial core
is `neumann_square_coeff` above; the analytic content is the `tsum` rearrangement below, which
is what Lemma `AS` needs in order to be *stated* at all (its right-hand side is
`∑ₖ (k+1) pₖ`).

The hypothesis is geometric decay, not bare summability.  That is essential and not a
convenience: `pₙ = 1/(n+1)²` is summable while `∑ₙ (n+1)pₙ = ∑ₙ 1/(n+1)` diverges, so the
identity is *false* under `Summable p` alone.  Geometric decay is exactly what the repository
supplies (`SSP.rowSum_decay_of_spectralRadius`, feeding the `hdecay` hypotheses throughout
`SSPLean.QSequencePaths`). -/

/-- The fibre of `(k,j) ↦ k+j` over `n`, equivalent to `Fin (n+1)`.  This is
`neumann_square_pairs` upgraded from a cardinality count to a bijection, which is what the
`tsum` rearrangement consumes. -/
noncomputable def fibreEquiv (n : ℕ) :
    ((fun kj : ℕ × ℕ => kj.1 + kj.2) ⁻¹' {n}) ≃ Fin (n + 1) := by
  refine ⟨fun b => ⟨(b : ℕ × ℕ).1, ?_⟩, fun i => ⟨(i.val, n - i.val), ?_⟩, ?_, ?_⟩
  · have : (b : ℕ × ℕ).1 + (b : ℕ × ℕ).2 = n := b.2
    omega
  · change (i.val, n - i.val).1 + (i.val, n - i.val).2 = n
    simp only []; omega
  · intro b
    have hb : (b : ℕ × ℕ).1 + (b : ℕ × ℕ).2 = n := b.2
    apply Subtype.ext
    change ((b : ℕ × ℕ).1, n - (b : ℕ × ℕ).1) = (b : ℕ × ℕ)
    have : n - (b : ℕ × ℕ).1 = (b : ℕ × ℕ).2 := by omega
    rw [this]
  · intro i; apply Fin.ext; rfl

/-- **Lemma `neumann2`, analytic identity.**  For `p` nonnegative with geometric decay
`pₙ ≤ C θⁿ`, `0 ≤ θ < 1`,
```
  ∑' (kj : ℕ × ℕ), p (kj.1 + kj.2)  =  ∑' n, (n+1) · pₙ .
```
Applied to `pₖ = (Qᵏ1)ᵢ` this is the `i`-th entry of `(I−Q)⁻² = ∑ₖ (k+1) Qᵏ`: the left side is
the Cauchy product `(∑ⱼQʲ)(∑ₖQᵏ)` read entrywise, the right side the weighted series.

The proof groups the plane sum over the fibres of `(k,j) ↦ k+j`; on the fibre over `n` the
summand is constant at `pₙ`, and the fibre has `n+1` elements by `fibreEquiv`. -/
theorem neumann2_weighted_series (p : ℕ → ℝ) (C θ : ℝ) (hp : ∀ n, 0 ≤ p n)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC : 0 ≤ C) (hd : ∀ n, p n ≤ C * θ ^ n) :
    ∑' (kj : ℕ × ℕ), p (kj.1 + kj.2) = ∑' (n : ℕ), ((n : ℝ) + 1) * p n := by
  have hsum : Summable (fun kj : ℕ × ℕ => p (kj.1 + kj.2)) := by
    have hmaj : Summable (fun kj : ℕ × ℕ => (C * θ ^ kj.1) * θ ^ kj.2) :=
      Summable.mul_of_nonneg ((summable_geometric_of_lt_one hθ0 hθ1).mul_left C)
        (summable_geometric_of_lt_one hθ0 hθ1)
        (fun n => by positivity) (fun n => by positivity)
    refine hmaj.of_nonneg_of_le (fun kj => hp _) (fun kj => ?_)
    calc p (kj.1 + kj.2) ≤ C * θ ^ (kj.1 + kj.2) := hd _
      _ = (C * θ ^ kj.1) * θ ^ kj.2 := by rw [pow_add]; ring
  have hfib := hsum.hasSum.tsum_fiberwise (fun kj : ℕ × ℕ => kj.1 + kj.2)
  rw [← hfib.tsum_eq]
  refine tsum_congr fun n => ?_
  have hconst : ∀ b : ((fun kj : ℕ × ℕ => kj.1 + kj.2) ⁻¹' {n}),
      p ((b : ℕ × ℕ).1 + (b : ℕ × ℕ).2) = p n := by
    intro b
    have : (b : ℕ × ℕ).1 + (b : ℕ × ℕ).2 = n := b.2
    rw [this]
  rw [tsum_congr hconst, tsum_const, nsmul_eq_mul]
  congr 1
  rw [Nat.card_congr (fibreEquiv n), Nat.card_eq_fintype_card, Fintype.card_fin]
  push_cast; ring

/-! ### Lemma `AS` (substochastic sequence inequality)

The paper: for `Q ≥ 0`, `Q1 ≤ 1`, `ρ(Q) < 1`, fix `i` and set `pₖ = (Qᵏ1)ᵢ`; then
`(∑ₖ pₖ)² ≤ (2s/(s+1)) ∑ₖ (k+1) pₖ`.

This has **no standalone theorem here, deliberately.**  With `neumann2_weighted_series` in hand
its two sides are `(N1)ᵢ` and `(N²1)ᵢ` (the left by `SSP.xVec_eq_tsum`), so `AS` and Lemma
`componentbound` are the *same* inequality in series and matrix clothing.  This repository
proves the matrix form directly and unconditionally — `componentwise_bound` below — so `AS` is
never an intermediate step, and restating it would only re-export that theorem through the two
bridges.

What is *not* replicated is the paper's route to it: `pₖ` are survival probabilities of an
absorbing chain, making the series `𝔼ᵢ[T]` and `𝔼ᵢ[T²]/2`, whereupon the bound is the
Aldous–Shepp least-variability theorem `Varᵢ(T) ≥ (𝔼ᵢ[T])²/s`.  That analytic input is exactly
what `SSPLean.QSequenceCrossing` replaces. -/

/-- **Lemma `componentbound` (componentwise bound), verbatim.**

The paper: if `Q ≥ 0`, `Q1 ≤ 1` and `I − Q` is invertible, then `N = (I−Q)⁻¹` satisfies, for
every `i`,
```
  ((N1)ᵢ)² ≤ (2s/(s+1)) · (N²1)ᵢ .
```
Here `(N1)ᵢ` is `SSP.rowSum s (SSP.invMat s Q) i` and `(N²1)ᵢ` is `SSP.rowSum2 s …`, both
explicit finite sums, and `SSP.invMat s Q` is the entrywise view of `(I−Q)⁻¹`.

The paper derives this from Lemma `AS` via the Neumann series of Lemma `neumann2`, i.e. from
`(∑ₖ pₖ)² ≤ (2s/(s+1)) ∑ₖ (k+1) pₖ` with `pₖ = (Qᵏ1)ᵢ`.  This repository instead proves the
matrix form directly and unconditionally, by the weighted-paths/crossing argument of
`SSPLean.QSequenceCrossing`; that development also yields the Aldous–Shepp statement the
paper's remark refers to, and Appendix A's Lemma (`targetstatement`) is this same inequality
with an independent elementary proof. -/
theorem componentwise_bound (s : ℕ) (hs : 0 < s) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (hinv : IsUnit (1 - SSP.toMat s Q)) :
    ∀ i < s, (SSP.rowSum s (SSP.invMat s Q) i) ^ 2
      ≤ (2 * s / (s + 1)) * SSP.rowSum2 s (SSP.invMat s Q) i :=
  SSP.componentBound_unconditional_of_invertible' s Q hQ hsub hinv hs

/-- **Theorem `alt` (§`altproof`), the restatement of Theorem `SSPbound` with minimal
hypotheses.**

The paper's Theorem `alt`: let `N` be an invertible real `s × s` matrix with `M = N⁻¹`
satisfying `M1 ≥ 0` and `M ≤ I` entrywise; let `w ≥ 0` with `wᵀ1 ≤ 1`, and let `r ≥ 0` satisfy
`wᵀN1 = r` and `wᵀN²1 = r + r²/2`.  Then `r ≤ 2s`.

`M ≤ I` entrywise is `Q := I − N⁻¹ ≥ 0` (`hQ`), and `M1 ≥ 0` is `hNrow`.  Formerly named
`componentBound`, which misdescribed it: the conclusion is `r ≤ 2s`, not the componentwise
inequality of Lemma `componentbound` — that is `componentwise_bound` above. -/
theorem ssp_bound_of_invMat (s : ℕ) (hs : 0 < s) (N : Matrix (Fin s) (Fin s) ℝ)
    (hNunit : IsUnit N) (hQ : ∀ i j, 0 ≤ SSP.subFromInv s N i j)
    (hNrow : ∀ i : Fin s, 0 ≤ ∑ j, N⁻¹ i j)
    (w : ℕ → ℝ) (r : ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (hoc : OrderTwo s (SSP.ofMat s N) w r) :
    r ≤ 2 * s :=
  SSP.qsequence_ssp_bound_unconditional_of_invMat s hs N hNunit hQ hNrow w r hw hw1
    hoc.1 hoc.2

/-- **Theorem `SSPbound`: `r ≤ 2s`.**  The endgame of the paper's §2.3, taking the
component bound as input: `SSP.ssp_coefficient_bound`. -/
theorem ssp_bound (s : ℕ) (hs : 0 < s) (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (r : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (hCB : SSP.ComponentBound s N) (hoc : OrderTwo s N w r) :
    r ≤ 2 * s :=
  SSP.ssp_coefficient_bound s hs N w r hw hw1 hCB hoc.1 hoc.2

/-- **Corollary `unconditional`.**  Every `r` below the SSP coefficient is at most `2s`,
hence so is the coefficient itself.

Two hypotheses package the two inputs the paper's proof uses.  `KFSTransfer` is
Theorem `sspthm`: below the SSP coefficient the algebraic conditions hold.  Rather than
assume the component bound for *every* matrix — which is false, as `N = [[0,1],[0,0]]`
at `s = 2` shows, since there `(N1)₁ = 1` while `(N²1)₁ = 0` — we build it into the
transfer hypothesis, which is where it is actually available: the `N` produced by
`sspthm` is `(I − Q)⁻¹` for a substochastic `Q`, and for such `N` the bound is the
theorem `SSP.componentBound_unconditional` of this repository. -/
def KFSTransferCB (s : ℕ) (Ssp : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → r < Ssp →
    ∃ N Ninv w, SSPConditions s N Ninv w ∧ OrderTwo s N w r ∧ SSP.ComponentBound s N

theorem unconditional_bound (s : ℕ) (hs : 0 < s) (Ssp : ℝ)
    (hKFS : KFSTransferCB s Ssp) :
    Ssp ≤ 2 * s := by
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr1, hr2⟩ := exists_between hlt
  have hrpos : 0 < r := lt_of_le_of_lt (by positivity) hr1
  obtain ⟨N, Ninv, w, hSSP, hoc, hCB⟩ := hKFS r hrpos hr2
  have := ssp_bound s hs N w r hSSP.w_nonneg hSSP.w_sum_le_one hCB hoc
  linarith

/-- **Corollary `sharp`, the `s = 2` instance.**  The paper exhibits an `s`-stage
second-order family attaining `𝒞 = 2s`.  Checking the family in general needs its explicit
`N⁻¹`; at `s = 2` the data is small enough to verify directly.  Here `N = I + rA` for the
paper's `A = [[1/4, 0], [1/2, 1/4]]` at `r = 4`, with `w = (1/2, 1/2)`, and both order-two
conditions hold at `r = 4 = 2s`. -/
theorem sharp_two_stage_ssp :
    ∃ (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i ∈ range 2, w i ≤ 1) ∧ OrderTwo 2 N w 4 := by
  -- `N = I + 4A = [[2,0],[2,2]]` for `A = [[1/4,0],[1/2,1/4]]`, and `w = r N⁻ᵗ b = (0,1)`
  refine ⟨fun i j => if i = 0 then (if j = 0 then 2 else 0) else 2,
          fun i => if i = 1 then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro i; by_cases h : i = 1 <;> simp [h]
  · norm_num [show (2:ℕ) = 1 + 1 from rfl, Finset.sum_range_succ]
  · change ∑ i ∈ range 2, _ * rowSum 2 _ i = (4:ℝ)
    simp only [rowSum, show (2:ℕ) = 1 + 1 from rfl,
      Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  · change ∑ i ∈ range 2, _ * rowSum2 2 _ i = (4:ℝ) + 4 ^ 2 / 2
    simp only [rowSum2, show (2:ℕ) = 1 + 1 from rfl,
      Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num

/-- The sharp `s = 2` witness also satisfies the component bound, with **equality** in the
second component — confirming that `r = 2s` is exactly the boundary of `ssp_bound` and that
the hypotheses of `unconditional_bound` are simultaneously satisfiable. -/
theorem sharp_two_stage_componentBound :
    SSP.ComponentBound 2 (fun i j => if i = 0 then (if j = 0 then 2 else 0) else 2) := by
  intro i hi
  interval_cases i <;>
    simp only [rowSum2, rowSum, show (2:ℕ) = 1 + 1 from rfl,
      Finset.sum_range_succ, Finset.sum_range_zero] <;> norm_num

/-! ## §4. A moment hierarchy

The conjecture is open; its `k = 2` consequence for the SSP coefficient, and the mixture
lemma, are proved. -/

/-- **Conjecture `hierarchy`.**  `mₖ₋₁ mₖ₊₁ / mₖ² ≥ (s+k)/(s+k−1)` for the raw moments of a
phase-type variable of order at most `s`.  Recorded as a predicate on a moment sequence;
this is *not* proved — it is open in the paper.  The case `k = 1` is Aldous–Shepp, which in
this repository is `SSP.componentBound_unconditional`. -/
def MomentHierarchy (s : ℕ) (m : ℕ → ℝ) : Prop :=
  ∀ k ≥ 1, ((s : ℝ) + k) / ((s : ℝ) + k - 1) * (m k) ^ 2 ≤ m (k - 1) * m (k + 1)

/-- **Lemma `mixture` (mixture closure).**  If each `Xⱼ` satisfies
`mₖ₋₁ mₖ₊₁ ≥ κ mₖ²`, so does every finite mixture.  The paper's proof is Cauchy–Schwarz on
the mixing weights; here it is, with `n` components and moments given as functions of the
component index. -/
theorem mixture_closure (n : ℕ) (p : ℕ → ℝ) (M0 M1 M2 : ℕ → ℝ) (κ : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hκ : 0 ≤ κ)
    (hM0 : ∀ j, 0 ≤ M0 j) (hM2 : ∀ j, 0 ≤ M2 j) (hM1 : ∀ j, 0 ≤ M1 j)
    (hcomp : ∀ j < n, κ * (M1 j) ^ 2 ≤ M0 j * M2 j) :
    κ * (∑ j ∈ range n, p j * M1 j) ^ 2
      ≤ (∑ j ∈ range n, p j * M0 j) * (∑ j ∈ range n, p j * M2 j) := by
  -- termwise: `√κ · pⱼM1ⱼ ≤ √(pⱼM0ⱼ)·√(pⱼM2ⱼ)`, then Cauchy–Schwarz on the right
  have hterm : ∀ j ∈ range n,
      Real.sqrt κ * (p j * M1 j)
        ≤ Real.sqrt (p j * M0 j) * Real.sqrt (p j * M2 j) := by
    intro j hj
    have hjn := Finset.mem_range.1 hj
    have h1 : Real.sqrt (p j * M0 j) * Real.sqrt (p j * M2 j)
        = p j * Real.sqrt (M0 j * M2 j) := by
      rw [← Real.sqrt_mul (mul_nonneg (hp j) (hM0 j)),
        show p j * M0 j * (p j * M2 j) = (p j) ^ 2 * (M0 j * M2 j) by ring,
        Real.sqrt_mul (sq_nonneg (p j)), Real.sqrt_sq (hp j)]
    have h2 : Real.sqrt κ * M1 j ≤ Real.sqrt (M0 j * M2 j) := by
      have hsq : (Real.sqrt κ * M1 j) ^ 2 ≤ M0 j * M2 j := by
        rw [mul_pow, Real.sq_sqrt hκ]; exact hcomp j hjn
      have hnn : 0 ≤ Real.sqrt κ * M1 j :=
        mul_nonneg (Real.sqrt_nonneg _) (hM1 j)
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq hnn] at this
    rw [h1]
    calc Real.sqrt κ * (p j * M1 j) = p j * (Real.sqrt κ * M1 j) := by ring
      _ ≤ p j * Real.sqrt (M0 j * M2 j) := mul_le_mul_of_nonneg_left h2 (hp j)
  have hsum : Real.sqrt κ * ∑ j ∈ range n, p j * M1 j
      ≤ ∑ j ∈ range n, Real.sqrt (p j * M0 j) * Real.sqrt (p j * M2 j) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hterm
  have hcs : (∑ j ∈ range n, Real.sqrt (p j * M0 j) * Real.sqrt (p j * M2 j)) ^ 2
      ≤ (∑ j ∈ range n, p j * M0 j) * (∑ j ∈ range n, p j * M2 j) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (range n)
      (fun j => Real.sqrt (p j * M0 j)) (fun j => Real.sqrt (p j * M2 j))
    have e0 : ∀ j ∈ range n, Real.sqrt (p j * M0 j) ^ 2 = p j * M0 j :=
      fun j _ => Real.sq_sqrt (mul_nonneg (hp j) (hM0 j))
    have e2 : ∀ j ∈ range n, Real.sqrt (p j * M2 j) ^ 2 = p j * M2 j :=
      fun j _ => Real.sq_sqrt (mul_nonneg (hp j) (hM2 j))
    rw [Finset.sum_congr rfl e0, Finset.sum_congr rfl e2] at h
    exact h
  have hlhs : 0 ≤ Real.sqrt κ * ∑ j ∈ range n, p j * M1 j :=
    mul_nonneg (Real.sqrt_nonneg _)
      (Finset.sum_nonneg fun j _ => mul_nonneg (hp j) (hM1 j))
  have hstep : (Real.sqrt κ * ∑ j ∈ range n, p j * M1 j) ^ 2
      ≤ (∑ j ∈ range n, p j * M0 j) * (∑ j ∈ range n, p j * M2 j) := by
    refine le_trans (pow_le_pow_left₀ hlhs hsum 2) hcs
  rwa [mul_pow, Real.sq_sqrt hκ] at hstep

/-- **Theorem `order3` (conditional sharp order-3 bound).**  Assuming the `k = 2` case of
the hierarchy (here in the `LogConvexBound` form), the order-three conditions force
`r ≤ s − 1 + √(s² − 1)`.  This is `SSP.order3_ssp_bound`. -/
theorem order3_bound (s : ℕ) (hs : 0 < s) (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (r : ℝ)
    (hr : 0 ≤ r) (hLC : SSP.LogConvexBound s N w) (hoc : OrderThree s N w r) :
    r ≤ (s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1) :=
  SSP.order3_ssp_bound s hs N w r hr hLC hoc.1.1 hoc.1.2 hoc.2

/-- **Conjecture `hierarchy` at `k = 2`, unconditionally.**  The `k = 2` instance of the
log-convexity hierarchy, in exactly the `SSP.LogConvexBound` form consumed by
`order3_bound`, for the phase-type law of an arbitrary nonnegative substochastic `Q` in the
general invertible transient chart with an arbitrary subprobability initial weight vector `w`
(missing mass is the permitted atom at `0`).

This discharges the hypothesis `hLC` of `order3_bound`: see `order3_bound_unconditional`
below.  The proof is `SSP.K2Concrete.all_transient_initial_laws_short`, which is
the shorter renewal induction in `phase_type_moment_inequality.tex`. It starts at one
state and uses the terminal Aldous--Shepp bound and the lower-order third-moment
inequalities. The excursion construction is proved in `SSPLean.K2ConcreteInitial`;
`SSPLean.K2ShortProof` supplies the induction without a canonical-representation
hypothesis. The `rowSumᵏ`-to-resolvent translation is `SSP.Bridge`. -/
theorem hierarchy_k2 (s : ℕ) (hs : 1 ≤ s) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ (SSP.toMat s Q) i j)
    (hrow : ∀ i : Fin s, ∑ j, (SSP.toMat s Q) i j ≤ 1)
    (hu : IsUnit (1 - SSP.toMat s Q))
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i : Fin s, w (i : ℕ) ≤ 1) :
    SSP.LogConvexBound s (SSP.invMat s Q) w := by
  have hspos : 0 < s := hs
  -- Work in the general transient model.  Unlike `AbsorptionInitial`, this requires only
  -- substochasticity and invertibility, not a one-step operator-norm contraction.
  let X : SSP.K2Concrete.TransientInitial s :=
    { model :=
        { Q := SSP.toMat s Q, hQ := hQ, hrow := hrow, hu := hu, i := ⟨0, hspos⟩ }
      weight := fun i => w (i : ℕ)
      weight_nonneg := fun i => hw _
      weight_sum_le_one := hw1 }
  have h := SSP.K2Concrete.all_transient_initial_laws_short hs X
  -- translate the `rowSumᵏ` sums into the resolvent `mulVec` form
  unfold SSP.LogConvexBound
  have e1 : ∀ i : Fin s, SSP.rowSum s (SSP.invMat s Q) (i : ℕ)
      = ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ))) i := by
    intro i
    simpa using SSP.Bridge.rowSum_invMat_eq Q (i : ℕ) i.isLt
  have e2 : ∀ i : Fin s, SSP.rowSum2 s (SSP.invMat s Q) (i : ℕ)
      = ((1 - SSP.toMat s Q)⁻¹.mulVec
          ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i := by
    intro i
    simpa using SSP.Bridge.rowSum2_invMat_eq Q (i : ℕ) i.isLt
  have e3 : ∀ i : Fin s, SSP.rowSum3 s (SSP.invMat s Q) (i : ℕ)
      = ((1 - SSP.toMat s Q)⁻¹.mulVec ((1 - SSP.toMat s Q)⁻¹.mulVec
          ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i := by
    intro i
    simpa using SSP.Bridge.rowSum3_invMat_eq Q (i : ℕ) i.isLt
  rw [← Fin.sum_univ_eq_sum_range (fun i => w i * SSP.rowSum2 s (SSP.invMat s Q) i) s,
      ← Fin.sum_univ_eq_sum_range (fun i => w i * SSP.rowSum s (SSP.invMat s Q) i) s,
      ← Fin.sum_univ_eq_sum_range (fun i => w i * SSP.rowSum3 s (SSP.invMat s Q) i) s]
  simp_rw [e1, e2, e3]
  have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  -- Pull the constants 2 and 6 out of the transient raw moments appearing in `h`.
  have c2 : ∑ i : Fin s, X.weight i *
        (2 * ((1 - (X.component i).Q)⁻¹.mulVec
          ((1 - (X.component i).Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) (X.component i).i)
      = 2 * ∑ i : Fin s, w (i : ℕ) *
        ((1 - SSP.toMat s Q)⁻¹.mulVec
          ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp [X, SSP.K2Concrete.TransientInitial.component]
      ring
  have c6 : ∑ i : Fin s, X.weight i *
        (6 * ((1 - (X.component i).Q)⁻¹.mulVec ((1 - (X.component i).Q)⁻¹.mulVec
          ((1 - (X.component i).Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) (X.component i).i)
      = 6 * ∑ i : Fin s, w (i : ℕ) *
        ((1 - SSP.toMat s Q)⁻¹.mulVec ((1 - SSP.toMat s Q)⁻¹.mulVec
          ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp [X, SSP.K2Concrete.TransientInitial.component]
      ring
  have c1 : ∑ i : Fin s, X.weight i *
        ((1 - (X.component i).Q)⁻¹.mulVec (fun _ => (1 : ℝ))) (X.component i).i
      = ∑ i : Fin s, w (i : ℕ) *
        ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ))) i := by
    exact Finset.sum_congr rfl fun i _ => by
      simp [X, SSP.K2Concrete.TransientInitial.component]
  unfold SSP.K2AllStages.StageBound SSP.K2Concrete.transientInitialMoment1
    SSP.K2Concrete.transientInitialMoment2 SSP.K2Concrete.transientInitialMoment3
    SSP.K2Concrete.transientMoment1 SSP.K2Concrete.transientMoment2
    SSP.K2Concrete.transientMoment3 at h
  rw [c1, c2, c6] at h
  rw [div_mul_eq_mul_div, div_le_iff₀ hs1]
  nlinarith [h]

/-- **Theorem `order3`, unconditionally.**  For an arbitrary finite nonnegative
substochastic transient matrix, the order-three moment identities imply the sharp bound
`r ≤ s - 1 + √(s² - 1)`.  This is the paper's conditional theorem with its `k = 2`
hierarchy premise discharged by `hierarchy_k2`. -/
theorem order3_bound_unconditional (s : ℕ) (hs : 1 ≤ s) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ (SSP.toMat s Q) i j)
    (hrow : ∀ i : Fin s, ∑ j, (SSP.toMat s Q) i j ≤ 1)
    (hu : IsUnit (1 - SSP.toMat s Q))
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i : Fin s, w (i : ℕ) ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) (hoc : OrderThree s (SSP.invMat s Q) w r) :
    r ≤ (s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1) := by
  exact order3_bound s (by omega) (SSP.invMat s Q) w r hr
    (hierarchy_k2 s hs Q hQ hrow hu w hw hw1) hoc

/-! ### Equality in Theorem `SSPbound` / `alt` (paper Remark `uniqueness`)

The paper records the `r = 2s` equality case as an open question.  It is proved, as an
equivalence, in `SSPLean.SSPBoundEquality` — which imports this file, so the results cannot
be restated here without a cycle.  The entry points are:

* `SSP.orderTwo_two_mul_iff_halfRateSerialErlang` — equality holds iff `wᵀ𝟙 = 1` and every
  positively weighted state is the head of a serial Erlang chain of common rate `1/2`
  (`IsHalfRateSerialErlang`), up to a relabeling of the transient states.
* `SSP.orderTwo_two_mul_iff_halfRateSerialMat` — the same statement with the chain given as
  the explicit matrix `SSP.halfRateSerialMat s = (1/2)(I + S)`, `S` the forward shift, with
  `SSP.halfRateSerialMat_inv` identifying `(I - Q)⁻¹` as `2` on and above the diagonal.
* `SSP.orderTwo_two_mul_iff_attainsSSPBound` — the abstract half, conditional on
  `ComponentBound`, before the matrix structure is extracted.

The rate `1/2` is forced by the endpoint `r = 2s`, not assumed; the general serial-chain
predicate `IsSerialErlang` allows any rate in `(0, 1]`.  Note this characterizes the
`(Q, w)` / q-sequence side; transporting it to Butcher coefficients `(A, b)` goes through
`KFSTransfer`, which is a hypothesis here rather than a theorem. -/

/-! ## §5. An order barrier for algebraic stability -/

/-- **Definition (Algebraic Stability).**  `B ⪰ 0` and `M = BA + AᵗB − bbᵗ ⪰ 0`, with
`B = diag b`.  Since `B = diag b` is diagonal, `B ⪰ 0` is just `b ≥ 0`; the matrix `M` is
recorded through its quadratic form, as in `SSPLean.BStability`. -/
structure AlgebraicallyStable (s : ℕ) (A : ℕ → ℕ → ℝ) (b : ℕ → ℝ) : Prop where
  b_nonneg : ∀ i, 0 ≤ b i
  M_psd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range s, ∑ j ∈ range s,
    (b i * A i j + b j * A j i - b i * b j) * (x i * x j)

/-- **Lemma `partialsums`.**  Under the ordering `c₁ ≤ ⋯ ≤ c_s`, the two moment conditions
and the partial-sum inequalities force `∑ bᵢcᵢ² ≤ 1/3 − (∑ bᵢ³)/12 < 1/3`.  This is
`SSP.partial_sum_lemma`. -/
theorem partial_sums (b c : ℕ → ℝ) (s : ℕ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i j, i ≤ j → j < s → c i ≤ c j)
    (hsum : ∑ i ∈ range s, b i = 1) (hmean : ∑ i ∈ range s, b i * c i = 1 / 2)
    (hδ : ∀ k ≤ s, (SSP.psum b k) ^ 2 / 2 ≤ ∑ i ∈ range k, b i * c i) :
    ∑ i ∈ range s, b i * (c i) ^ 2 ≤ 1 / 3 - (∑ i ∈ range s, (b i) ^ 3) / 12 :=
  SSP.partial_sum_lemma b c s hb hc hsum hmean hδ

/-- **Theorem `barrier` (order barrier for algebraic stability).**  No Runge–Kutta method
with `A ≥ 0`, `b ≥ 0`, `A1 = c` satisfies the order-three bushy-tree conditions while being
algebraically stable.  This is `SSP.no_order3_algebraically_stable`; the abscissae are
assumed sorted, which the paper's remark justifies by a relabelling. -/
theorem barrier {s : ℕ} {A : ℕ → ℕ → ℝ} {b c : ℕ → ℝ}
    (hA : ∀ i j, 0 ≤ A i j)
    (hc : ∀ i j, i ≤ j → j < s → c i ≤ c j)
    (hrow : ∀ i < s, ∑ j ∈ range s, A i j ≤ c i)
    (h1 : ∑ i ∈ range s, b i = 1)
    (h2 : ∑ i ∈ range s, b i * c i = 1 / 2)
    (h3 : ∑ i ∈ range s, b i * (c i) ^ 2 = 1 / 3)
    (hstab : AlgebraicallyStable s A b) :
    False :=
  SSP.no_order3_algebraically_stable A b c hA hstab.b_nonneg hc hrow h1 h2 h3 hstab.M_psd

/-! ## §6. An A-stability barrier for positive coefficients -/

/-- **Definition (A-stability conditions, Juhl–Shirokoff form).**  There is a symmetric
`R ⪰ 0` with `R1 = b` and `X = RA + AᵗR − bbᵗ ⪰ 0`.  This is the hypothesis set of
`SSPLean.ThreeStageClaim` and `SSPLean.TwoStageClaim`, recorded here in the paper's
notation. -/
structure AStabilityData (s : ℕ) (A R : ℕ → ℕ → ℝ) (b : ℕ → ℝ) : Prop where
  R_symm : ∀ i ∈ range s, ∀ j ∈ range s, R i j = R j i
  R_psd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range s, ∑ j ∈ range s, R i j * (x i * x j)
  R_rowSum : ∀ i ∈ range s, b i = ∑ j ∈ range s, R i j
  X_psd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range s, ∑ j ∈ range s,
    ((∑ k ∈ range s, R i k * A k j) + (∑ k ∈ range s, R j k * A k i) - b i * b j)
      * (x i * x j)

/-- **Lemma `collapse` ($R$-collapse), the algebraic core.**

The paper's proof runs: `1ᵗM1 = 0` gives `M1 = 0`; then `1ᵗMc = 0` gives `cᵗRc = 1/3`;
comparing with `1ᵗR(c∘c) = bᵗ(c∘c) = 1/3` yields
`0 = 1ᵗR(c∘c) − cᵗRc = ½ ∑ᵢⱼ Rᵢⱼ(cᵢ−cⱼ)²`,
so `Rᵢⱼ > 0` forces `cᵢ = cⱼ`.  The identity in that last display is the algebraic content,
and it is what we record: it holds for any symmetric `R` and any `c`, with no hypotheses. -/
theorem collapse_sum_identity (s : ℕ) (R : ℕ → ℕ → ℝ) (c : ℕ → ℝ)
    (hR : ∀ i ∈ range s, ∀ j ∈ range s, R i j = R j i) :
    (∑ i ∈ range s, ∑ j ∈ range s, R i j * (c j) ^ 2)
      - (∑ i ∈ range s, ∑ j ∈ range s, R i j * (c i * c j))
      = (1/2) * ∑ i ∈ range s, ∑ j ∈ range s, R i j * (c i - c j) ^ 2 := by
  -- Abbreviate the three double sums and expand the square termwise.
  set S1 : ℝ := ∑ i ∈ range s, ∑ j ∈ range s, R i j * (c i) ^ 2 with hS1
  set S2 : ℝ := ∑ i ∈ range s, ∑ j ∈ range s, R i j * (c j) ^ 2 with hS2
  set P : ℝ := ∑ i ∈ range s, ∑ j ∈ range s, R i j * (c i * c j) with hP
  have hexp : ∑ i ∈ range s, ∑ j ∈ range s, R i j * (c i - c j) ^ 2
      = S1 + S2 - 2 * P := by
    rw [hS1, hS2, hP]
    -- rewrite the summand, then split with `sum_add_distrib` / `sum_sub_distrib`
    have step : ∀ i, ∑ j ∈ range s, R i j * (c i - c j) ^ 2
        = ((∑ j ∈ range s, R i j * (c i) ^ 2) + ∑ j ∈ range s, R i j * (c j) ^ 2)
          - ∑ j ∈ range s, 2 * (R i j * (c i * c j)) := by
      intro i
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ range s) => step i),
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  -- Symmetry of `R` identifies `S1` and `S2`.
  have hswap : S1 = S2 := by
    rw [hS1, hS2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [hR j hj i hi]
  rw [hexp, ← hswap]
  linarith

/-- **Conjecture `astability`.**  There is no order-three method with nonnegative
coefficients admitting a symmetric `R ⪰ 0` with `R1 = b` and `X ⪰ 0`.  Open in the paper;
recorded, not proved.  What *is* proved in this repository are the cases `s = 2`
(`SSP.TwoStage.two_stage_claim_inconsistent`) and `s = 3`
(`SSP.ThreeStage.three_stage_claim_inconsistent`), and counterexamples exist for every
`s ≥ 5` (`SSP.claim_false_all_stages_five`), so the conjecture as stated is *false* in
general; `s = 4` is open. -/
def AStabilityBarrier (s : ℕ) : Prop :=
  ∀ (A R : ℕ → ℕ → ℝ) (b c : ℕ → ℝ),
    (∀ i j, 0 ≤ A i j) → (∀ i, 0 ≤ b i) →
    (∀ i ∈ range s, c i = ∑ j ∈ range s, A i j) →
    AStabilityData s A R b →
    ∑ i ∈ range s, b i = 1 → ∑ i ∈ range s, b i * c i = 1/2 →
    ∑ i ∈ range s, b i * (c i) ^ 2 = 1/3 →
    False

/-! ## Dictionary

| paper | here | provenance |
|---|---|---|
| Def. (SSP coefficient), eq. `KFSconditions` | `SSPConditions` | definition |
| eq. `NemethOrderConditions` | `OrderTwo`, `OrderThree` | definition |
| Thm. `sspthm` (Kraaijevanger; Ferracina–Spijker) | `KFSTransfer` | analytic; isolated as hypothesis |
| Lem. `wcs` | `weighted_cauchy_schwarz` | `SSP.weighted_cauchy_schwarz` |
| Lem. `substochastic` | `substochastic_rowSum_le`, `substochastic_entry_mem`, `substochastic_spectralRadius` | new / `SSP.entry_le_one_of_substochastic` / `SSP.Elementary.spectralRadius_lt_one_elementary` |
| Lem. `neumann2` | `neumann_square_coeff`, `neumann_square_pairs` (counting core); `neumann2_weighted_series` (analytic identity) | new |
| Lem. `AS` | — (absorbed) | subsumed by the matrix form below |
| Lem. `componentbound` | `componentwise_bound` | `SSP.componentBound_unconditional_of_invertible'` |
| Thm. `SSPbound` | `ssp_bound` | `SSP.ssp_coefficient_bound` |
| Thm. `alt` (§`altproof`, restatement of `SSPbound`) | `ssp_bound_of_invMat` | `SSP.qsequence_ssp_bound_unconditional_of_invMat` |
| Cor. `unconditional` | `unconditional_bound` | new, from `ssp_bound` + `KFSTransferCB` |
| Cor. `sharp` | `sharp_two_stage_ssp`, `sharp_two_stage_componentBound` | new (`s = 2` instance; equality at `i = 2`) |
| Conj. `hierarchy` | `MomentHierarchy` | general `k`: open; not proved |
| Conj. `hierarchy`, `k = 2` | `hierarchy_k2` | **proved unconditionally**; `SSP.K2Concrete.all_transient_initial_laws_short` (no canonical-representation theorem) |
| Conj. `hierarchy`, `k = 3` | `hierarchy_k3` (in `SSPLean.K3Complete`) | **proved unconditionally**; `SSP.K2Concrete.all_transient_initial_k3` |
| Lem. `mixture` | `mixture_closure` | new |
| Thm. `order3` | `order3_bound_unconditional` | `hierarchy_k2` + `SSP.order3_ssp_bound` |
| Rem. `uniqueness` (equality at `r = 2s`) | — | **proved**: `SSP.orderTwo_two_mul_iff_halfRateSerialErlang`, `SSP.orderTwo_two_mul_iff_halfRateSerialMat` (in `SSPLean.SSPBoundEquality`) |
| Def. (Algebraic Stability) | `AlgebraicallyStable` | definition |
| Lem. `partialsums` | `partial_sums` | `SSP.partial_sum_lemma` |
| Thm. `barrier` | `barrier` | `SSP.no_order3_algebraically_stable` |
| Def. (A-stability conditions) | `AStabilityData` | definition |
| Lem. `collapse` | `collapse_sum_identity` | new (algebraic core) |
| Conj. `astability` | `AStabilityBarrier` | open at `s = 4`; false for `s ≥ 5` |
| Lem. `targetstatement` (App. A, elementary proof of Lem. `componentbound`) | — | `SSP.componentBound_unconditional` |
-/

end SSP.MainRevised
