import SSPLean.K2AllStages
import SSPLean.ThirdMomentBridge
import SSPLean.QSequenceCrossing

/-!
# Connecting the all-stage `k = 2` theorem to concrete absorption laws

`SSPLean.K2AllStages` proves the algebraic induction for an abstract family of laws.  This file
instantiates its moment functions with the actual Stieltjes absorption-time measure constructed
from a finite nonnegative substochastic matrix.  Consequently the only remaining input to the
all-stage theorem is now visibly the representation data: the base-case representation through
three states and the strong-Markov state-return certificate in larger orders.
-/

open scoped Matrix.Norms.Operator
open NormedSpace Matrix Set Filter MeasureTheory SSP.Survival Finset SSP.Chain

set_option autoImplicit false

namespace SSP.K2Concrete

/-- A deterministic-start absorption law in the strict-contraction chart used by the analytic
moment development. -/
structure AbsorptionStart (s : ℕ) where
  Q : Matrix (Fin s) (Fin s) ℝ
  θ : ℝ
  hQ : ∀ i j, 0 ≤ Q i j
  hrow : ∀ i, ∑ j, Q i j ≤ 1
  hu : IsUnit (1 - Q)
  hnorm : ‖Q‖ ≤ θ
  hθ : θ < 1
  i : Fin s

/-- The concrete absorption-time measure belonging to a deterministic start. -/
noncomputable def law {s : ℕ} (X : AbsorptionStart s) : Measure ℝ :=
  (survivalStieltjes X.Q X.hQ X.hrow X.i).measure

/-- First raw moment of the concrete absorption-time law. -/
noncomputable def moment1 (s : ℕ) (X : AbsorptionStart s) : ℝ :=
  ∫ x, id x ∂law X

/-- Second raw moment of the concrete absorption-time law. -/
noncomputable def moment2 (s : ℕ) (X : AbsorptionStart s) : ℝ :=
  ∫ x, (id x)^2 ∂law X

/-- Third raw moment of the concrete absorption-time law. -/
noncomputable def moment3 (s : ℕ) (X : AbsorptionStart s) : ℝ :=
  ∫ x, (id x)^3 ∂law X

theorem moment1_eq {s : ℕ} (X : AbsorptionStart s) :
    moment1 s X = ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i := by
  exact SSP.Law.expectation_eq X.Q X.θ X.hQ X.hrow X.hu X.hnorm X.hθ X.i

theorem moment2_eq {s : ℕ} (X : AbsorptionStart s) :
    moment2 s X = 2 * ((1 - X.Q)⁻¹.mulVec
      ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) X.i := by
  exact SSP.Law.second_moment_eq X.Q X.θ X.hQ X.hrow X.hu X.hnorm X.hθ X.i

theorem moment3_eq {s : ℕ} (X : AbsorptionStart s) :
    moment3 s X = 6 * ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
      ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) X.i := by
  exact SSP.Law.third_moment_eq X.Q X.θ X.hQ X.hrow X.hu X.hnorm X.hθ X.i

theorem moment1_nonneg {s : ℕ} (X : AbsorptionStart s) : 0 ≤ moment1 s X := by
  exact integral_nonneg_of_ae (SSP.Law.ae_nonneg X.Q X.hQ X.hrow X.i)

theorem moment2_nonneg {s : ℕ} (X : AbsorptionStart s) : 0 ≤ moment2 s X := by
  exact integral_nonneg fun x => sq_nonneg (id x)

theorem moment3_nonneg {s : ℕ} (X : AbsorptionStart s) : 0 ≤ moment3 s X := by
  apply integral_nonneg_of_ae
  filter_upwards [SSP.Law.ae_nonneg X.Q X.hQ X.hrow X.i] with x hx
  exact pow_nonneg hx 3

/-- Every concrete absorption time is strictly positive almost surely, and therefore has
strictly positive mean. -/
theorem moment1_pos {s : ℕ} (X : AbsorptionStart s) : 0 < moment1 s X := by
  have hnonneg : 0 ≤ᵐ[law X] (id : ℝ → ℝ) := by
    simpa [law] using SSP.Law.ae_nonneg X.Q X.hQ X.hrow X.i
  have hint : Integrable (id : ℝ → ℝ) (law X) := by
    simpa [law] using SSP.Law.integrable_id X.Q X.θ X.hQ X.hrow X.hnorm X.hθ X.i
  rw [moment1, integral_pos_iff_support_of_nonneg_ae hnonneg hint]
  have hIoi : law X (Ioi 0) = 1 := by
    rw [law]
    simpa using SSP.Law.measure_Ioi_eq_survival X.Q X.θ X.hQ X.hrow X.hnorm X.hθ X.i
      0 le_rfl
  have hsub : Ioi (0 : ℝ) ⊆ Function.support (id : ℝ → ℝ) := by
    intro x hx
    simpa [Function.mem_support] using ne_of_gt hx
  calc
    0 < (1 : ENNReal) := zero_lt_one
    _ = law X (Ioi 0) := hIoi.symm
    _ ≤ law X (Function.support (id : ℝ → ℝ)) := measure_mono hsub

/-- The genuine exit rate from the selected transient state, after diagonal self-loops in the
uniformized chain have been absorbed into its exponential clock. -/
noncomputable def exitRate {s : ℕ} (X : AbsorptionStart s) : ℝ :=
  1 - X.Q X.i X.i

/-- The genuine exit rate from the selected transient state is positive.  A zero value would
make the corresponding row of `I - Q` vanish, contradicting invertibility. -/
theorem exitRate_pos {s : ℕ} (X : AbsorptionStart s) : 0 < exitRate X := by
  unfold exitRate
  have hdiag_le_sum : X.Q X.i X.i ≤ ∑ j, X.Q X.i j := by
    exact Finset.single_le_sum (fun j _ => X.hQ X.i j) (Finset.mem_univ X.i)
  have hdiag_le_one : X.Q X.i X.i ≤ 1 := hdiag_le_sum.trans (X.hrow X.i)
  have hexit_nonneg : 0 ≤ 1 - X.Q X.i X.i := sub_nonneg.mpr hdiag_le_one
  rcases eq_or_lt_of_le hexit_nonneg with hzero | hpos
  · exfalso
    have hdiag : X.Q X.i X.i = 1 := by linarith
    have hsum : ∑ j, X.Q X.i j = 1 := le_antisymm (X.hrow X.i) (by
      calc
        1 = X.Q X.i X.i := hdiag.symm
        _ ≤ ∑ j, X.Q X.i j := hdiag_le_sum)
    have herase : ∑ j ∈ (Finset.univ : Finset (Fin s)).erase X.i, X.Q X.i j = 0 := by
      have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
        (f := fun j => X.Q X.i j) (Finset.mem_univ X.i)
      linarith
    have hoffdiag : ∀ j, j ≠ X.i → X.Q X.i j = 0 := by
      intro j hji
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => X.hQ X.i k)).mp herase
      exact hall j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    have hrowzero : ∀ j, (1 - X.Q) X.i j = 0 := by
      intro j
      by_cases hji : j = X.i
      · subst j
        simp [Matrix.sub_apply, hdiag]
      · simp [Matrix.sub_apply, Ne.symm hji, hoffdiag j hji]
    have hdetzero : (1 - X.Q).det = 0 := Matrix.det_eq_zero_of_row_eq_zero X.i hrowzero
    exact ((Matrix.isUnit_iff_isUnit_det _).mp X.hu).ne_zero hdetzero
  · exact hpos

/-- Mean of the exponential holding time at the selected state after diagonal self-loops have
been absorbed into its clock. -/
noncomputable def holdingMean {s : ℕ} (X : AbsorptionStart s) : ℝ :=
  (exitRate X)⁻¹

theorem holdingMean_pos {s : ℕ} (X : AbsorptionStart s) : 0 < holdingMean X := by
  exact inv_pos.mpr (exitRate_pos X)

/-- Conditional probability, at a genuine departure from the selected state, of jumping to
transient state `j`.  Its value at the selected state itself is set to zero. -/
noncomputable def departureWeight {s : ℕ} (X : AbsorptionStart s) (j : Fin s) : ℝ :=
  if j = X.i then 0 else X.Q X.i j / exitRate X

/-- Conditional probability of direct absorption at a genuine departure from the selected
state. -/
noncomputable def directExitWeight {s : ℕ} (X : AbsorptionStart s) : ℝ :=
  (1 - ∑ j, X.Q X.i j) / exitRate X

theorem departureWeight_nonneg {s : ℕ} (X : AbsorptionStart s) (j : Fin s) :
    0 ≤ departureWeight X j := by
  unfold departureWeight
  split_ifs
  · exact le_rfl
  · exact div_nonneg (X.hQ X.i j) (exitRate_pos X).le

@[simp] theorem departureWeight_self {s : ℕ} (X : AbsorptionStart s) :
    departureWeight X X.i = 0 := by
  simp [departureWeight]

theorem directExitWeight_nonneg {s : ℕ} (X : AbsorptionStart s) :
    0 ≤ directExitWeight X := by
  exact div_nonneg (sub_nonneg.mpr (X.hrow X.i)) (exitRate_pos X).le

/-- The transient destinations and direct absorption exhaust a genuine departure. -/
theorem departureWeight_sum_add_direct {s : ℕ} (X : AbsorptionStart s) :
    (∑ j, departureWeight X j) + directExitWeight X = 1 := by
  have hsplitQ := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
    (f := fun j => X.Q X.i j) (Finset.mem_univ X.i)
  have hsplitP := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
    (f := fun j => departureWeight X j) (Finset.mem_univ X.i)
  have herase : ∑ j ∈ (Finset.univ : Finset (Fin s)).erase X.i,
      departureWeight X j =
        (∑ j ∈ (Finset.univ : Finset (Fin s)).erase X.i, X.Q X.i j) /
          exitRate X := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ X.i := (Finset.mem_erase.mp hj).1
    simp [departureWeight, hji]
  rw [← hsplitP, departureWeight_self, add_zero, herase]
  unfold directExitWeight exitRate
  have hne : 1 - X.Q X.i X.i ≠ 0 := ne_of_gt (exitRate_pos X)
  field_simp [hne]
  linarith

/-- A nonnegative absorption time with zero mean vanishes almost everywhere, so all of the
higher moments used by the induction vanish as well. -/
theorem higher_moments_eq_zero_of_moment1_eq_zero {s : ℕ} (X : AbsorptionStart s)
    (h : moment1 s X = 0) : moment2 s X = 0 ∧ moment3 s X = 0 := by
  have hnonneg : 0 ≤ᵐ[law X] (id : ℝ → ℝ) := by
    simpa [law] using SSP.Law.ae_nonneg X.Q X.hQ X.hrow X.i
  have hint : Integrable (id : ℝ → ℝ) (law X) := by
    simpa [law] using SSP.Law.integrable_id X.Q X.θ X.hQ X.hrow X.hnorm X.hθ X.i
  have hid0 : (id : ℝ → ℝ) =ᵐ[law X] 0 := by
    exact (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp h
  constructor
  · unfold moment2
    apply integral_eq_zero_of_ae
    filter_upwards [hid0] with x hx
    change x = 0 at hx
    simp [hx]
  · unfold moment3
    apply integral_eq_zero_of_ae
    filter_upwards [hid0] with x hx
    change x = 0 at hx
    simp [hx]

/-- The one-state base case is an identity; no representation theorem is needed. -/
theorem stageBound_one (X : AbsorptionStart 1) :
    SSP.K2AllStages.StageBound 1 (moment1 1 X) (moment2 1 X) (moment3 1 X) := by
  rw [moment1_eq X, moment2_eq X, moment3_eq X]
  unfold SSP.K2AllStages.StageBound
  have hi : X.i = (0 : Fin 1) := Subsingleton.elim _ _
  rw [hi]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, mul_one]
  ring_nf
  exact le_rfl

/-! ## The complete two-state base case -/

/-- The rational moment inequality underlying the two-cycle calculation.  Clearing the positive
fourth power of the determinant reduces it exactly to `cyc2N_nonneg`. -/
theorem twoCycleClosed (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hδ : a * b * (1 - u * v) ≠ 0) :
    let δ := a * b * (1 - u * v)
    let z1 := (b + a * u) / δ
    let z2 := (b * (b + a * u) + a * u * (b * v + a)) / δ^2
    let z3 := (b * (b * (b + a * u) + a * u * (b * v + a))
      + a * u * (b * v * (b + a * u) + a * (b * v + a))) / δ^3
    16 * z2^2 ≤ 18 * z1 * z3 := by
  dsimp
  have hp := cyc2N_nonneg a b u v ha hb hu0 hu1 hv0 hv1
  have h1uv : 1 - u * v ≠ 0 := by
    intro h
    apply hδ
    rw [h]
    ring
  have hid : (a * b * (1 - u * v))^4 *
      (18 * ((b + a * u) / (a * b * (1 - u * v))) *
        ((b * (b * (b + a * u) + a * u * (b * v + a))
          + a * u * (b * v * (b + a * u) + a * (b * v + a))) /
            (a * b * (1 - u * v))^3)
      - 16 * ((b * (b + a * u) + a * u * (b * v + a)) /
          (a * b * (1 - u * v))^2)^2)
      = 2 * cyc2N a b u v := by
    field_simp [h1uv, ha.ne', hb.ne']
    unfold cyc2N
    ring
  have hδ4 : 0 < (a * b * (1 - u * v))^4 := pow_pos (by
    have huv : u * v ≤ 1 := by
      calc u * v ≤ u * 1 := mul_le_mul_of_nonneg_left hv1 hu0
        _ = u := by ring
        _ ≤ 1 := hu1
    exact mul_pos (mul_pos ha hb)
      (lt_of_le_of_ne (sub_nonneg.mpr huv) h1uv.symm)) 4
  have hprod : 0 ≤ (a * b * (1 - u * v))^4 *
      (18 * ((b + a * u) / (a * b * (1 - u * v))) *
        ((b * (b * (b + a * u) + a * u * (b * v + a))
          + a * u * (b * v * (b + a * u) + a * (b * v + a))) /
            (a * b * (1 - u * v))^3)
      - 16 * ((b * (b + a * u) + a * u * (b * v + a)) /
          (a * b * (1 - u * v))^2)^2) := by
    rw [hid]
    positivity
  exact (mul_nonneg_iff_of_pos_left hδ4).mp hprod |> sub_nonneg.mp

set_option maxHeartbeats 1000000 in
-- Explicit normalization of three nested products of a symbolic `2 × 2` inverse is expensive.
/-- Resolvent inequality for the first state of a general two-cycle rate matrix.  The larger
heartbeat budget is for normalization of the explicit nested `2 × 2` inverse products. -/
theorem twoCycleMatrixStartZero (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hδ : a * b * (1 - u * v) ≠ 0) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![a, -a * u; -b * v, b]
    let N := A⁻¹
    16 * (N.mulVec (N.mulVec (fun _ => (1 : ℝ))) 0)^2
      ≤ 18 * (N.mulVec (fun _ => (1 : ℝ)) 0) *
        (N.mulVec (N.mulVec (N.mulVec (fun _ => (1 : ℝ)))) 0) := by
  dsimp
  have hn :
      (!![a, -a * u; -b * v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
        = !![b / (a * b * (1 - u * v)), (a * u) / (a * b * (1 - u * v));
            (b * v) / (a * b * (1 - u * v)), a / (a * b * (1 - u * v))] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two,
        Ring.inverse_eq_inv] <;> field_simp [hδ]
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![a, -a * u; -b * v, b]
  have hz1 : (A⁻¹.mulVec (fun _ => (1 : ℝ))) 0 =
      (b + a * u) / (a * b * (1 - u * v)) := by
    rw [show A⁻¹ = _ from hn]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hz2 : (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ)))) 0 =
      (b * (b + a * u) + a * u * (b * v + a)) / (a * b * (1 - u * v))^2 := by
    rw [show A⁻¹ = _ from hn]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp [hδ]
  have hz3 : (A⁻¹.mulVec (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ))))) 0 =
      (b * (b * (b + a * u) + a * u * (b * v + a))
        + a * u * (b * v * (b + a * u) + a * (b * v + a))) /
          (a * b * (1 - u * v))^3 := by
    rw [show A⁻¹ = _ from hn]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp [hδ]
  change 16 * (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ))) 0)^2 ≤
    18 * (A⁻¹.mulVec (fun _ => (1 : ℝ)) 0) *
      (A⁻¹.mulVec (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ)))) 0)
  rw [hz1, hz2, hz3]
  exact twoCycleClosed a b u v ha hb hu0 hu1 hv0 hv1 hδ

set_option maxHeartbeats 1000000 in
-- Explicit normalization of three nested products of a symbolic `2 × 2` inverse is expensive.
/-- Resolvent inequality for the second state of a general two-cycle rate matrix.  The larger
heartbeat budget is for normalization of the explicit nested `2 × 2` inverse products. -/
theorem twoCycleMatrixStartOne (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hδ : a * b * (1 - u * v) ≠ 0) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![a, -a * u; -b * v, b]
    let N := A⁻¹
    16 * (N.mulVec (N.mulVec (fun _ => (1 : ℝ))) 1)^2
      ≤ 18 * (N.mulVec (fun _ => (1 : ℝ)) 1) *
        (N.mulVec (N.mulVec (N.mulVec (fun _ => (1 : ℝ)))) 1) := by
  dsimp
  have hδ' : b * a * (1 - v * u) ≠ 0 := by
    intro h
    apply hδ
    nlinarith
  have hn :
      (!![a, -a * u; -b * v, b] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
        = !![b / (a * b * (1 - u * v)), (a * u) / (a * b * (1 - u * v));
            (b * v) / (a * b * (1 - u * v)), a / (a * b * (1 - u * v))] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two,
        Ring.inverse_eq_inv] <;> field_simp [hδ]
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![a, -a * u; -b * v, b]
  have hz1 : (A⁻¹.mulVec (fun _ => (1 : ℝ))) 1 =
      (a + b * v) / (b * a * (1 - v * u)) := by
    rw [show A⁻¹ = _ from hn]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp [hδ, hδ']
    ring
  have hz2 : (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ)))) 1 =
      (a * (a + b * v) + b * v * (a * u + b)) / (b * a * (1 - v * u))^2 := by
    rw [show A⁻¹ = _ from hn]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp [hδ, hδ']
    ring
  have hz3 : (A⁻¹.mulVec (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ))))) 1 =
      (a * (a * (a + b * v) + b * v * (a * u + b))
        + b * v * (a * u * (a + b * v) + b * (a * u + b))) /
          (b * a * (1 - v * u))^3 := by
    rw [show A⁻¹ = _ from hn]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp [hδ, hδ']
    ring
  change 16 * (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ))) 1)^2 ≤
    18 * (A⁻¹.mulVec (fun _ => (1 : ℝ)) 1) *
      (A⁻¹.mulVec (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ)))) 1)
  rw [hz1, hz2, hz3]
  exact twoCycleClosed b a v u hb ha hv0 hv1 hu0 hu1 hδ'

set_option maxHeartbeats 1000000 in
-- This invokes both symbolic start-state calculations for an arbitrary concrete matrix.
/-- Every concrete two-state absorption law satisfies the sharp `k = 2` inequality.  The larger
heartbeat budget is for the two explicit finite-matrix normalizations. -/
theorem stageBound_two (X : AbsorptionStart 2) :
    SSP.K2AllStages.StageBound 2 (moment1 2 X) (moment2 2 X) (moment3 2 X) := by
  let a := 1 - X.Q 0 0
  let b := 1 - X.Q 1 1
  let u := X.Q 0 1 / a
  let v := X.Q 1 0 / b
  have hrow0 := X.hrow (0 : Fin 2)
  have hrow1 := X.hrow (1 : Fin 2)
  rw [Fin.sum_univ_two] at hrow0 hrow1
  have hca : X.Q 0 1 ≤ a := by dsimp [a]; linarith
  have hdb : X.Q 1 0 ≤ b := by dsimp [b]; linarith
  have ha0 : 0 ≤ a := (X.hQ 0 1).trans hca
  have hb0 : 0 ≤ b := (X.hQ 1 0).trans hdb
  have hdetunit := (Matrix.isUnit_iff_isUnit_det _).mp X.hu
  have ha : 0 < a := by
    rcases eq_or_lt_of_le ha0 with ha' | ha'
    · exfalso
      have hc : X.Q 0 1 = 0 := by
        rw [← ha'] at hca
        exact le_antisymm hca (X.hQ 0 1)
      apply hdetunit.ne_zero
      rw [Matrix.det_fin_two]
      simp only [Matrix.sub_apply, Matrix.one_apply]
      norm_num
      rw [show 1 - X.Q 0 0 = 0 from ha'.symm, hc]
      ring
    · exact ha'
  have hb : 0 < b := by
    rcases eq_or_lt_of_le hb0 with hb' | hb'
    · exfalso
      have hd : X.Q 1 0 = 0 := by
        rw [← hb'] at hdb
        exact le_antisymm hdb (X.hQ 1 0)
      apply hdetunit.ne_zero
      rw [Matrix.det_fin_two]
      simp only [Matrix.sub_apply, Matrix.one_apply]
      norm_num
      rw [show 1 - X.Q 1 1 = 0 from hb'.symm, hd]
      ring
    · exact hb'
  have hu0 : 0 ≤ u := div_nonneg (X.hQ 0 1) ha.le
  have hu1 : u ≤ 1 := (div_le_one ha).mpr hca
  have hv0 : 0 ≤ v := div_nonneg (X.hQ 1 0) hb.le
  have hv1 : v ≤ 1 := (div_le_one hb).mpr hdb
  have hau : a * u = X.Q 0 1 := by dsimp [u]; field_simp [ha.ne']
  have hbv : b * v = X.Q 1 0 := by dsimp [v]; field_simp [hb.ne']
  have hA : 1 - X.Q = (!![a, -a * u; -b * v, b] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [a, Matrix.sub_apply]
    · simp only [Matrix.sub_apply, Matrix.one_apply]
      norm_num
      rw [hau]
    · simp only [Matrix.sub_apply, Matrix.one_apply]
      norm_num
      rw [hbv]
    · simp [b, Matrix.sub_apply]
  have hδ : a * b * (1 - u * v) ≠ 0 := by
    intro hzero
    apply hdetunit.ne_zero
    rw [hA, Matrix.det_fin_two]
    norm_num
    calc a * b - a * u * (b * v) = a * b * (1 - u * v) := by ring
      _ = 0 := hzero
  have hmain := twoCycleMatrixStartZero a b u v ha hb hu0 hu1 hv0 hv1 hδ
  have hmain' := twoCycleMatrixStartOne a b u v ha hb hu0 hu1 hv0 hv1 hδ
  rw [moment1_eq X, moment2_eq X, moment3_eq X]
  unfold SSP.K2AllStages.StageBound
  push_cast
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
  rw [hA]
  generalize hk : X.i = k
  fin_cases k
  · convert hmain using 1 <;> simp only [Fin.zero_eta] <;> ring
  · convert hmain' using 1 <;> simp only [Fin.mk_one] <;> ring

/-! ## The exact order-three representation interface -/

/-- Data asserting that a concrete three-state absorption law has the standard He--Zhang
canonical representation, stated only through the three moments needed here.  The cited
representation theorem should construct this structure; all subsequent inequality reasoning is
already internal to Lean. -/
structure OrderThreeCanonicalCertificate (X : AbsorptionStart 3) where
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  x13 : ℝ
  π : Fin 3 → ℝ
  x1_pos : 0 < x1
  x2_pos : 0 < x2
  x3_pos : 0 < x3
  x13_nonneg : 0 ≤ x13
  x13_lt : x13 < x1
  π_nonneg : ∀ i, 0 ≤ π i
  moment1_eq : moment1 3 X = ∑ i, π i * SSP.Canonical.canMoment x1 x2 x3 x13 0 i
  moment2_eq : moment2 3 X = 2 * ∑ i, π i * SSP.Canonical.canMoment x1 x2 x3 x13 1 i
  moment3_eq : moment3 3 X = 6 * ∑ i, π i * SSP.Canonical.canMoment x1 x2 x3 x13 2 i

/-- The existing canonical three-state certificate proves the concrete order-three base case. -/
theorem stageBound_three_of_canonical (X : AbsorptionStart 3)
    (c : OrderThreeCanonicalCertificate X) :
    SSP.K2AllStages.StageBound 3 (moment1 3 X) (moment2 3 X) (moment3 3 X) := by
  have h := SSP.Canonical.canonical_hierarchy_s3_moments
    c.x1 c.x2 c.x3 c.x13 c.π c.x1_pos c.x2_pos c.x3_pos
    c.x13_nonneg c.x13_lt c.π_nonneg
  unfold SSP.K2AllStages.StageBound
  rw [c.moment1_eq, c.moment2_eq, c.moment3_eq]
  norm_num at h ⊢
  nlinarith

/-! ## Discharging the Aldous--Shepp fields of the renewal certificate -/

/-- The concrete Aldous--Shepp second-moment inequality, expressed in raw moments. -/
theorem aldousSheppMoment {s : ℕ} (hs : 1 ≤ s) (X : AbsorptionStart s) :
    ((s : ℝ) + 1) / s * (moment1 s X)^2 ≤ moment2 s X := by
  let q : ℕ → ℕ → ℝ := SSP.ofMat s X.Q
  have hto : SSP.toMat s q = X.Q := by
    ext i j
    simp [q, SSP.toMat, SSP.ofMat]
  have hq : ∀ i j, 0 ≤ q i j := by
    intro i j
    simp only [q, SSP.ofMat]
    split_ifs with h
    · exact X.hQ ⟨i, h.1⟩ ⟨j, h.2⟩
    · exact le_rfl
  have hsub : ∀ i < s, ∑ j ∈ range s, q i j ≤ 1 := by
    intro i hi
    rw [← Fin.sum_univ_eq_sum_range (fun j => q i j) s]
    simpa [q, SSP.ofMat, hi] using X.hrow ⟨i, hi⟩
  have hinv : IsUnit (1 - SSP.toMat s q) := by simpa [hto] using X.hu
  have hcb := SSP.componentBound_unconditional_of_invertible' s q hq hsub hinv hs
    (X.i : ℕ) X.i.isLt
  rw [SSP.Bridge.rowSum_invMat_eq q X.i X.i.isLt,
    SSP.Bridge.rowSum2_invMat_eq q X.i X.i.isLt, hto] at hcb
  rw [moment1_eq X, moment2_eq X]
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
  rw [div_mul_eq_mul_div, le_div_iff₀ hs1] at hcb
  nlinarith

/-- If a law uses at most `n-1` transient states, its own Aldous--Shepp bound implies the weaker
coefficient `n/(n-1)` required by the order-`n` renewal step. -/
theorem aldousSheppForParent {s n : ℕ} (hs : 1 ≤ s) (hsn : s < n)
    (X : AbsorptionStart s) :
    (n : ℝ) / (n - 1) * (moment1 s X)^2 ≤ moment2 s X := by
  have hn2 : 2 ≤ n := by omega
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hsn' : (s : ℝ) ≤ (n : ℝ) - 1 := by
    have hsnNat : s + 1 ≤ n := by omega
    have hsnR : (s : ℝ) + 1 ≤ n := by exact_mod_cast hsnNat
    linarith
  have hcoef : (n : ℝ) / (n - 1) ≤ ((s : ℝ) + 1) / s := by
    rw [div_le_div_iff₀ hn1 hs0]
    nlinarith
  calc
    (n : ℝ) / (n - 1) * (moment1 s X)^2
        ≤ ((s : ℝ) + 1) / s * (moment1 s X)^2 :=
          mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ ≤ moment2 s X := aldousSheppMoment hs X

/-- The genuinely probabilistic/state-return data, with the Aldous--Shepp inequalities omitted:
those are derived automatically by `toRenewalCertificate`. -/
structure StateReturnData (n : ℕ) (X : AbsorptionStart n) where
  su : ℕ
  sv : ℕ
  su_pos : 1 ≤ su
  sv_pos : 1 ≤ sv
  su_lt : su < n
  sv_lt : sv < n
  U : AbsorptionStart su
  V : AbsorptionStart sv
  x : ℝ
  p : ℝ
  q : ℝ
  x_pos : 0 < x
  p_nonneg : 0 ≤ p
  q_pos : 0 < q
  prob_sum : p + q = 1
  moment1_decomp : moment1 n X = SSP.K2AllStages.renewalM1 x
    (moment1 su U) (moment1 sv V) p q
  moment2_decomp : moment2 n X = SSP.K2AllStages.renewalM2 x
    (moment1 su U) (moment1 sv V) p q (moment2 su U) (moment2 sv V)
  moment3_decomp : moment3 n X = SSP.K2AllStages.renewalM3 x
    (moment1 su U) (moment1 sv V) p q (moment2 su U) (moment2 sv V)
      (moment3 su U) (moment3 sv V)

/-- Concrete state-return data produces the full abstract renewal certificate; in particular,
the two variance bounds are no longer part of the external interface. -/
def StateReturnData.toRenewalCertificate {n : ℕ} {X : AbsorptionStart n}
    (d : StateReturnData n X) :
    SSP.K2AllStages.RenewalCertificate AbsorptionStart moment1 moment2 moment3 n X where
  su := d.su
  sv := d.sv
  su_pos := d.su_pos
  sv_pos := d.sv_pos
  su_lt := d.su_lt
  sv_lt := d.sv_lt
  U := d.U
  V := d.V
  x := d.x
  p := d.p
  q := d.q
  x_pos := d.x_pos
  p_nonneg := d.p_nonneg
  q_pos := d.q_pos
  prob_sum := d.prob_sum
  return_mean_pos := fun _ => moment1_pos d.U
  terminal_zero := higher_moments_eq_zero_of_moment1_eq_zero d.V
  as_U := aldousSheppForParent d.su_pos d.su_lt d.U
  as_V := aldousSheppForParent d.sv_pos d.sv_lt d.V
  moment1 := d.moment1_decomp
  moment2 := d.moment2_decomp
  moment3 := d.moment3_decomp

/-- The abstract induction specialized to the repository's concrete absorption-time measures.

All moment-side premises are discharged here.  The two remaining hypotheses are precisely the
base-case representation and the state-return decomposition.
-/
theorem all_concrete_starts_of_renewal
    (hbase : ∀ s, 1 ≤ s → s ≤ 3 → ∀ X : AbsorptionStart s,
      SSP.K2AllStages.StageBound s (moment1 s X) (moment2 s X) (moment3 s X))
    (hrenew : ∀ n, 4 ≤ n → ∀ X : AbsorptionStart n,
      SSP.K2AllStages.RenewalCertificate AbsorptionStart moment1 moment2 moment3 n X) :
    ∀ n, 1 ≤ n → ∀ X : AbsorptionStart n,
      SSP.K2AllStages.StageBound n (moment1 n X) (moment2 n X) (moment3 n X) := by
  exact SSP.K2AllStages.all_stages_of_renewal AbsorptionStart moment1 moment2 moment3
    (fun _ X => moment1_nonneg X) (fun _ X => moment2_nonneg X)
    (fun _ X => moment3_nonneg X) hbase hrenew

/-- A version of the concrete induction in which the elementary one-state base case has already
been discharged.  Only orders two and three remain in the base representation interface. -/
theorem all_concrete_starts_of_renewal_from_two_three
    (hbase23 : ∀ s, 2 ≤ s → s ≤ 3 → ∀ X : AbsorptionStart s,
      SSP.K2AllStages.StageBound s (moment1 s X) (moment2 s X) (moment3 s X))
    (hrenew : ∀ n, 4 ≤ n → ∀ X : AbsorptionStart n,
      SSP.K2AllStages.RenewalCertificate AbsorptionStart moment1 moment2 moment3 n X) :
    ∀ n, 1 ≤ n → ∀ X : AbsorptionStart n,
      SSP.K2AllStages.StageBound n (moment1 n X) (moment2 n X) (moment3 n X) := by
  apply all_concrete_starts_of_renewal
  · intro s hs1 hs3 X
    rcases Nat.eq_or_lt_of_le hs1 with rfl | hs2
    · exact stageBound_one X
    · exact hbase23 s hs2 hs3 X
  · exact hrenew

/-- The concrete induction with both elementary low-order cases discharged.  Its only base-case
input is now the order-three representation theorem. -/
theorem all_concrete_starts_of_renewal_from_three
    (hbase3 : ∀ X : AbsorptionStart 3,
      SSP.K2AllStages.StageBound 3 (moment1 3 X) (moment2 3 X) (moment3 3 X))
    (hrenew : ∀ n, 4 ≤ n → ∀ X : AbsorptionStart n,
      SSP.K2AllStages.RenewalCertificate AbsorptionStart moment1 moment2 moment3 n X) :
    ∀ n, 1 ≤ n → ∀ X : AbsorptionStart n,
      SSP.K2AllStages.StageBound n (moment1 n X) (moment2 n X) (moment3 n X) := by
  apply all_concrete_starts_of_renewal_from_two_three
  · intro s hs2 hs3 X
    have hs : s = 2 ∨ s = 3 := by omega
    rcases hs with rfl | rfl
    · exact stageBound_two X
    · exact hbase3 X
  · exact hrenew

/-- End-to-end concrete inequality from the two remaining representation constructions:
He--Zhang at order three and the state-return certificate from order four onward. -/
theorem all_concrete_starts
    (hcanonical : ∀ X : AbsorptionStart 3, OrderThreeCanonicalCertificate X)
    (hrenew : ∀ n, 4 ≤ n → ∀ X : AbsorptionStart n,
      SSP.K2AllStages.RenewalCertificate AbsorptionStart moment1 moment2 moment3 n X) :
    ∀ n, 1 ≤ n → ∀ X : AbsorptionStart n,
      SSP.K2AllStages.StageBound n (moment1 n X) (moment2 n X) (moment3 n X) := by
  exact all_concrete_starts_of_renewal_from_three
    (fun X => stageBound_three_of_canonical X (hcanonical X)) hrenew

/-- End-to-end concrete inequality with the probabilistic input reduced to the raw
state-return data.  The Aldous--Shepp side conditions required by the abstract induction are
filled in internally by `StateReturnData.toRenewalCertificate`. -/
theorem all_concrete_starts_from_state_return
    (hcanonical : ∀ X : AbsorptionStart 3, OrderThreeCanonicalCertificate X)
    (hreturn : ∀ n, 4 ≤ n → ∀ X : AbsorptionStart n, StateReturnData n X) :
    ∀ n, 1 ≤ n → ∀ X : AbsorptionStart n,
      SSP.K2AllStages.StageBound n (moment1 n X) (moment2 n X) (moment3 n X) := by
  exact all_concrete_starts hcanonical
    (fun n hn X => (hreturn n hn X).toRenewalCertificate)

/-- Resolvent form of the deterministic-start conclusion. -/
theorem resolvent_bound_of_stageBound {s : ℕ} (X : AbsorptionStart s)
    (h : SSP.K2AllStages.StageBound s (moment1 s X) (moment2 s X) (moment3 s X)) :
    (s + 2) *
        (2 * ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
          (fun _ => (1 : ℝ)))) X.i)^2
      ≤ (s + 1) * ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i *
        (6 * ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
          ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) X.i) := by
  rw [← moment1_eq X, ← moment2_eq X, ← moment3_eq X]
  exact h

/-- Replace only the initial state while retaining the same transient matrix and proofs. -/
def withStart {s : ℕ} (X : AbsorptionStart s) (i : Fin s) : AbsorptionStart s :=
  { X with i := i }

/-- Mixture closure for a concrete matrix: deterministic-start bounds imply the bound for every
nonnegative initial weight vector.  Normalization of the weights is not needed for this
homogeneous inequality. -/
theorem initial_mixture_bound {s : ℕ} (X : AbsorptionStart s) (π : Fin s → ℝ)
    (hπ : ∀ i, 0 ≤ π i)
    (hdet : ∀ i, SSP.K2AllStages.StageBound s
      (moment1 s (withStart X i)) (moment2 s (withStart X i))
      (moment3 s (withStart X i))) :
    ((s : ℝ) + 2) * (∑ i, π i * moment2 s (withStart X i))^2
      ≤ ((s : ℝ) + 1) *
        ((∑ i, π i * moment1 s (withStart X i)) *
          (∑ i, π i * moment3 s (withStart X i))) := by
  apply SSP.K2AllStages.mixture_closure Finset.univ π
    (fun i => moment1 s (withStart X i))
    (fun i => moment2 s (withStart X i))
    (fun i => moment3 s (withStart X i)) (s : ℝ)
  · positivity
  · intro i _; exact hπ i
  · intro i _; exact moment1_nonneg (withStart X i)
  · intro i _; exact moment2_nonneg (withStart X i)
  · intro i _; exact moment3_nonneg (withStart X i)
  · intro i _
    simpa [SSP.K2AllStages.StageBound, mul_assoc] using hdet i

/-- Fully concrete matrix form of the initial-mixture inequality. -/
theorem initial_mixture_resolvent_bound {s : ℕ} (X : AbsorptionStart s) (π : Fin s → ℝ)
    (hπ : ∀ i, 0 ≤ π i)
    (hdet : ∀ i, SSP.K2AllStages.StageBound s
      (moment1 s (withStart X i)) (moment2 s (withStart X i))
      (moment3 s (withStart X i))) :
    ((s : ℝ) + 2) *
        (∑ i, π i *
          (2 * ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
            (fun _ => (1 : ℝ)))) i))^2
      ≤ ((s : ℝ) + 1) *
        ((∑ i, π i * ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) i) *
          (∑ i, π i *
            (6 * ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
              ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i))) := by
  have h := initial_mixture_bound X π hπ hdet
  simpa [moment1_eq, moment2_eq, moment3_eq, withStart] using h

/-- Deterministic-start resolvent inequality with all of the proved layers assembled and only
the two representation inputs left explicit. -/
theorem resolvent_bound_from_state_return {s : ℕ} (hs : 1 ≤ s) (X : AbsorptionStart s)
    (hcanonical : ∀ Y : AbsorptionStart 3, OrderThreeCanonicalCertificate Y)
    (hreturn : ∀ n, 4 ≤ n → ∀ Y : AbsorptionStart n, StateReturnData n Y) :
    (s + 2) *
        (2 * ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
          (fun _ => (1 : ℝ)))) X.i)^2
      ≤ (s + 1) * ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i *
        (6 * ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
          ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) X.i) := by
  apply resolvent_bound_of_stageBound X
  exact all_concrete_starts_from_state_return hcanonical hreturn s hs X

/-- Arbitrary-initial-distribution resolvent inequality with the proved analytic and algebraic
layers assembled.  The weights may sum to at most one; missing mass is an atom at zero and does
not affect the three positive moments. -/
theorem initial_mixture_resolvent_bound_from_state_return {s : ℕ} (hs : 1 ≤ s)
    (X : AbsorptionStart s) (π : Fin s → ℝ) (hπ : ∀ i, 0 ≤ π i)
    (hcanonical : ∀ Y : AbsorptionStart 3, OrderThreeCanonicalCertificate Y)
    (hreturn : ∀ n, 4 ≤ n → ∀ Y : AbsorptionStart n, StateReturnData n Y) :
    ((s : ℝ) + 2) *
        (∑ i, π i *
          (2 * ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
            (fun _ => (1 : ℝ)))) i))^2
      ≤ ((s : ℝ) + 1) *
        ((∑ i, π i * ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) i) *
          (∑ i, π i *
            (6 * ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
              ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i))) := by
  apply initial_mixture_resolvent_bound X π hπ
  intro i
  exact all_concrete_starts_from_state_return hcanonical hreturn s hs (withStart X i)

end SSP.K2Concrete
