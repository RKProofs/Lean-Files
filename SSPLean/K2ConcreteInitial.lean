import SSPLean.K2Concrete

/-!
# The `k = 2` induction for general initial distributions

A return or terminal excursion obtained by conditioning a finite CTMC need not start at one
deterministic transient state: it normally starts with a distribution on the remaining states.
This module supplies the corresponding concrete law type.  Its weights are allowed to sum to at
most one, with the missing mass representing an atom at zero.  This is the natural class closed by
the state-return decomposition without increasing the number of transient states.
-/

open scoped Matrix.Norms.Operator
open NormedSpace Matrix Set Filter MeasureTheory Finset

set_option autoImplicit false

namespace SSP.K2Concrete

/-- Transient states other than the state at which the return decomposition is based. -/
abbrev OtherState {s : ℕ} (i : Fin s) := {j : Fin s // j ≠ i}

@[simp] theorem card_otherState {s : ℕ} (i : Fin s) :
    Fintype.card (OtherState i) = s - 1 := by
  simp [OtherState]

/-- A fixed reindexing of the states other than `i` by `Fin (s - 1)`. -/
noncomputable def otherStateEquiv {s : ℕ} (i : Fin s) :
    OtherState i ≃ Fin (s - 1) :=
  (Fintype.equivFin (OtherState i)).trans (finCongr (card_otherState i))

/-- Inclusion of the reindexed complement of the selected state into the original state space. -/
noncomputable def otherStateIndex {s : ℕ} (i : Fin s) : Fin (s - 1) → Fin s :=
  fun j => ((otherStateEquiv i).symm j).1

theorem otherStateIndex_ne {s : ℕ} (i : Fin s) (j : Fin (s - 1)) :
    otherStateIndex i j ≠ i :=
  ((otherStateEquiv i).symm j).2

theorem otherStateIndex_injective {s : ℕ} (i : Fin s) :
    Function.Injective (otherStateIndex i) := by
  intro j k h
  apply (otherStateEquiv i).symm.injective
  apply Subtype.ext
  exact h

theorem image_otherStateIndex {s : ℕ} (i : Fin s) :
    (Finset.univ : Finset (Fin (s - 1))).image (otherStateIndex i) =
      (Finset.univ : Finset (Fin s)).erase i := by
  ext j
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨k, _, rfl⟩
    exact Finset.mem_erase.mpr ⟨otherStateIndex_ne i k, Finset.mem_univ _⟩
  · intro hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    let u : OtherState i := ⟨j, hji⟩
    let k : Fin (s - 1) := otherStateEquiv i u
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    change ((otherStateEquiv i).symm k).1 = j
    rw [show (otherStateEquiv i).symm k = u by simp [k]]

/-- The principal transient block obtained by deleting the distinguished state. -/
noncomputable def deletedQ {s : ℕ} (X : AbsorptionStart s) :
    Matrix (Fin (s - 1)) (Fin (s - 1)) ℝ :=
  X.Q.submatrix (otherStateIndex X.i) (otherStateIndex X.i)

theorem deletedQ_nonneg {s : ℕ} (X : AbsorptionStart s) :
    ∀ j k, 0 ≤ deletedQ X j k := by
  intro j k
  exact X.hQ _ _

theorem deletedQ_row_le_one {s : ℕ} (X : AbsorptionStart s) :
    ∀ j, ∑ k, deletedQ X j k ≤ 1 := by
  intro j
  let r := otherStateIndex X.i j
  calc
    ∑ k, deletedQ X j k =
        ∑ k ∈ (Finset.univ : Finset (Fin s)).erase X.i, X.Q r k := by
      unfold deletedQ
      rw [← image_otherStateIndex X.i,
        Finset.sum_image (otherStateIndex_injective X.i).injOn]
      rfl
    _ ≤ ∑ k, X.Q r k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro k _ _
      exact X.hQ r k
    _ ≤ 1 := X.hrow r

/-- Deleting a row and column cannot increase the `L∞` operator norm of a nonnegative
matrix.  This is the analytic fact needed to reuse the strict-contraction chart on the
complementary state space. -/
theorem deletedQ_norm_le {s : ℕ} (X : AbsorptionStart s) :
    ‖deletedQ X‖ ≤ ‖X.Q‖ := by
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  norm_cast
  apply Finset.sup_le
  intro j _
  calc
    ∑ k, ‖deletedQ X j k‖₊ =
        ∑ k ∈ (Finset.univ : Finset (Fin s)).erase X.i,
          ‖X.Q (otherStateIndex X.i j) k‖₊ := by
      unfold deletedQ
      rw [← image_otherStateIndex X.i,
        Finset.sum_image (otherStateIndex_injective X.i).injOn]
      rfl
    _ ≤ ∑ k, ‖X.Q (otherStateIndex X.i j) k‖₊ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun k _ _ => by positivity)
    _ ≤ Finset.univ.sup (fun r => ∑ k, ‖X.Q r k‖₊) := by
      exact Finset.le_sup (s := (Finset.univ : Finset (Fin s)))
        (f := fun r => ∑ k, ‖X.Q r k‖₊)
        (Finset.mem_univ (otherStateIndex X.i j))

/-- Rate/probability weight with which the deleted chain exits by returning to the distinguished
state. -/
noncomputable def returnExitWeight {s : ℕ} (X : AbsorptionStart s)
    (j : Fin (s - 1)) : ℝ :=
  X.Q (otherStateIndex X.i j) X.i

/-- Rate/probability weight with which the deleted chain exits directly to the absorbing state. -/
noncomputable def absorptionExitWeight {s : ℕ} (X : AbsorptionStart s)
    (j : Fin (s - 1)) : ℝ :=
  1 - ∑ k, X.Q (otherStateIndex X.i j) k

theorem returnExitWeight_nonneg {s : ℕ} (X : AbsorptionStart s)
    (j : Fin (s - 1)) : 0 ≤ returnExitWeight X j :=
  X.hQ _ _

theorem absorptionExitWeight_nonneg {s : ℕ} (X : AbsorptionStart s)
    (j : Fin (s - 1)) : 0 ≤ absorptionExitWeight X j :=
  sub_nonneg.mpr (X.hrow _)

/-- Each row of the deleted chain splits into motion among the other states, return to the
distinguished state, and direct absorption. -/
theorem deletedQ_row_add_exits {s : ℕ} (X : AbsorptionStart s)
    (j : Fin (s - 1)) :
    (∑ k, deletedQ X j k) + returnExitWeight X j + absorptionExitWeight X j = 1 := by
  let r := otherStateIndex X.i j
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
    (f := fun k => X.Q r k) (Finset.mem_univ X.i)
  have hdeleted : ∑ k, deletedQ X j k =
      ∑ k ∈ (Finset.univ : Finset (Fin s)).erase X.i, X.Q r k := by
    unfold deletedQ
    rw [← image_otherStateIndex X.i,
      Finset.sum_image (otherStateIndex_injective X.i).injOn]
    rfl
  rw [hdeleted]
  unfold returnExitWeight absorptionExitWeight
  change (∑ k ∈ (Finset.univ : Finset (Fin s)).erase X.i, X.Q r k) +
    X.Q r X.i + (1 - ∑ k, X.Q r k) = 1
  linarith

/-- The complement of a selected state, with any chosen deterministic start, is itself an
absorption model of order `s - 1`. -/
noncomputable def deletedStart {s : ℕ} (X : AbsorptionStart s) (j : Fin (s - 1)) :
    AbsorptionStart (s - 1) where
  Q := deletedQ X
  θ := X.θ
  hQ := deletedQ_nonneg X
  hrow := deletedQ_row_le_one X
  hu := isUnit_one_sub_of_norm_lt_one
    (lt_of_le_of_lt (deletedQ_norm_le X |>.trans X.hnorm) X.hθ)
  hnorm := (deletedQ_norm_le X).trans X.hnorm
  hθ := X.hθ
  i := j

/-- The fundamental matrix of any finite transient substochastic matrix is entrywise
nonnegative.  This version uses the spectral-radius theorem, so it does not assume that the
one-step `L∞` norm is strictly below one. -/
theorem inverse_one_sub_nonneg {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hu : IsUnit (1 - Q)) : ∀ i j, 0 ≤ (1 - Q)⁻¹ i j := by
  intro i j
  have hρ : spectralRadius ℂ (Q.map (algebraMap ℝ ℂ)) < 1 :=
    SSP.Elementary.spectralRadius_lt_one_elementary Q hQ hrow hu
  have hsum : Summable (fun n : ℕ => Q ^ n) :=
    SSP.summable_pow_of_spectralRadius_lt_one Q hρ
  have hrowSum : Summable (fun n : ℕ => (Q ^ n) i) := (Pi.summable.mp hsum) i
  have hentry : (∑' n : ℕ, (Q ^ n) i j) = (1 - Q)⁻¹ i j := by
    have h1 : (∑' n : ℕ, (Q ^ n) i j) = (∑' n : ℕ, (Q ^ n) i) j :=
      (tsum_apply hrowSum).symm
    have h2 : (∑' n : ℕ, (Q ^ n) i) = (∑' n : ℕ, Q ^ n) i :=
      (tsum_apply hsum).symm
    rw [h1, h2, SSP.tsum_pow_eq_inv_one_sub Q hρ]
  rw [← hentry]
  exact tsum_nonneg fun n => SSP.Survival.pow_nonneg_entry Q hQ n i j

/-- The diagonal of a fundamental matrix is at least one: the zeroth term of its Neumann
series is the identity matrix. -/
theorem one_le_inverse_one_sub_diag {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hu : IsUnit (1 - Q)) (i : Fin m) : 1 ≤ (1 - Q)⁻¹ i i := by
  have hρ : spectralRadius ℂ (Q.map (algebraMap ℝ ℂ)) < 1 :=
    SSP.Elementary.spectralRadius_lt_one_elementary Q hQ hrow hu
  have hsum : Summable (fun n : ℕ => Q ^ n) :=
    SSP.summable_pow_of_spectralRadius_lt_one Q hρ
  have hrowSum : Summable (fun n : ℕ => (Q ^ n) i) := (Pi.summable.mp hsum) i
  have hentrySum : Summable (fun n : ℕ => (Q ^ n) i i) := (Pi.summable.mp hrowSum) i
  have hentry : (∑' n : ℕ, (Q ^ n) i i) = (1 - Q)⁻¹ i i := by
    have h1 : (∑' n : ℕ, (Q ^ n) i i) = (∑' n : ℕ, (Q ^ n) i) i :=
      (tsum_apply hrowSum).symm
    have h2 : (∑' n : ℕ, (Q ^ n) i) = (∑' n : ℕ, Q ^ n) i :=
      (tsum_apply hsum).symm
    rw [h1, h2, SSP.tsum_pow_eq_inv_one_sub Q hρ]
  rw [← hentry]
  have hzero : (Q ^ 0) i i = 1 := by simp
  rw [← hzero]
  exact hentrySum.le_tsum 0 fun n _ => SSP.Survival.pow_nonneg_entry Q hQ n i i

/-! ## General transient models

Conditioning a transient chain on its exit route preserves transience and substochasticity, but
can produce rows whose sum is exactly one.  Thus it need not remain in the strict `‖Q‖ < 1`
chart used by `AbsorptionStart`.  The following algebraic model records precisely the hypotheses
needed by the resolvent proof and by the Doob transforms. -/

/-- A deterministic-start finite transient substochastic model, without the unnecessarily strong
one-step strict-contraction assumption. -/
structure TransientStart (s : ℕ) where
  Q : Matrix (Fin s) (Fin s) ℝ
  hQ : ∀ i j, 0 ≤ Q i j
  hrow : ∀ i, ∑ j, Q i j ≤ 1
  hu : IsUnit (1 - Q)
  i : Fin s

/-- The principal block obtained by deleting the distinguished state of a general transient
model. -/
noncomputable def transientDeletedQ {s : ℕ} (X : TransientStart s) :
    Matrix (Fin (s - 1)) (Fin (s - 1)) ℝ :=
  X.Q.submatrix (otherStateIndex X.i) (otherStateIndex X.i)

theorem transientDeletedQ_nonneg {s : ℕ} (X : TransientStart s) :
    ∀ j k, 0 ≤ transientDeletedQ X j k := by
  intro j k
  exact X.hQ _ _

theorem transientDeletedQ_row_le_one {s : ℕ} (X : TransientStart s) :
    ∀ j, ∑ k, transientDeletedQ X j k ≤ 1 := by
  intro j
  let r := otherStateIndex X.i j
  calc
    ∑ k, transientDeletedQ X j k =
        ∑ k ∈ (Finset.univ : Finset (Fin s)).erase X.i, X.Q r k := by
      unfold transientDeletedQ
      rw [← image_otherStateIndex X.i,
        Finset.sum_image (otherStateIndex_injective X.i).injOn]
      rfl
    _ ≤ ∑ k, X.Q r k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro k _ _
      exact X.hQ r k
    _ ≤ 1 := X.hrow r

/-- Every deleted-block path is also a path in the full chain. -/
theorem transientDeletedQ_pow_le {s : ℕ} (X : TransientStart s) (m : ℕ)
    (j k : Fin (s - 1)) :
    (transientDeletedQ X ^ m) j k ≤
      (X.Q ^ m) (otherStateIndex X.i j) (otherStateIndex X.i k) := by
  induction m generalizing j k with
  | zero =>
      simp [Matrix.one_apply, otherStateIndex_injective X.i |>.eq_iff]
  | succ m ih =>
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      calc
        ∑ l, (transientDeletedQ X ^ m) j l * transientDeletedQ X l k ≤
            ∑ l, (X.Q ^ m) (otherStateIndex X.i j) (otherStateIndex X.i l) *
              X.Q (otherStateIndex X.i l) (otherStateIndex X.i k) := by
          apply Finset.sum_le_sum
          intro l _
          exact mul_le_mul_of_nonneg_right (ih j l)
            (X.hQ (otherStateIndex X.i l) (otherStateIndex X.i k))
        _ = ∑ l ∈ (Finset.univ : Finset (Fin (s - 1))).image (otherStateIndex X.i),
              (X.Q ^ m) (otherStateIndex X.i j) l *
                X.Q l (otherStateIndex X.i k) := by
          rw [Finset.sum_image (otherStateIndex_injective X.i).injOn]
        _ ≤ ∑ l, (X.Q ^ m) (otherStateIndex X.i j) l *
              X.Q l (otherStateIndex X.i k) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro l _ _
          exact mul_nonneg (SSP.Survival.pow_nonneg_entry X.Q X.hQ m _ _)
            (X.hQ _ _)

/-- A principal deleted block of a finite transient substochastic matrix is again transient.
The proof compares its path series term-by-term with the summable Neumann series of the full
matrix. -/
theorem transientDeletedQ_isUnit {s : ℕ} (X : TransientStart s) :
    IsUnit (1 - transientDeletedQ X) := by
  have hρ : spectralRadius ℂ (X.Q.map (algebraMap ℝ ℂ)) < 1 :=
    SSP.Elementary.spectralRadius_lt_one_elementary X.Q X.hQ X.hrow X.hu
  have hQsum : Summable (fun m : ℕ => X.Q ^ m) :=
    SSP.summable_pow_of_spectralRadius_lt_one X.Q hρ
  have hBsum : Summable (fun m : ℕ => transientDeletedQ X ^ m) := by
    apply Pi.summable.mpr
    intro j
    apply Pi.summable.mpr
    intro k
    have hrow := (Pi.summable.mp hQsum) (otherStateIndex X.i j)
    have hentry := (Pi.summable.mp hrow) (otherStateIndex X.i k)
    exact Summable.of_nonneg_of_le
      (fun m => SSP.Survival.pow_nonneg_entry (transientDeletedQ X)
        (transientDeletedQ_nonneg X) m j k)
      (fun m => transientDeletedQ_pow_le X m j k) hentry
  apply isUnit_iff_exists_inv.mpr
  exact ⟨∑' m : ℕ, transientDeletedQ X ^ m, hBsum.one_sub_mul_tsum_pow⟩

/-- The deleted block, with an arbitrary selected start, as a general transient model. -/
noncomputable def transientDeletedStart {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) : TransientStart (s - 1) where
  Q := transientDeletedQ X
  hQ := transientDeletedQ_nonneg X
  hrow := transientDeletedQ_row_le_one X
  hu := transientDeletedQ_isUnit X
  i := j

/-- Genuine departure rate at the selected state of a general transient model. -/
noncomputable def transientExitRate {s : ℕ} (X : TransientStart s) : ℝ :=
  1 - X.Q X.i X.i

theorem transientExitRate_pos {s : ℕ} (X : TransientStart s) :
    0 < transientExitRate X := by
  unfold transientExitRate
  have hdiag_le_sum : X.Q X.i X.i ≤ ∑ j, X.Q X.i j :=
    Finset.single_le_sum (fun j _ => X.hQ X.i j) (Finset.mem_univ X.i)
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

noncomputable def transientHoldingMean {s : ℕ} (X : TransientStart s) : ℝ :=
  (transientExitRate X)⁻¹

theorem transientHoldingMean_pos {s : ℕ} (X : TransientStart s) :
    0 < transientHoldingMean X :=
  inv_pos.mpr (transientExitRate_pos X)

noncomputable def transientDepartureWeight {s : ℕ} (X : TransientStart s)
    (j : Fin s) : ℝ :=
  if j = X.i then 0 else X.Q X.i j / transientExitRate X

noncomputable def transientDirectExitWeight {s : ℕ} (X : TransientStart s) : ℝ :=
  (1 - ∑ j, X.Q X.i j) / transientExitRate X

theorem transientDepartureWeight_nonneg {s : ℕ} (X : TransientStart s) (j : Fin s) :
    0 ≤ transientDepartureWeight X j := by
  unfold transientDepartureWeight
  split_ifs
  · exact le_rfl
  · exact div_nonneg (X.hQ X.i j) (transientExitRate_pos X).le

@[simp] theorem transientDepartureWeight_self {s : ℕ} (X : TransientStart s) :
    transientDepartureWeight X X.i = 0 := by
  simp [transientDepartureWeight]

theorem transientDirectExitWeight_nonneg {s : ℕ} (X : TransientStart s) :
    0 ≤ transientDirectExitWeight X :=
  div_nonneg (sub_nonneg.mpr (X.hrow X.i)) (transientExitRate_pos X).le

theorem transientDepartureWeight_sum_add_direct {s : ℕ} (X : TransientStart s) :
    (∑ j, transientDepartureWeight X j) + transientDirectExitWeight X = 1 := by
  have hsplitQ := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
    (f := fun j => X.Q X.i j) (Finset.mem_univ X.i)
  have hsplitP := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
    (f := fun j => transientDepartureWeight X j) (Finset.mem_univ X.i)
  have herase : ∑ j ∈ (Finset.univ : Finset (Fin s)).erase X.i,
      transientDepartureWeight X j =
        (∑ j ∈ (Finset.univ : Finset (Fin s)).erase X.i, X.Q X.i j) /
          transientExitRate X := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ X.i := (Finset.mem_erase.mp hj).1
    simp [transientDepartureWeight, hji]
  rw [← hsplitP, transientDepartureWeight_self, add_zero, herase]
  unfold transientDirectExitWeight transientExitRate
  have hne : 1 - X.Q X.i X.i ≠ 0 := ne_of_gt (transientExitRate_pos X)
  field_simp [hne]
  linarith

noncomputable def transientReturnExitWeight {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) : ℝ :=
  X.Q (otherStateIndex X.i j) X.i

noncomputable def transientAbsorptionExitWeight {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) : ℝ :=
  1 - ∑ k, X.Q (otherStateIndex X.i j) k

theorem transientReturnExitWeight_nonneg {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) : 0 ≤ transientReturnExitWeight X j :=
  X.hQ _ _

theorem transientAbsorptionExitWeight_nonneg {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) : 0 ≤ transientAbsorptionExitWeight X j :=
  sub_nonneg.mpr (X.hrow _)

theorem transientDeletedQ_row_add_exits {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) :
    (∑ k, transientDeletedQ X j k) + transientReturnExitWeight X j +
      transientAbsorptionExitWeight X j = 1 := by
  let r := otherStateIndex X.i j
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
    (f := fun k => X.Q r k) (Finset.mem_univ X.i)
  have hdeleted : ∑ k, transientDeletedQ X j k =
      ∑ k ∈ (Finset.univ : Finset (Fin s)).erase X.i, X.Q r k := by
    unfold transientDeletedQ
    rw [← image_otherStateIndex X.i,
      Finset.sum_image (otherStateIndex_injective X.i).injOn]
    rfl
  rw [hdeleted]
  unfold transientReturnExitWeight transientAbsorptionExitWeight
  change (∑ k ∈ (Finset.univ : Finset (Fin s)).erase X.i, X.Q r k) +
    X.Q r X.i + (1 - ∑ k, X.Q r k) = 1
  linarith

/-- Probability of returning to the distinguished state when starting in the deleted block. -/
noncomputable def transientReturnPotential {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) : ℝ :=
  ((1 - transientDeletedQ X)⁻¹.mulVec (transientReturnExitWeight X)) j

/-- Probability of absorption before return when starting in the deleted block. -/
noncomputable def transientAbsorptionPotential {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) : ℝ :=
  ((1 - transientDeletedQ X)⁻¹.mulVec (transientAbsorptionExitWeight X)) j

noncomputable def transientReturnHittingVector {s : ℕ} (X : TransientStart s)
    (j : Fin s) : ℝ :=
  if hji : j = X.i then 1
  else transientReturnPotential X (otherStateEquiv X.i ⟨j, hji⟩)

@[simp] theorem transientReturnHittingVector_self {s : ℕ} (X : TransientStart s) :
    transientReturnHittingVector X X.i = 1 := by
  simp [transientReturnHittingVector]

@[simp] theorem transientReturnHittingVector_otherStateIndex {s : ℕ}
    (X : TransientStart s) (j : Fin (s - 1)) :
    transientReturnHittingVector X (otherStateIndex X.i j) =
      transientReturnPotential X j := by
  rw [transientReturnHittingVector]
  simp only [otherStateIndex_ne X.i j, ↓reduceDIte]
  congr 1
  exact (otherStateEquiv X.i).apply_symm_apply j

theorem transientReturnPotential_harmonic {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) :
    transientReturnPotential X j =
      (∑ k, transientDeletedQ X j k * transientReturnPotential X k) +
        transientReturnExitWeight X j := by
  let B := transientDeletedQ X
  let r := transientReturnExitWeight X
  have hdet : IsUnit (1 - B).det :=
    Matrix.isUnit_iff_isUnit_det (1 - B) |>.mp (transientDeletedStart X j).hu
  have hvec : (1 - B).mulVec ((1 - B)⁻¹.mulVec r) = r := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (1 - B) hdet, Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hvec
  have hj := congrFun hvec j
  change transientReturnPotential X j -
    (∑ k, transientDeletedQ X j k * transientReturnPotential X k) =
      transientReturnExitWeight X j at hj
  linarith

theorem transientAbsorptionPotential_harmonic {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) :
    transientAbsorptionPotential X j =
      (∑ k, transientDeletedQ X j k * transientAbsorptionPotential X k) +
        transientAbsorptionExitWeight X j := by
  let B := transientDeletedQ X
  let a := transientAbsorptionExitWeight X
  have hdet : IsUnit (1 - B).det :=
    Matrix.isUnit_iff_isUnit_det (1 - B) |>.mp (transientDeletedStart X j).hu
  have hvec : (1 - B).mulVec ((1 - B)⁻¹.mulVec a) = a := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (1 - B) hdet, Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hvec
  have hj := congrFun hvec j
  change transientAbsorptionPotential X j -
    (∑ k, transientDeletedQ X j k * transientAbsorptionPotential X k) =
      transientAbsorptionExitWeight X j at hj
  linarith

theorem transientReturnPotential_nonneg {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) : 0 ≤ transientReturnPotential X j := by
  unfold transientReturnPotential Matrix.mulVec dotProduct
  exact Finset.sum_nonneg fun k _ => mul_nonneg
    (inverse_one_sub_nonneg (transientDeletedQ X) (transientDeletedQ_nonneg X)
      (transientDeletedQ_row_le_one X) (transientDeletedQ_isUnit X) j k)
    (transientReturnExitWeight_nonneg X k)

theorem transientAbsorptionPotential_nonneg {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) : 0 ≤ transientAbsorptionPotential X j := by
  unfold transientAbsorptionPotential Matrix.mulVec dotProduct
  exact Finset.sum_nonneg fun k _ => mul_nonneg
    (inverse_one_sub_nonneg (transientDeletedQ X) (transientDeletedQ_nonneg X)
      (transientDeletedQ_row_le_one X) (transientDeletedQ_isUnit X) j k)
    (transientAbsorptionExitWeight_nonneg X k)

/-- The two deleted-block exit routes exhaust all possibilities. -/
theorem transientReturnPotential_add_absorptionPotential {s : ℕ}
    (X : TransientStart s) :
    ∀ j, transientReturnPotential X j + transientAbsorptionPotential X j = 1 := by
  intro j
  let B := transientDeletedQ X
  let r := transientReturnExitWeight X
  let a := transientAbsorptionExitWeight X
  have hexit : (fun k => r k + a k) = (1 - B).mulVec (fun _ => (1 : ℝ)) := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, mul_one]
    rw [Finset.sum_sub_distrib]
    have hone : ∑ x : Fin (s - 1),
        (1 : Matrix (Fin (s - 1)) (Fin (s - 1)) ℝ) k x = 1 := by
      simp [Matrix.one_apply]
    rw [hone]
    dsimp [B, r, a]
    linarith [transientDeletedQ_row_add_exits X k]
  have hunitDet : IsUnit (1 - B).det :=
    Matrix.isUnit_iff_isUnit_det (1 - B) |>.mp (transientDeletedQ_isUnit X)
  have hfund : (1 - B)⁻¹.mulVec (fun k => r k + a k) =
      (fun _ => (1 : ℝ)) := by
    rw [hexit, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul (1 - B) hunitDet,
      Matrix.one_mulVec]
  have hj := congrFun hfund j
  unfold transientReturnPotential transientAbsorptionPotential
  change (((1 - transientDeletedQ X)⁻¹.mulVec (transientReturnExitWeight X)) +
    ((1 - transientDeletedQ X)⁻¹.mulVec (transientAbsorptionExitWeight X))) j = 1
  rw [← Matrix.mulVec_add]
  exact hj

theorem transientReturnPotential_le_one {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) : transientReturnPotential X j ≤ 1 := by
  linarith [transientReturnPotential_add_absorptionPotential X j,
    transientAbsorptionPotential_nonneg X j]

theorem transientAbsorptionPotential_le_one {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) : transientAbsorptionPotential X j ≤ 1 := by
  linarith [transientReturnPotential_add_absorptionPotential X j,
    transientReturnPotential_nonneg X j]

/-- Forget the strict-contraction witness from an `AbsorptionStart`. -/
def AbsorptionStart.toTransient {s : ℕ} (X : AbsorptionStart s) : TransientStart s where
  Q := X.Q
  hQ := X.hQ
  hrow := X.hrow
  hu := X.hu
  i := X.i

noncomputable def transientMoment1 (s : ℕ) (X : TransientStart s) : ℝ :=
  ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i

noncomputable def transientMoment2 (s : ℕ) (X : TransientStart s) : ℝ :=
  2 * ((1 - X.Q)⁻¹.mulVec
    ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) X.i

noncomputable def transientMoment3 (s : ℕ) (X : TransientStart s) : ℝ :=
  6 * ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
    ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) X.i

@[simp] theorem toTransient_moment1 {s : ℕ} (X : AbsorptionStart s) :
    transientMoment1 s X.toTransient = moment1 s X := by
  rw [moment1_eq]
  rfl

@[simp] theorem toTransient_moment2 {s : ℕ} (X : AbsorptionStart s) :
    transientMoment2 s X.toTransient = moment2 s X := by
  rw [moment2_eq]
  rfl

@[simp] theorem toTransient_moment3 {s : ℕ} (X : AbsorptionStart s) :
    transientMoment3 s X.toTransient = moment3 s X := by
  rw [moment3_eq]
  rfl

theorem transientMoment1_pos {s : ℕ} (X : TransientStart s) :
    0 < transientMoment1 s X := by
  unfold transientMoment1 Matrix.mulVec dotProduct
  have hdiag : 1 ≤ (1 - X.Q)⁻¹ X.i X.i :=
    one_le_inverse_one_sub_diag X.Q X.hQ X.hrow X.hu X.i
  have hle : (1 - X.Q)⁻¹ X.i X.i ≤ ∑ j, (1 - X.Q)⁻¹ X.i j * 1 := by
    simpa using Finset.single_le_sum
      (fun j _ => mul_nonneg (inverse_one_sub_nonneg X.Q X.hQ X.hrow X.hu X.i j) zero_le_one)
      (Finset.mem_univ X.i)
  linarith

theorem transientMoment1_nonneg {s : ℕ} (X : TransientStart s) :
    0 ≤ transientMoment1 s X := (transientMoment1_pos X).le

theorem transientMoment2_nonneg {s : ℕ} (X : TransientStart s) :
    0 ≤ transientMoment2 s X := by
  unfold transientMoment2 Matrix.mulVec dotProduct
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (inverse_one_sub_nonneg X.Q X.hQ X.hrow X.hu X.i j)
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (inverse_one_sub_nonneg X.Q X.hQ X.hrow X.hu j k) zero_le_one

theorem transientMoment3_nonneg {s : ℕ} (X : TransientStart s) :
    0 ≤ transientMoment3 s X := by
  unfold transientMoment3 Matrix.mulVec dotProduct
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (inverse_one_sub_nonneg X.Q X.hQ X.hrow X.hu X.i j)
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (inverse_one_sub_nonneg X.Q X.hQ X.hrow X.hu j k)
  exact Finset.sum_nonneg fun l _ =>
    mul_nonneg (inverse_one_sub_nonneg X.Q X.hQ X.hrow X.hu k l) zero_le_one

/-- Aldous--Shepp for the general transient model.  The existing path proof already assumes only
nonnegativity, substochasticity, and invertibility, so no analytic strict-norm witness is needed. -/
theorem transientAldousSheppMoment {s : ℕ} (hs : 1 ≤ s) (X : TransientStart s) :
    ((s : ℝ) + 1) / s * (transientMoment1 s X) ^ 2 ≤ transientMoment2 s X := by
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
  unfold transientMoment1 transientMoment2
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
  rw [div_mul_eq_mul_div, le_div_iff₀ hs1] at hcb
  nlinarith

/-- The one-state base case for the general transient model. -/
theorem transientStageBound_one (X : TransientStart 1) :
    SSP.K2AllStages.StageBound 1
      (transientMoment1 1 X) (transientMoment2 1 X) (transientMoment3 1 X) := by
  unfold SSP.K2AllStages.StageBound transientMoment1 transientMoment2 transientMoment3
  have hi : X.i = (0 : Fin 1) := Subsingleton.elim _ _
  rw [hi]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, mul_one]
  ring_nf
  exact le_rfl

set_option maxHeartbeats 1000000 in
-- This reuses the expensive symbolic normalization of the general two-state inverse.
/-- The complete two-state base case requires only substochasticity and invertibility, and hence
applies unchanged to a conditioned transient model. -/
theorem transientStageBound_two (X : TransientStart 2) :
    SSP.K2AllStages.StageBound 2
      (transientMoment1 2 X) (transientMoment2 2 X) (transientMoment3 2 X) := by
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
  have hdelta : a * b * (1 - u * v) ≠ 0 := by
    intro hzero
    apply hdetunit.ne_zero
    rw [hA, Matrix.det_fin_two]
    norm_num
    calc a * b - a * u * (b * v) = a * b * (1 - u * v) := by ring
      _ = 0 := hzero
  have hmain := twoCycleMatrixStartZero a b u v ha hb hu0 hu1 hv0 hv1 hdelta
  have hmain' := twoCycleMatrixStartOne a b u v ha hb hu0 hu1 hv0 hv1 hdelta
  unfold SSP.K2AllStages.StageBound transientMoment1 transientMoment2 transientMoment3
  push_cast
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
  rw [hA]
  generalize hk : X.i = k
  fin_cases k
  · convert hmain using 1 <;> simp only [Fin.zero_eta] <;> ring
  · convert hmain' using 1 <;> simp only [Fin.mk_one] <;> ring

/-- A subprobability initial vector on a general transient model.  This is the class naturally
closed under exit conditioning; missing mass again denotes an atom at zero. -/
structure TransientInitial (s : ℕ) where
  model : TransientStart s
  weight : Fin s → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum_le_one : ∑ i, weight i ≤ 1

/-- Embed a deterministic transient start as a probability initial vector. -/
noncomputable def pureTransientInitial {s : ℕ} (X : TransientStart s) :
    TransientInitial s where
  model := X
  weight := fun j => if j = X.i then 1 else 0
  weight_nonneg := by intro j; split_ifs <;> positivity
  weight_sum_le_one := by simp

def TransientInitial.component {s : ℕ} (X : TransientInitial s)
    (i : Fin s) : TransientStart s :=
  { X.model with i := i }

noncomputable def transientInitialMoment1 (s : ℕ) (X : TransientInitial s) : ℝ :=
  ∑ i, X.weight i * transientMoment1 s (X.component i)

noncomputable def transientInitialMoment2 (s : ℕ) (X : TransientInitial s) : ℝ :=
  ∑ i, X.weight i * transientMoment2 s (X.component i)

noncomputable def transientInitialMoment3 (s : ℕ) (X : TransientInitial s) : ℝ :=
  ∑ i, X.weight i * transientMoment3 s (X.component i)

@[simp] theorem pureTransientInitial_moment1 {s : ℕ} (X : TransientStart s) :
    transientInitialMoment1 s (pureTransientInitial X) = transientMoment1 s X := by
  simp [transientInitialMoment1, pureTransientInitial, TransientInitial.component]

@[simp] theorem pureTransientInitial_moment2 {s : ℕ} (X : TransientStart s) :
    transientInitialMoment2 s (pureTransientInitial X) = transientMoment2 s X := by
  simp [transientInitialMoment2, pureTransientInitial, TransientInitial.component]

@[simp] theorem pureTransientInitial_moment3 {s : ℕ} (X : TransientStart s) :
    transientInitialMoment3 s (pureTransientInitial X) = transientMoment3 s X := by
  simp [transientInitialMoment3, pureTransientInitial, TransientInitial.component]

theorem transientInitialMoment1_nonneg {s : ℕ} (X : TransientInitial s) :
    0 ≤ transientInitialMoment1 s X := by
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (X.weight_nonneg i) (transientMoment1_nonneg (X.component i))

theorem transientInitialMoment2_nonneg {s : ℕ} (X : TransientInitial s) :
    0 ≤ transientInitialMoment2 s X := by
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (X.weight_nonneg i) (transientMoment2_nonneg (X.component i))

theorem transientInitialMoment3_nonneg {s : ℕ} (X : TransientInitial s) :
    0 ≤ transientInitialMoment3 s X := by
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (X.weight_nonneg i) (transientMoment3_nonneg (X.component i))

/-- The order-three canonical representation interface for a general transient model. -/
structure TransientOrderThreeCanonicalCertificate (X : TransientStart 3) where
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  x13 : ℝ
  pi : Fin 3 → ℝ
  x1_pos : 0 < x1
  x2_pos : 0 < x2
  x3_pos : 0 < x3
  x13_nonneg : 0 ≤ x13
  x13_lt : x13 < x1
  pi_nonneg : ∀ i, 0 ≤ pi i
  moment1_eq : transientMoment1 3 X =
    ∑ i, pi i * SSP.Canonical.canMoment x1 x2 x3 x13 0 i
  moment2_eq : transientMoment2 3 X =
    2 * ∑ i, pi i * SSP.Canonical.canMoment x1 x2 x3 x13 1 i
  moment3_eq : transientMoment3 3 X =
    6 * ∑ i, pi i * SSP.Canonical.canMoment x1 x2 x3 x13 2 i

/-- Similarity-form output of the He--Zhang order-three representation theorem.  Here
`1 - X.Q` is the negated original subgenerator, `SSP.Canonical.negA` is the negated canonical
subgenerator, and `S` preserves the all-ones column.  The transformed deterministic initial row
is the row `X.i` of `S`. -/
structure TransientOrderThreeSimilarityRepresentation (X : TransientStart 3) where
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  x13 : ℝ
  pi : Fin 3 → ℝ
  S : Matrix (Fin 3) (Fin 3) ℝ
  x1_pos : 0 < x1
  x2_pos : 0 < x2
  x3_pos : 0 < x3
  x13_nonneg : 0 ≤ x13
  x13_lt : x13 < x1
  pi_nonneg : ∀ j, 0 ≤ pi j
  S_unit : IsUnit S
  intertwine : (1 - X.Q) * S = S * SSP.Canonical.negA x1 x2 x3 x13
  preserve_one : S.mulVec (fun _ => (1 : ℝ)) = fun _ => 1
  initial_row : ∀ j, pi j = S X.i j

/-- The precise external representation result used by the proof: every transient
three-state model admits the He--Zhang canonical moment representation.  All subsequent
probabilistic and algebraic reasoning is proved in Lean. -/
def OrderThreeCanonicalRepresentationTheorem : Prop :=
  ∀ X : TransientStart 3, Nonempty (TransientOrderThreeCanonicalCertificate X)

/-- The cited theorem in its standard similarity-transform form. -/
def HeZhangOrderThreeRepresentationTheorem : Prop :=
  ∀ X : TransientStart 3, Nonempty (TransientOrderThreeSimilarityRepresentation X)

theorem transientStageBound_three_of_canonical (X : TransientStart 3)
    (c : TransientOrderThreeCanonicalCertificate X) :
    SSP.K2AllStages.StageBound 3
      (transientMoment1 3 X) (transientMoment2 3 X) (transientMoment3 3 X) := by
  have h := SSP.Canonical.canonical_hierarchy_s3_moments
    c.x1 c.x2 c.x3 c.x13 c.pi c.x1_pos c.x2_pos c.x3_pos
    c.x13_nonneg c.x13_lt c.pi_nonneg
  unfold SSP.K2AllStages.StageBound
  rw [c.moment1_eq, c.moment2_eq, c.moment3_eq]
  norm_num at h ⊢
  nlinarith

/-- A finite absorption model with a nonnegative subprobability initial vector.  The stored start
of `model` is immaterial; it lets us reuse all matrix and integrability facts for
`AbsorptionStart`, while `weight` is the actual initial distribution. -/
structure AbsorptionInitial (s : ℕ) where
  model : AbsorptionStart s
  weight : Fin s → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum_le_one : ∑ i, weight i ≤ 1

/-- The law in the deleted chain immediately after a genuine departure from the distinguished
state.  Its missing initial mass is exactly the probability of direct absorption at that
departure. -/
noncomputable def deletedDepartureInitial {s : ℕ} (X : AbsorptionStart s) (hs : 2 ≤ s) :
    AbsorptionInitial (s - 1) where
  model := deletedStart X ⟨0, by omega⟩
  weight := fun j => departureWeight X (otherStateIndex X.i j)
  weight_nonneg := fun j => departureWeight_nonneg X _
  weight_sum_le_one := by
    have hsum :
        ∑ j : Fin (s - 1), departureWeight X (otherStateIndex X.i j) =
          ∑ j : Fin s, departureWeight X j := by
      calc
        ∑ j : Fin (s - 1), departureWeight X (otherStateIndex X.i j) =
            ∑ j ∈ (Finset.univ : Finset (Fin s)).erase X.i,
              departureWeight X j := by
          rw [← image_otherStateIndex X.i,
            Finset.sum_image (otherStateIndex_injective X.i).injOn]
        _ = ∑ j : Fin s, departureWeight X j := by
          rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
            (f := fun j => departureWeight X j) (Finset.mem_univ X.i),
            departureWeight_self, add_zero]
    rw [hsum]
    linarith [departureWeight_sum_add_direct X, directExitWeight_nonneg X]

/-- Probability of eventually leaving the deleted block by returning to the distinguished
state, conditional on currently being at `j` in that block. -/
noncomputable def returnPotential {s : ℕ} (X : AbsorptionStart s)
    (j : Fin (s - 1)) : ℝ :=
  ((1 - deletedQ X)⁻¹.mulVec (returnExitWeight X)) j

/-- Probability of eventually leaving the deleted block by absorption, conditional on currently
being at `j` in that block. -/
noncomputable def absorptionPotential {s : ℕ} (X : AbsorptionStart s)
    (j : Fin (s - 1)) : ℝ :=
  ((1 - deletedQ X)⁻¹.mulVec (absorptionExitWeight X)) j

/-- Return-hitting probability on the full transient state space: it is one at the
distinguished state and is `returnPotential` on its complement. -/
noncomputable def returnHittingVector {s : ℕ} (X : AbsorptionStart s) (j : Fin s) : ℝ :=
  if hji : j = X.i then 1 else returnPotential X (otherStateEquiv X.i ⟨j, hji⟩)

@[simp] theorem returnHittingVector_self {s : ℕ} (X : AbsorptionStart s) :
    returnHittingVector X X.i = 1 := by
  simp [returnHittingVector]

@[simp] theorem returnHittingVector_otherStateIndex {s : ℕ} (X : AbsorptionStart s)
    (j : Fin (s - 1)) :
    returnHittingVector X (otherStateIndex X.i j) = returnPotential X j := by
  rw [returnHittingVector]
  simp only [otherStateIndex_ne X.i j, ↓reduceDIte]
  congr 1
  exact (otherStateEquiv X.i).apply_symm_apply j

/-- Doob transform associated with a nonnegative harmonic/excessive function.  Zero-potential
states are made inert; they will receive zero conditioned initial mass. -/
noncomputable def doobTransform {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (h : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun j k => if h j = 0 then 0 else B j k * h k / h j

theorem doobTransform_nonneg {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (h : Fin m → ℝ) (hB : ∀ j k, 0 ≤ B j k) (hh : ∀ j, 0 ≤ h j) :
    ∀ j k, 0 ≤ doobTransform B h j k := by
  intro j k
  unfold doobTransform
  split_ifs with hj
  · exact le_rfl
  · exact div_nonneg (mul_nonneg (hB j k) (hh k)) (hh j)

theorem doobTransform_row_le_one {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (h : Fin m → ℝ) (hh : ∀ j, 0 ≤ h j)
    (hsuper : ∀ j, ∑ k, B j k * h k ≤ h j) :
    ∀ j, ∑ k, doobTransform B h j k ≤ 1 := by
  intro j
  by_cases hj : h j = 0
  · simp [doobTransform, hj]
  · have hjpos : 0 < h j := lt_of_le_of_ne (hh j) (Ne.symm hj)
    simp only [doobTransform, hj, if_false, ← Finset.sum_div]
    exact (div_le_one hjpos).mpr (hsuper j)

/-- A Doob transform of a transient matrix is again transient.  Zero-potential states cause no
problem: their transformed rows are zero, while positive-potential states are diagonally similar
to the corresponding part of the original matrix. -/
theorem doobTransform_isUnit {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (h e : Fin m → ℝ) (hB : ∀ j k, 0 ≤ B j k) (hh : ∀ j, 0 ≤ h j)
    (he : ∀ j, 0 ≤ e j) (hharm : ∀ j, h j = (∑ k, B j k * h k) + e j)
    (hunit : IsUnit (1 - B)) : IsUnit (1 - doobTransform B h) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  let z := v - w
  have hzker : (1 - doobTransform B h).mulVec z = 0 := by
    rw [Matrix.mulVec_sub]
    exact sub_eq_zero.mpr hvw
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hzker
  have hDz : (doobTransform B h).mulVec z = z := by
    exact (sub_eq_zero.mp hzker).symm
  let y : Fin m → ℝ := fun j => h j * z j
  have hBy : B.mulVec y = y := by
    funext j
    by_cases hj : h j = 0
    · have hsum0 : ∑ k, B j k * h k = 0 := by
        have := hharm j
        rw [hj] at this
        have hsum_nonneg : 0 ≤ ∑ k, B j k * h k :=
          Finset.sum_nonneg fun k _ => mul_nonneg (hB j k) (hh k)
        linarith [he j]
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k (_ : k ∈ (Finset.univ : Finset (Fin m))) =>
          mul_nonneg (hB j k) (hh k))).mp hsum0
      change (∑ k, B j k * y k) = y j
      rw [show y j = 0 by simp [y, hj]]
      apply Finset.sum_eq_zero
      intro k hk
      dsimp [y]
      rw [← mul_assoc, hterm k hk, zero_mul]
    · have hzj := congrFun hDz j
      simp only [Matrix.mulVec, dotProduct, doobTransform, hj, if_false] at hzj
      unfold Matrix.mulVec dotProduct
      dsimp [y]
      have hscaled := congrArg (fun t : ℝ => t * h j) hzj
      rw [Finset.sum_mul] at hscaled
      calc
        ∑ k, B j k * (h k * z k) =
            ∑ k, (B j k * h k / h j * z k) * h j := by
          apply Finset.sum_congr rfl
          intro k _
          field_simp [hj]
        _ = z j * h j := hscaled
        _ = h j * z j := mul_comm _ _
  have hBker : (1 - B).mulVec y = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hBy, sub_self]
  have hBinj : Function.Injective (1 - B).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  have hy0 : y = 0 := hBinj (by simpa using hBker)
  have hz0 : z = 0 := by
    funext j
    by_cases hj : h j = 0
    · have hzj := congrFun hDz j
      simp [doobTransform, Matrix.mulVec, dotProduct, hj] at hzj
      exact hzj.symm
    · have hyj := congrFun hy0 j
      dsimp [y] at hyj
      exact (mul_eq_zero.mp hyj).resolve_left hj
  exact sub_eq_zero.mp hz0

/-- Diagonal intertwining identity for the Doob transform. -/
theorem diagonal_mul_doobTransform {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (h e : Fin m → ℝ) (hB : ∀ j k, 0 ≤ B j k) (hh : ∀ j, 0 ≤ h j)
    (he : ∀ j, 0 ≤ e j) (hharm : ∀ j, h j = (∑ k, B j k * h k) + e j) :
    Matrix.diagonal h * doobTransform B h = B * Matrix.diagonal h := by
  ext j k
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hj : h j = 0
  · have hsum0 : ∑ l, B j l * h l = 0 := by
      have := hharm j
      rw [hj] at this
      have hsum_nonneg : 0 ≤ ∑ l, B j l * h l :=
        Finset.sum_nonneg fun l _ => mul_nonneg (hB j l) (hh l)
      linarith [he j]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun l (_ : l ∈ (Finset.univ : Finset (Fin m))) =>
        mul_nonneg (hB j l) (hh l))).mp hsum0
    simp only [doobTransform, hj, if_pos, zero_mul]
    exact (hterm k (Finset.mem_univ k)).symm
  · simp only [doobTransform, hj, if_false]
    field_simp [hj]

/-- Resolvents inherit the diagonal intertwining identity. -/
theorem diagonal_mul_doobResolvent {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (h e : Fin m → ℝ) (hB : ∀ j k, 0 ≤ B j k) (hh : ∀ j, 0 ≤ h j)
    (he : ∀ j, 0 ≤ e j) (hharm : ∀ j, h j = (∑ k, B j k * h k) + e j)
    (hunit : IsUnit (1 - B)) :
    Matrix.diagonal h * (1 - doobTransform B h)⁻¹ =
      (1 - B)⁻¹ * Matrix.diagonal h := by
  let D := doobTransform B h
  let H := Matrix.diagonal h
  have hinter : H * D = B * H :=
    diagonal_mul_doobTransform B h e hB hh he hharm
  have hbridge : H * (1 - D) = (1 - B) * H := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hinter]
  have hDunit : IsUnit (1 - D) :=
    doobTransform_isUnit B h e hB hh he hharm hunit
  have hBdet : IsUnit (1 - B).det := Matrix.isUnit_iff_isUnit_det _ |>.mp hunit
  have hDdet : IsUnit (1 - D).det := Matrix.isUnit_iff_isUnit_det _ |>.mp hDunit
  calc
    H * (1 - D)⁻¹ = (1 * H) * (1 - D)⁻¹ := by rw [Matrix.one_mul]
    _ = (((1 - B)⁻¹ * (1 - B)) * H) * (1 - D)⁻¹ := by
      rw [Matrix.nonsing_inv_mul (1 - B) hBdet]
    _ = (1 - B)⁻¹ * ((1 - B) * H) * (1 - D)⁻¹ := by
      simp only [Matrix.mul_assoc]
    _ = (1 - B)⁻¹ * (H * (1 - D)) * (1 - D)⁻¹ := by rw [hbridge]
    _ = (1 - B)⁻¹ * H * ((1 - D) * (1 - D)⁻¹) := by
      simp only [Matrix.mul_assoc]
    _ = (1 - B)⁻¹ * H := by
      rw [Matrix.mul_nonsing_inv (1 - D) hDdet, Matrix.mul_one]

theorem diagonal_mul_doobResolvent_pow {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (h e : Fin m → ℝ) (hB : ∀ j k, 0 ≤ B j k) (hh : ∀ j, 0 ≤ h j)
    (he : ∀ j, 0 ≤ e j) (hharm : ∀ j, h j = (∑ k, B j k * h k) + e j)
    (hunit : IsUnit (1 - B)) (k : ℕ) :
    Matrix.diagonal h * (1 - doobTransform B h)⁻¹ ^ k =
      (1 - B)⁻¹ ^ k * Matrix.diagonal h := by
  let ND := (1 - doobTransform B h)⁻¹
  let NB := (1 - B)⁻¹
  have hbase : Matrix.diagonal h * ND = NB * Matrix.diagonal h :=
    diagonal_mul_doobResolvent B h e hB hh he hharm hunit
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hbase,
        ← Matrix.mul_assoc]

/-- Moment-vector form of the Doob resolvent identity, paired with an arbitrary initial row
weight. -/
theorem weighted_doobResolvent_pow {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (h e alpha : Fin m → ℝ) (hB : ∀ j k, 0 ≤ B j k) (hh : ∀ j, 0 ≤ h j)
    (he : ∀ j, 0 ≤ e j) (hharm : ∀ j, h j = (∑ k, B j k * h k) + e j)
    (hunit : IsUnit (1 - B)) (k : ℕ) :
    (∑ j, (alpha j * h j) *
      (((1 - doobTransform B h)⁻¹ ^ k).mulVec (fun _ => (1 : ℝ))) j) =
      ∑ j, alpha j * (((1 - B)⁻¹ ^ k).mulVec h) j := by
  have hmat := diagonal_mul_doobResolvent_pow B h e hB hh he hharm hunit k
  have hvec := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ =>
    M.mulVec (fun _ => (1 : ℝ))) hmat
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hvec
  have hdiag_one : (Matrix.diagonal h).mulVec (fun _ => (1 : ℝ)) = h := by
    funext j
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal]
  rw [hdiag_one] at hvec
  apply Finset.sum_congr rfl
  intro j _
  have hj := congrFun hvec j
  have hdiag_apply :
      ((Matrix.diagonal h).mulVec
        (((1 - doobTransform B h)⁻¹ ^ k).mulVec (fun _ => (1 : ℝ)))) j =
        h j * (((1 - doobTransform B h)⁻¹ ^ k).mulVec (fun _ => (1 : ℝ))) j := by
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal]
  rw [hdiag_apply] at hj
  rw [mul_assoc, hj]

theorem weighted_doobResolvent_pow_div {m : ℕ} (B : Matrix (Fin m) (Fin m) ℝ)
    (h e alpha : Fin m → ℝ) (c : ℝ) (hB : ∀ j k, 0 ≤ B j k)
    (hh : ∀ j, 0 ≤ h j) (he : ∀ j, 0 ≤ e j)
    (hharm : ∀ j, h j = (∑ k, B j k * h k) + e j)
    (hunit : IsUnit (1 - B)) (k : ℕ) :
    (∑ j, (alpha j * h j / c) *
      (((1 - doobTransform B h)⁻¹ ^ k).mulVec (fun _ => (1 : ℝ))) j) =
      (∑ j, alpha j * (((1 - B)⁻¹ ^ k).mulVec h) j) / c := by
  calc
    (∑ j, (alpha j * h j / c) *
      (((1 - doobTransform B h)⁻¹ ^ k).mulVec (fun _ => (1 : ℝ))) j) =
        (∑ j, (alpha j * h j) *
          (((1 - doobTransform B h)⁻¹ ^ k).mulVec (fun _ => (1 : ℝ))) j) / c := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ j, alpha j * (((1 - B)⁻¹ ^ k).mulVec h) j) / c := by
      rw [weighted_doobResolvent_pow B h e alpha hB hh he hharm hunit k]

theorem returnPotential_harmonic {s : ℕ} (X : AbsorptionStart s)
    (j : Fin (s - 1)) :
    returnPotential X j =
      (∑ k, deletedQ X j k * returnPotential X k) + returnExitWeight X j := by
  let B := deletedQ X
  let r := returnExitWeight X
  have hdet : IsUnit (1 - B).det :=
    Matrix.isUnit_iff_isUnit_det (1 - B) |>.mp (deletedStart X j).hu
  have hvec : (1 - B).mulVec ((1 - B)⁻¹.mulVec r) = r := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (1 - B) hdet, Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hvec
  have hj := congrFun hvec j
  change returnPotential X j -
    (∑ k, deletedQ X j k * returnPotential X k) = returnExitWeight X j at hj
  linarith

/-- Away from the distinguished state, the full return-hitting vector is `Q`-harmonic. -/
theorem returnHittingVector_harmonic_other {s : ℕ} (X : AbsorptionStart s)
    (j : Fin (s - 1)) :
    (X.Q.mulVec (returnHittingVector X)) (otherStateIndex X.i j) =
      returnHittingVector X (otherStateIndex X.i j) := by
  let r := otherStateIndex X.i j
  unfold Matrix.mulVec dotProduct
  calc
    ∑ k, X.Q r k * returnHittingVector X k =
        (∑ k ∈ (Finset.univ : Finset (Fin s)).erase X.i,
          X.Q r k * returnHittingVector X k) +
          X.Q r X.i * returnHittingVector X X.i := by
      exact (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
        (f := fun k => X.Q r k * returnHittingVector X k)
        (Finset.mem_univ X.i)).symm
    _ = (∑ k, deletedQ X j k * returnPotential X k) + returnExitWeight X j := by
      rw [returnHittingVector_self, mul_one]
      unfold deletedQ returnExitWeight
      rw [← image_otherStateIndex X.i,
        Finset.sum_image (otherStateIndex_injective X.i).injOn]
      simp only [returnHittingVector_otherStateIndex]
      rfl
    _ = returnPotential X j := (returnPotential_harmonic X j).symm
    _ = returnHittingVector X (otherStateIndex X.i j) :=
      (returnHittingVector_otherStateIndex X j).symm

theorem absorptionPotential_harmonic {s : ℕ} (X : AbsorptionStart s)
    (j : Fin (s - 1)) :
    absorptionPotential X j =
      (∑ k, deletedQ X j k * absorptionPotential X k) + absorptionExitWeight X j := by
  let B := deletedQ X
  let a := absorptionExitWeight X
  have hdet : IsUnit (1 - B).det :=
    Matrix.isUnit_iff_isUnit_det (1 - B) |>.mp (deletedStart X j).hu
  have hvec : (1 - B).mulVec ((1 - B)⁻¹.mulVec a) = a := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (1 - B) hdet, Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hvec
  have hj := congrFun hvec j
  change absorptionPotential X j -
    (∑ k, deletedQ X j k * absorptionPotential X k) = absorptionExitWeight X j at hj
  linarith

theorem returnPotential_nonneg {s : ℕ} (X : AbsorptionStart s) (j : Fin (s - 1)) :
    0 ≤ returnPotential X j := by
  unfold returnPotential Matrix.mulVec dotProduct
  exact Finset.sum_nonneg fun k _ => mul_nonneg
    (inverse_one_sub_nonneg (deletedQ X) (deletedQ_nonneg X) (deletedQ_row_le_one X)
      (deletedStart X j).hu j k)
    (returnExitWeight_nonneg X k)

theorem absorptionPotential_nonneg {s : ℕ} (X : AbsorptionStart s)
    (j : Fin (s - 1)) : 0 ≤ absorptionPotential X j := by
  unfold absorptionPotential Matrix.mulVec dotProduct
  exact Finset.sum_nonneg fun k _ => mul_nonneg
    (inverse_one_sub_nonneg (deletedQ X) (deletedQ_nonneg X) (deletedQ_row_le_one X)
      (deletedStart X j).hu j k)
    (absorptionExitWeight_nonneg X k)

/-- Since the deleted block is transient, it eventually exits by exactly one of the two routes. -/
theorem returnPotential_add_absorptionPotential {s : ℕ} (X : AbsorptionStart s) :
    ∀ j, returnPotential X j + absorptionPotential X j = 1 := by
  intro j
  let B := deletedQ X
  let r := returnExitWeight X
  let a := absorptionExitWeight X
  have hexit : (fun k => r k + a k) = (1 - B).mulVec (fun _ => (1 : ℝ)) := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, mul_one]
    rw [Finset.sum_sub_distrib]
    have hone : ∑ x : Fin (s - 1), (1 : Matrix (Fin (s - 1)) (Fin (s - 1)) ℝ) k x = 1 := by
      simp [Matrix.one_apply]
    rw [hone]
    dsimp [B, r, a]
    linarith [deletedQ_row_add_exits X k]
  have hunitDet : IsUnit (1 - B).det :=
    Matrix.isUnit_iff_isUnit_det (1 - B) |>.mp (deletedStart X j).hu
  have hfund : (1 - B)⁻¹.mulVec (fun k => r k + a k) = (fun _ => (1 : ℝ)) := by
    rw [hexit, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul (1 - B) hunitDet,
      Matrix.one_mulVec]
  have hj := congrFun hfund j
  unfold returnPotential absorptionPotential
  change (((1 - deletedQ X)⁻¹.mulVec (returnExitWeight X)) +
    ((1 - deletedQ X)⁻¹.mulVec (absorptionExitWeight X))) j = 1
  rw [← Matrix.mulVec_add]
  exact hj

theorem returnPotential_le_one {s : ℕ} (X : AbsorptionStart s) (j : Fin (s - 1)) :
    returnPotential X j ≤ 1 := by
  linarith [returnPotential_add_absorptionPotential X j, absorptionPotential_nonneg X j]

theorem absorptionPotential_le_one {s : ℕ} (X : AbsorptionStart s)
    (j : Fin (s - 1)) : absorptionPotential X j ≤ 1 := by
  linarith [returnPotential_add_absorptionPotential X j, returnPotential_nonneg X j]

/-! ## State-return conditioning for arbitrary transient starts -/

noncomputable def transientReturnConditionedQ {s : ℕ} (X : TransientStart s) :
    Matrix (Fin (s - 1)) (Fin (s - 1)) ℝ :=
  doobTransform (transientDeletedQ X) (transientReturnPotential X)

noncomputable def transientTerminalConditionedQ {s : ℕ} (X : TransientStart s) :
    Matrix (Fin (s - 1)) (Fin (s - 1)) ℝ :=
  doobTransform (transientDeletedQ X) (transientAbsorptionPotential X)

theorem transientReturnConditionedQ_nonneg {s : ℕ} (X : TransientStart s) :
    ∀ j k, 0 ≤ transientReturnConditionedQ X j k :=
  doobTransform_nonneg (transientDeletedQ X) (transientReturnPotential X)
    (transientDeletedQ_nonneg X) (transientReturnPotential_nonneg X)

theorem transientTerminalConditionedQ_nonneg {s : ℕ} (X : TransientStart s) :
    ∀ j k, 0 ≤ transientTerminalConditionedQ X j k :=
  doobTransform_nonneg (transientDeletedQ X) (transientAbsorptionPotential X)
    (transientDeletedQ_nonneg X) (transientAbsorptionPotential_nonneg X)

theorem transientReturnConditionedQ_row_le_one {s : ℕ} (X : TransientStart s) :
    ∀ j, ∑ k, transientReturnConditionedQ X j k ≤ 1 := by
  apply doobTransform_row_le_one (transientDeletedQ X) (transientReturnPotential X)
    (transientReturnPotential_nonneg X)
  intro j
  linarith [transientReturnPotential_harmonic X j,
    transientReturnExitWeight_nonneg X j]

theorem transientTerminalConditionedQ_row_le_one {s : ℕ} (X : TransientStart s) :
    ∀ j, ∑ k, transientTerminalConditionedQ X j k ≤ 1 := by
  apply doobTransform_row_le_one (transientDeletedQ X) (transientAbsorptionPotential X)
    (transientAbsorptionPotential_nonneg X)
  intro j
  linarith [transientAbsorptionPotential_harmonic X j,
    transientAbsorptionExitWeight_nonneg X j]

theorem transientReturnConditionedQ_isUnit {s : ℕ} (X : TransientStart s) :
    IsUnit (1 - transientReturnConditionedQ X) := by
  exact doobTransform_isUnit (transientDeletedQ X) (transientReturnPotential X)
    (transientReturnExitWeight X) (transientDeletedQ_nonneg X)
    (transientReturnPotential_nonneg X) (transientReturnExitWeight_nonneg X)
    (transientReturnPotential_harmonic X) (transientDeletedQ_isUnit X)

theorem transientTerminalConditionedQ_isUnit {s : ℕ} (X : TransientStart s) :
    IsUnit (1 - transientTerminalConditionedQ X) := by
  exact doobTransform_isUnit (transientDeletedQ X) (transientAbsorptionPotential X)
    (transientAbsorptionExitWeight X) (transientDeletedQ_nonneg X)
    (transientAbsorptionPotential_nonneg X) (transientAbsorptionExitWeight_nonneg X)
    (transientAbsorptionPotential_harmonic X) (transientDeletedQ_isUnit X)

noncomputable def transientReturnConditionedStart {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) : TransientStart (s - 1) where
  Q := transientReturnConditionedQ X
  hQ := transientReturnConditionedQ_nonneg X
  hrow := transientReturnConditionedQ_row_le_one X
  hu := transientReturnConditionedQ_isUnit X
  i := j

noncomputable def transientTerminalConditionedStart {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) : TransientStart (s - 1) where
  Q := transientTerminalConditionedQ X
  hQ := transientTerminalConditionedQ_nonneg X
  hrow := transientTerminalConditionedQ_row_le_one X
  hu := transientTerminalConditionedQ_isUnit X
  i := j

noncomputable def transientReturnProbability {s : ℕ} (X : TransientStart s) : ℝ :=
  ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
    transientReturnPotential X j

noncomputable def transientTerminalProbability {s : ℕ} (X : TransientStart s) : ℝ :=
  transientDirectExitWeight X +
    ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
      transientAbsorptionPotential X j

theorem transientReturnHittingVector_harmonic_other {s : ℕ} (X : TransientStart s)
    (j : Fin (s - 1)) :
    (X.Q.mulVec (transientReturnHittingVector X)) (otherStateIndex X.i j) =
      transientReturnHittingVector X (otherStateIndex X.i j) := by
  let r := otherStateIndex X.i j
  unfold Matrix.mulVec dotProduct
  calc
    ∑ k, X.Q r k * transientReturnHittingVector X k =
        (∑ k ∈ (Finset.univ : Finset (Fin s)).erase X.i,
          X.Q r k * transientReturnHittingVector X k) +
          X.Q r X.i * transientReturnHittingVector X X.i := by
      exact (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
        (f := fun k => X.Q r k * transientReturnHittingVector X k)
        (Finset.mem_univ X.i)).symm
    _ = (∑ k, transientDeletedQ X j k * transientReturnPotential X k) +
        transientReturnExitWeight X j := by
      rw [transientReturnHittingVector_self, mul_one]
      unfold transientDeletedQ transientReturnExitWeight
      rw [← image_otherStateIndex X.i,
        Finset.sum_image (otherStateIndex_injective X.i).injOn]
      simp only [transientReturnHittingVector_otherStateIndex]
      rfl
    _ = transientReturnPotential X j :=
      (transientReturnPotential_harmonic X j).symm
    _ = transientReturnHittingVector X (otherStateIndex X.i j) :=
      (transientReturnHittingVector_otherStateIndex X j).symm

theorem transientReturnHittingVector_at_start {s : ℕ} (X : TransientStart s) :
    (X.Q.mulVec (transientReturnHittingVector X)) X.i =
      X.Q X.i X.i + transientExitRate X * transientReturnProbability X := by
  have herase :
      ∑ j ∈ (Finset.univ : Finset (Fin s)).erase X.i,
          X.Q X.i j * transientReturnHittingVector X j =
        transientExitRate X * transientReturnProbability X := by
    unfold transientReturnProbability
    rw [Finset.mul_sum, ← image_otherStateIndex X.i,
      Finset.sum_image (otherStateIndex_injective X.i).injOn]
    apply Finset.sum_congr rfl
    intro j _
    rw [transientReturnHittingVector_otherStateIndex]
    simp only [transientDepartureWeight, otherStateIndex_ne X.i j, if_false]
    field_simp [(transientExitRate_pos X).ne']
  unfold Matrix.mulVec dotProduct
  rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
    (f := fun j => X.Q X.i j * transientReturnHittingVector X j)
    (Finset.mem_univ X.i), transientReturnHittingVector_self, mul_one, herase]
  ring

theorem transientReturnProbability_nonneg {s : ℕ} (X : TransientStart s) :
    0 ≤ transientReturnProbability X := by
  unfold transientReturnProbability
  exact Finset.sum_nonneg fun j _ => mul_nonneg
    (transientDepartureWeight_nonneg X _) (transientReturnPotential_nonneg X j)

theorem transientTerminalProbability_nonneg {s : ℕ} (X : TransientStart s) :
    0 ≤ transientTerminalProbability X := by
  unfold transientTerminalProbability
  exact add_nonneg (transientDirectExitWeight_nonneg X) <|
    Finset.sum_nonneg fun j _ => mul_nonneg
      (transientDepartureWeight_nonneg X _) (transientAbsorptionPotential_nonneg X j)

theorem transientReturnProbability_add_terminalProbability {s : ℕ}
    (X : TransientStart s) :
    transientReturnProbability X + transientTerminalProbability X = 1 := by
  have hsum :
      ∑ j, transientDepartureWeight X (otherStateIndex X.i j) =
        ∑ j : Fin s, transientDepartureWeight X j := by
    calc
      ∑ j, transientDepartureWeight X (otherStateIndex X.i j) =
          ∑ j ∈ (Finset.univ : Finset (Fin s)).erase X.i,
            transientDepartureWeight X j := by
        rw [← image_otherStateIndex X.i,
          Finset.sum_image (otherStateIndex_injective X.i).injOn]
      _ = ∑ j : Fin s, transientDepartureWeight X j := by
        rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
          (f := fun j => transientDepartureWeight X j) (Finset.mem_univ X.i),
          transientDepartureWeight_self, add_zero]
  unfold transientReturnProbability transientTerminalProbability
  rw [show
    (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        transientReturnPotential X j) +
      (transientDirectExitWeight X +
        ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
          transientAbsorptionPotential X j) =
      transientDirectExitWeight X +
        ((∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
          transientReturnPotential X j) +
        ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
          transientAbsorptionPotential X j) by ring]
  rw [← Finset.sum_add_distrib]
  have hcollapse :
      ∑ j, (transientDepartureWeight X (otherStateIndex X.i j) *
          transientReturnPotential X j +
        transientDepartureWeight X (otherStateIndex X.i j) *
          transientAbsorptionPotential X j) =
        ∑ j, transientDepartureWeight X (otherStateIndex X.i j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_add, transientReturnPotential_add_absorptionPotential X j, mul_one]
  rw [hcollapse, hsum]
  linarith [transientDepartureWeight_sum_add_direct X]

theorem transientTerminalProbability_pos {s : ℕ} (X : TransientStart s) :
    0 < transientTerminalProbability X := by
  rcases eq_or_lt_of_le (transientTerminalProbability_nonneg X) with hq0 | hqpos
  · exfalso
    have hp1 : transientReturnProbability X = 1 := by
      linarith [transientReturnProbability_add_terminalProbability X]
    have hstart : (X.Q.mulVec (transientReturnHittingVector X)) X.i =
        transientReturnHittingVector X X.i := by
      rw [transientReturnHittingVector_at_start, hp1,
        transientReturnHittingVector_self]
      unfold transientExitRate
      ring
    have hfixed : X.Q.mulVec (transientReturnHittingVector X) =
        transientReturnHittingVector X := by
      funext j
      by_cases hji : j = X.i
      · subst j
        exact hstart
      · let k : Fin (s - 1) := otherStateEquiv X.i ⟨j, hji⟩
        have hk : otherStateIndex X.i k = j := by
          change ((otherStateEquiv X.i).symm k).1 = j
          rw [show (otherStateEquiv X.i).symm k =
            (⟨j, hji⟩ : OtherState X.i) by simp [k]]
        simpa [hk] using transientReturnHittingVector_harmonic_other X k
    have hker : (1 - X.Q).mulVec (transientReturnHittingVector X) = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfixed, sub_self]
    have hinj : Function.Injective (1 - X.Q).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr X.hu
    have hzero : transientReturnHittingVector X = 0 := hinj (by simpa using hker)
    have hi := congrFun hzero X.i
    simp at hi
  · exact hqpos

theorem transientReturnProbability_lt_one {s : ℕ} (X : TransientStart s) :
    transientReturnProbability X < 1 := by
  linarith [transientReturnProbability_add_terminalProbability X,
    transientTerminalProbability_pos X]

theorem transientTerminalProbability_le_one {s : ℕ} (X : TransientStart s) :
    transientTerminalProbability X ≤ 1 := by
  linarith [transientReturnProbability_add_terminalProbability X,
    transientReturnProbability_nonneg X]

/-- Deleted-chain transition matrix conditioned on eventual return to the distinguished state. -/
noncomputable def returnConditionedQ {s : ℕ} (X : AbsorptionStart s) :
    Matrix (Fin (s - 1)) (Fin (s - 1)) ℝ :=
  doobTransform (deletedQ X) (returnPotential X)

/-- Deleted-chain transition matrix conditioned on eventual absorption before returning. -/
noncomputable def terminalConditionedQ {s : ℕ} (X : AbsorptionStart s) :
    Matrix (Fin (s - 1)) (Fin (s - 1)) ℝ :=
  doobTransform (deletedQ X) (absorptionPotential X)

theorem returnConditionedQ_nonneg {s : ℕ} (X : AbsorptionStart s) :
    ∀ j k, 0 ≤ returnConditionedQ X j k := by
  exact doobTransform_nonneg (deletedQ X) (returnPotential X)
    (deletedQ_nonneg X) (returnPotential_nonneg X)

theorem terminalConditionedQ_nonneg {s : ℕ} (X : AbsorptionStart s) :
    ∀ j k, 0 ≤ terminalConditionedQ X j k := by
  exact doobTransform_nonneg (deletedQ X) (absorptionPotential X)
    (deletedQ_nonneg X) (absorptionPotential_nonneg X)

theorem returnConditionedQ_row_le_one {s : ℕ} (X : AbsorptionStart s) :
    ∀ j, ∑ k, returnConditionedQ X j k ≤ 1 := by
  apply doobTransform_row_le_one (deletedQ X) (returnPotential X)
    (returnPotential_nonneg X)
  intro j
  linarith [returnPotential_harmonic X j, returnExitWeight_nonneg X j]

theorem terminalConditionedQ_row_le_one {s : ℕ} (X : AbsorptionStart s) :
    ∀ j, ∑ k, terminalConditionedQ X j k ≤ 1 := by
  apply doobTransform_row_le_one (deletedQ X) (absorptionPotential X)
    (absorptionPotential_nonneg X)
  intro j
  linarith [absorptionPotential_harmonic X j, absorptionExitWeight_nonneg X j]

theorem returnConditionedQ_isUnit {s : ℕ} (X : AbsorptionStart s) :
    IsUnit (1 - returnConditionedQ X) := by
  apply doobTransform_isUnit (deletedQ X) (returnPotential X) (returnExitWeight X)
    (deletedQ_nonneg X) (returnPotential_nonneg X) (returnExitWeight_nonneg X)
    (returnPotential_harmonic X)
  exact isUnit_one_sub_of_norm_lt_one
    (lt_of_le_of_lt ((deletedQ_norm_le X).trans X.hnorm) X.hθ)

theorem terminalConditionedQ_isUnit {s : ℕ} (X : AbsorptionStart s) :
    IsUnit (1 - terminalConditionedQ X) := by
  apply doobTransform_isUnit (deletedQ X) (absorptionPotential X) (absorptionExitWeight X)
    (deletedQ_nonneg X) (absorptionPotential_nonneg X) (absorptionExitWeight_nonneg X)
    (absorptionPotential_harmonic X)
  exact isUnit_one_sub_of_norm_lt_one
    (lt_of_le_of_lt ((deletedQ_norm_le X).trans X.hnorm) X.hθ)

/-- The return-conditioned deleted chain as a general transient deterministic-start model. -/
noncomputable def returnConditionedStart {s : ℕ} (X : AbsorptionStart s)
    (j : Fin (s - 1)) : TransientStart (s - 1) where
  Q := returnConditionedQ X
  hQ := returnConditionedQ_nonneg X
  hrow := returnConditionedQ_row_le_one X
  hu := returnConditionedQ_isUnit X
  i := j

/-- The terminal-conditioned deleted chain as a general transient deterministic-start model. -/
noncomputable def terminalConditionedStart {s : ℕ} (X : AbsorptionStart s)
    (j : Fin (s - 1)) : TransientStart (s - 1) where
  Q := terminalConditionedQ X
  hQ := terminalConditionedQ_nonneg X
  hrow := terminalConditionedQ_row_le_one X
  hu := terminalConditionedQ_isUnit X
  i := j

/-- Probability that a genuine departure from the distinguished state eventually returns to it. -/
noncomputable def returnProbability {s : ℕ} (X : AbsorptionStart s) : ℝ :=
  ∑ j, departureWeight X (otherStateIndex X.i j) * returnPotential X j

/-- Probability that a genuine departure is terminal, including immediate absorption. -/
noncomputable def terminalProbability {s : ℕ} (X : AbsorptionStart s) : ℝ :=
  directExitWeight X +
    ∑ j, departureWeight X (otherStateIndex X.i j) * absorptionPotential X j

/-- At the distinguished state, applying `Q` to the return-hitting vector gives the diagonal
self-loop contribution plus the genuine departure rate times the return probability. -/
theorem returnHittingVector_at_start {s : ℕ} (X : AbsorptionStart s) :
    (X.Q.mulVec (returnHittingVector X)) X.i =
      X.Q X.i X.i + exitRate X * returnProbability X := by
  have herase :
      ∑ j ∈ (Finset.univ : Finset (Fin s)).erase X.i,
          X.Q X.i j * returnHittingVector X j =
        exitRate X * returnProbability X := by
    unfold returnProbability
    rw [Finset.mul_sum, ← image_otherStateIndex X.i,
      Finset.sum_image (otherStateIndex_injective X.i).injOn]
    apply Finset.sum_congr rfl
    intro j _
    rw [returnHittingVector_otherStateIndex]
    simp only [departureWeight, otherStateIndex_ne X.i j, if_false]
    field_simp [(exitRate_pos X).ne']
  unfold Matrix.mulVec dotProduct
  rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
    (f := fun j => X.Q X.i j * returnHittingVector X j) (Finset.mem_univ X.i),
    returnHittingVector_self, mul_one, herase]
  ring

theorem returnProbability_nonneg {s : ℕ} (X : AbsorptionStart s) :
    0 ≤ returnProbability X := by
  unfold returnProbability
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (departureWeight_nonneg X _) (returnPotential_nonneg X j)

theorem terminalProbability_nonneg {s : ℕ} (X : AbsorptionStart s) :
    0 ≤ terminalProbability X := by
  unfold terminalProbability
  exact add_nonneg (directExitWeight_nonneg X) <|
    Finset.sum_nonneg fun j _ =>
      mul_nonneg (departureWeight_nonneg X _) (absorptionPotential_nonneg X j)

/-- Return and terminal absorption exhaust the possibilities after a genuine departure. -/
theorem returnProbability_add_terminalProbability {s : ℕ} (X : AbsorptionStart s) :
    returnProbability X + terminalProbability X = 1 := by
  have hsum :
      ∑ j, departureWeight X (otherStateIndex X.i j) =
        ∑ j : Fin s, departureWeight X j := by
    calc
      ∑ j, departureWeight X (otherStateIndex X.i j) =
          ∑ j ∈ (Finset.univ : Finset (Fin s)).erase X.i, departureWeight X j := by
        rw [← image_otherStateIndex X.i,
          Finset.sum_image (otherStateIndex_injective X.i).injOn]
      _ = ∑ j : Fin s, departureWeight X j := by
        rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
          (f := fun j => departureWeight X j) (Finset.mem_univ X.i),
          departureWeight_self, add_zero]
  unfold returnProbability terminalProbability
  rw [show
    (∑ j, departureWeight X (otherStateIndex X.i j) * returnPotential X j) +
        (directExitWeight X +
          ∑ j, departureWeight X (otherStateIndex X.i j) * absorptionPotential X j) =
      directExitWeight X +
        ((∑ j, departureWeight X (otherStateIndex X.i j) * returnPotential X j) +
          ∑ j, departureWeight X (otherStateIndex X.i j) * absorptionPotential X j) by ring]
  rw [← Finset.sum_add_distrib]
  have hcollapse :
      ∑ j, (departureWeight X (otherStateIndex X.i j) * returnPotential X j +
        departureWeight X (otherStateIndex X.i j) * absorptionPotential X j) =
        ∑ j, departureWeight X (otherStateIndex X.i j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_add, returnPotential_add_absorptionPotential X j, mul_one]
  rw [hcollapse, hsum]
  linarith [departureWeight_sum_add_direct X]

/-- A transient chain has a strictly positive chance of absorption before returning to the
distinguished state.  Otherwise its return-hitting vector would be a nonzero fixed vector of
`Q`, contradicting invertibility of `I - Q`. -/
theorem terminalProbability_pos {s : ℕ} (X : AbsorptionStart s) :
    0 < terminalProbability X := by
  rcases eq_or_lt_of_le (terminalProbability_nonneg X) with hq0 | hqpos
  · exfalso
    have hp1 : returnProbability X = 1 := by
      linarith [returnProbability_add_terminalProbability X]
    have hstart : (X.Q.mulVec (returnHittingVector X)) X.i =
        returnHittingVector X X.i := by
      rw [returnHittingVector_at_start, hp1, returnHittingVector_self]
      unfold exitRate
      ring
    have hfixed : X.Q.mulVec (returnHittingVector X) = returnHittingVector X := by
      funext j
      by_cases hji : j = X.i
      · subst j
        exact hstart
      · let k : Fin (s - 1) := otherStateEquiv X.i ⟨j, hji⟩
        have hk : otherStateIndex X.i k = j := by
          change ((otherStateEquiv X.i).symm k).1 = j
          rw [show (otherStateEquiv X.i).symm k = (⟨j, hji⟩ : OtherState X.i) by simp [k]]
        simpa [hk] using returnHittingVector_harmonic_other X k
    have hker : (1 - X.Q).mulVec (returnHittingVector X) = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfixed, sub_self]
    have hinj : Function.Injective (1 - X.Q).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr X.hu
    have hzero : returnHittingVector X = 0 := hinj (by simpa using hker)
    have hi := congrFun hzero X.i
    simp at hi
  · exact hqpos

theorem returnProbability_lt_one {s : ℕ} (X : AbsorptionStart s) :
    returnProbability X < 1 := by
  linarith [returnProbability_add_terminalProbability X, terminalProbability_pos X]

theorem terminalProbability_le_one {s : ℕ} (X : AbsorptionStart s) :
    terminalProbability X ≤ 1 := by
  linarith [returnProbability_add_terminalProbability X, returnProbability_nonneg X]

/-- The normalized return-conditioned initial law for an arbitrary transient start. -/
noncomputable def transientReturnConditionedInitial {s : ℕ} (X : TransientStart s)
    (hs : 2 ≤ s) (hp : 0 < transientReturnProbability X) : TransientInitial (s - 1) where
  model := transientReturnConditionedStart X ⟨0, by omega⟩
  weight := fun j =>
    transientDepartureWeight X (otherStateIndex X.i j) * transientReturnPotential X j /
      transientReturnProbability X
  weight_nonneg := fun j => div_nonneg
    (mul_nonneg (transientDepartureWeight_nonneg X _)
      (transientReturnPotential_nonneg X j)) hp.le
  weight_sum_le_one := by
    rw [← Finset.sum_div]
    change transientReturnProbability X / transientReturnProbability X ≤ 1
    rw [div_self hp.ne']

theorem transientReturnConditionedInitial_weight_sum {s : ℕ} (X : TransientStart s)
    (hs : 2 ≤ s) (hp : 0 < transientReturnProbability X) :
    ∑ j, (transientReturnConditionedInitial X hs hp).weight j = 1 := by
  unfold transientReturnConditionedInitial
  rw [← Finset.sum_div]
  change transientReturnProbability X / transientReturnProbability X = 1
  exact div_self hp.ne'

noncomputable def transientReturnExcursionInitial {s : ℕ} (X : TransientStart s)
    (hs : 2 ≤ s) : TransientInitial (s - 1) :=
  if hp : 0 < transientReturnProbability X then
    transientReturnConditionedInitial X hs hp
  else pureTransientInitial (transientReturnConditionedStart X ⟨0, by omega⟩)

theorem transientReturnExcursionInitial_weight_sum {s : ℕ} (X : TransientStart s)
    (hs : 2 ≤ s) :
    ∑ j, (transientReturnExcursionInitial X hs).weight j = 1 := by
  unfold transientReturnExcursionInitial
  split_ifs with hp
  · exact transientReturnConditionedInitial_weight_sum X hs hp
  · simp [pureTransientInitial]

/-- The normalized terminal-conditioned initial law.  Its missing mass is immediate
absorption at departure from the distinguished state. -/
noncomputable def transientTerminalConditionedInitial {s : ℕ} (X : TransientStart s)
    (hs : 2 ≤ s) (hq : 0 < transientTerminalProbability X) : TransientInitial (s - 1) where
  model := transientTerminalConditionedStart X ⟨0, by omega⟩
  weight := fun j =>
    transientDepartureWeight X (otherStateIndex X.i j) *
      transientAbsorptionPotential X j / transientTerminalProbability X
  weight_nonneg := fun j => div_nonneg
    (mul_nonneg (transientDepartureWeight_nonneg X _)
      (transientAbsorptionPotential_nonneg X j)) hq.le
  weight_sum_le_one := by
    rw [← Finset.sum_div]
    apply (div_le_one hq).mpr
    unfold transientTerminalProbability
    linarith [transientDirectExitWeight_nonneg X]

theorem transientReturnConditionedInitial_resolvent_pow {s : ℕ}
    (X : TransientStart s) (hs : 2 ≤ s) (hp : 0 < transientReturnProbability X)
    (k : ℕ) :
    (∑ j, (transientReturnConditionedInitial X hs hp).weight j *
      (((1 - (transientReturnConditionedInitial X hs hp).model.Q)⁻¹ ^ k).mulVec
        (fun _ => (1 : ℝ))) j) =
      (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        (((1 - transientDeletedQ X)⁻¹ ^ k).mulVec (transientReturnPotential X)) j) /
          transientReturnProbability X := by
  simpa [transientReturnConditionedInitial, transientReturnConditionedStart,
    transientReturnConditionedQ] using
    weighted_doobResolvent_pow_div (transientDeletedQ X) (transientReturnPotential X)
      (transientReturnExitWeight X)
      (fun j => transientDepartureWeight X (otherStateIndex X.i j))
      (transientReturnProbability X) (transientDeletedQ_nonneg X)
      (transientReturnPotential_nonneg X) (transientReturnExitWeight_nonneg X)
      (transientReturnPotential_harmonic X) (transientDeletedQ_isUnit X) k

theorem transientTerminalConditionedInitial_resolvent_pow {s : ℕ}
    (X : TransientStart s) (hs : 2 ≤ s) (hq : 0 < transientTerminalProbability X)
    (k : ℕ) :
    (∑ j, (transientTerminalConditionedInitial X hs hq).weight j *
      (((1 - (transientTerminalConditionedInitial X hs hq).model.Q)⁻¹ ^ k).mulVec
        (fun _ => (1 : ℝ))) j) =
      (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        (((1 - transientDeletedQ X)⁻¹ ^ k).mulVec
          (transientAbsorptionPotential X)) j) / transientTerminalProbability X := by
  simpa [transientTerminalConditionedInitial, transientTerminalConditionedStart,
    transientTerminalConditionedQ] using
    weighted_doobResolvent_pow_div (transientDeletedQ X) (transientAbsorptionPotential X)
      (transientAbsorptionExitWeight X)
      (fun j => transientDepartureWeight X (otherStateIndex X.i j))
      (transientTerminalProbability X) (transientDeletedQ_nonneg X)
      (transientAbsorptionPotential_nonneg X) (transientAbsorptionExitWeight_nonneg X)
      (transientAbsorptionPotential_harmonic X) (transientDeletedQ_isUnit X) k

theorem transientReturnConditionedInitial_moment1_eq {s : ℕ}
    (X : TransientStart s) (hs : 2 ≤ s) (hp : 0 < transientReturnProbability X) :
    transientInitialMoment1 (s - 1) (transientReturnConditionedInitial X hs hp) =
      (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        ((1 - transientDeletedQ X)⁻¹.mulVec (transientReturnPotential X)) j) /
          transientReturnProbability X := by
  simpa [transientInitialMoment1, transientMoment1, TransientInitial.component,
    pow_one] using transientReturnConditionedInitial_resolvent_pow X hs hp 1

theorem transientTerminalConditionedInitial_moment1_eq {s : ℕ}
    (X : TransientStart s) (hs : 2 ≤ s) :
    transientInitialMoment1 (s - 1)
        (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X)) =
      (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        ((1 - transientDeletedQ X)⁻¹.mulVec (transientAbsorptionPotential X)) j) /
          transientTerminalProbability X := by
  simpa [transientInitialMoment1, transientMoment1, TransientInitial.component,
    pow_one] using transientTerminalConditionedInitial_resolvent_pow X hs
      (transientTerminalProbability_pos X) 1

theorem transientReturnConditionedInitial_moment2_eq {s : ℕ}
    (X : TransientStart s) (hs : 2 ≤ s) (hp : 0 < transientReturnProbability X) :
    transientInitialMoment2 (s - 1) (transientReturnConditionedInitial X hs hp) =
      2 * ((∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        (((1 - transientDeletedQ X)⁻¹ ^ 2).mulVec (transientReturnPotential X)) j) /
          transientReturnProbability X) := by
  have h := congrArg (fun z : ℝ => 2 * z)
    (transientReturnConditionedInitial_resolvent_pow X hs hp 2)
  simpa [transientInitialMoment2, transientMoment2, TransientInitial.component,
    pow_two, ← Matrix.mulVec_mulVec, Finset.mul_sum, mul_assoc, mul_comm,
    mul_left_comm] using h

theorem transientTerminalConditionedInitial_moment2_eq {s : ℕ}
    (X : TransientStart s) (hs : 2 ≤ s) :
    transientInitialMoment2 (s - 1)
        (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X)) =
      2 * ((∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        (((1 - transientDeletedQ X)⁻¹ ^ 2).mulVec
          (transientAbsorptionPotential X)) j) / transientTerminalProbability X) := by
  have h := congrArg (fun z : ℝ => 2 * z)
    (transientTerminalConditionedInitial_resolvent_pow X hs
      (transientTerminalProbability_pos X) 2)
  simpa [transientInitialMoment2, transientMoment2, TransientInitial.component,
    pow_two, ← Matrix.mulVec_mulVec, Finset.mul_sum, mul_assoc, mul_comm,
    mul_left_comm] using h

theorem transientReturnConditionedInitial_moment3_eq {s : ℕ}
    (X : TransientStart s) (hs : 2 ≤ s) (hp : 0 < transientReturnProbability X) :
    transientInitialMoment3 (s - 1) (transientReturnConditionedInitial X hs hp) =
      6 * ((∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        (((1 - transientDeletedQ X)⁻¹ ^ 3).mulVec (transientReturnPotential X)) j) /
          transientReturnProbability X) := by
  have h := congrArg (fun z : ℝ => 6 * z)
    (transientReturnConditionedInitial_resolvent_pow X hs hp 3)
  simpa [transientInitialMoment3, transientMoment3, TransientInitial.component,
    pow_three, ← Matrix.mulVec_mulVec, Finset.mul_sum, mul_assoc, mul_comm,
    mul_left_comm] using h

theorem transientTerminalConditionedInitial_moment3_eq {s : ℕ}
    (X : TransientStart s) (hs : 2 ≤ s) :
    transientInitialMoment3 (s - 1)
        (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X)) =
      6 * ((∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        (((1 - transientDeletedQ X)⁻¹ ^ 3).mulVec
          (transientAbsorptionPotential X)) j) / transientTerminalProbability X) := by
  have h := congrArg (fun z : ℝ => 6 * z)
    (transientTerminalConditionedInitial_resolvent_pow X hs
      (transientTerminalProbability_pos X) 3)
  simpa [transientInitialMoment3, transientMoment3, TransientInitial.component,
    pow_three, ← Matrix.mulVec_mulVec, Finset.mul_sum, mul_assoc, mul_comm,
    mul_left_comm] using h

/-- The normalized initial law of the return-conditioned excursion. -/
noncomputable def returnConditionedInitial {s : ℕ} (X : AbsorptionStart s) (hs : 2 ≤ s)
    (hp : 0 < returnProbability X) : TransientInitial (s - 1) where
  model := returnConditionedStart X ⟨0, by omega⟩
  weight := fun j =>
    departureWeight X (otherStateIndex X.i j) * returnPotential X j /
      returnProbability X
  weight_nonneg := fun j => div_nonneg
    (mul_nonneg (departureWeight_nonneg X _) (returnPotential_nonneg X j)) hp.le
  weight_sum_le_one := by
    rw [← Finset.sum_div]
    change returnProbability X / returnProbability X ≤ 1
    rw [div_self hp.ne']

theorem returnConditionedInitial_weight_sum {s : ℕ} (X : AbsorptionStart s) (hs : 2 ≤ s)
    (hp : 0 < returnProbability X) :
    ∑ j, (returnConditionedInitial X hs hp).weight j = 1 := by
  unfold returnConditionedInitial
  rw [← Finset.sum_div]
  change returnProbability X / returnProbability X = 1
  exact div_self hp.ne'

/-- A total choice of return-excursion law.  When return has positive probability this is the
conditioned law; when return is impossible, an arbitrary pure lower-order law is used because
all terms involving it are multiplied by `p = 0`. -/
noncomputable def returnExcursionInitial {s : ℕ} (X : AbsorptionStart s) (hs : 2 ≤ s) :
    TransientInitial (s - 1) :=
  if hp : 0 < returnProbability X then returnConditionedInitial X hs hp
  else pureTransientInitial (returnConditionedStart X ⟨0, by omega⟩)

theorem returnExcursionInitial_weight_sum {s : ℕ} (X : AbsorptionStart s) (hs : 2 ≤ s) :
    ∑ j, (returnExcursionInitial X hs).weight j = 1 := by
  unfold returnExcursionInitial
  split_ifs with hp
  · exact returnConditionedInitial_weight_sum X hs hp
  · simp [pureTransientInitial]

/-- The normalized initial law of the terminal excursion.  Its missing initial mass is the
conditional probability of immediate absorption at the distinguished-state departure. -/
noncomputable def terminalConditionedInitial {s : ℕ} (X : AbsorptionStart s) (hs : 2 ≤ s)
    (hq : 0 < terminalProbability X) : TransientInitial (s - 1) where
  model := terminalConditionedStart X ⟨0, by omega⟩
  weight := fun j =>
    departureWeight X (otherStateIndex X.i j) * absorptionPotential X j /
      terminalProbability X
  weight_nonneg := fun j => div_nonneg
    (mul_nonneg (departureWeight_nonneg X _) (absorptionPotential_nonneg X j)) hq.le
  weight_sum_le_one := by
    rw [← Finset.sum_div]
    apply (div_le_one hq).mpr
    unfold terminalProbability
    linarith [directExitWeight_nonneg X]

theorem returnConditionedInitial_resolvent_pow {s : ℕ} (X : AbsorptionStart s)
    (hs : 2 ≤ s) (hp : 0 < returnProbability X) (k : ℕ) :
    (∑ j, (returnConditionedInitial X hs hp).weight j *
      (((1 - (returnConditionedInitial X hs hp).model.Q)⁻¹ ^ k).mulVec
        (fun _ => (1 : ℝ))) j) =
      (∑ j, departureWeight X (otherStateIndex X.i j) *
        (((1 - deletedQ X)⁻¹ ^ k).mulVec (returnPotential X)) j) /
          returnProbability X := by
  simpa [returnConditionedInitial, returnConditionedStart, returnConditionedQ] using
    weighted_doobResolvent_pow_div (deletedQ X) (returnPotential X)
      (returnExitWeight X) (fun j => departureWeight X (otherStateIndex X.i j))
      (returnProbability X) (deletedQ_nonneg X) (returnPotential_nonneg X)
      (returnExitWeight_nonneg X) (returnPotential_harmonic X)
      (isUnit_one_sub_of_norm_lt_one
        (lt_of_le_of_lt ((deletedQ_norm_le X).trans X.hnorm) X.hθ)) k

theorem terminalConditionedInitial_resolvent_pow {s : ℕ} (X : AbsorptionStart s)
    (hs : 2 ≤ s) (hq : 0 < terminalProbability X) (k : ℕ) :
    (∑ j, (terminalConditionedInitial X hs hq).weight j *
      (((1 - (terminalConditionedInitial X hs hq).model.Q)⁻¹ ^ k).mulVec
        (fun _ => (1 : ℝ))) j) =
      (∑ j, departureWeight X (otherStateIndex X.i j) *
        (((1 - deletedQ X)⁻¹ ^ k).mulVec (absorptionPotential X)) j) /
          terminalProbability X := by
  simpa [terminalConditionedInitial, terminalConditionedStart, terminalConditionedQ] using
    weighted_doobResolvent_pow_div (deletedQ X) (absorptionPotential X)
      (absorptionExitWeight X) (fun j => departureWeight X (otherStateIndex X.i j))
      (terminalProbability X) (deletedQ_nonneg X) (absorptionPotential_nonneg X)
      (absorptionExitWeight_nonneg X) (absorptionPotential_harmonic X)
      (isUnit_one_sub_of_norm_lt_one
        (lt_of_le_of_lt ((deletedQ_norm_le X).trans X.hnorm) X.hθ)) k

theorem returnConditionedInitial_moment1_eq {s : ℕ} (X : AbsorptionStart s)
    (hs : 2 ≤ s) (hp : 0 < returnProbability X) :
    transientInitialMoment1 (s - 1) (returnConditionedInitial X hs hp) =
      (∑ j, departureWeight X (otherStateIndex X.i j) *
        ((1 - deletedQ X)⁻¹.mulVec (returnPotential X)) j) /
          returnProbability X := by
  simpa [transientInitialMoment1, transientMoment1, TransientInitial.component,
    pow_one] using returnConditionedInitial_resolvent_pow X hs hp 1

theorem terminalConditionedInitial_moment1_eq {s : ℕ} (X : AbsorptionStart s)
    (hs : 2 ≤ s) :
    transientInitialMoment1 (s - 1)
        (terminalConditionedInitial X hs (terminalProbability_pos X)) =
      (∑ j, departureWeight X (otherStateIndex X.i j) *
        ((1 - deletedQ X)⁻¹.mulVec (absorptionPotential X)) j) /
          terminalProbability X := by
  simpa [transientInitialMoment1, transientMoment1, TransientInitial.component,
    pow_one] using terminalConditionedInitial_resolvent_pow X hs (terminalProbability_pos X) 1

theorem returnConditionedInitial_moment2_eq {s : ℕ} (X : AbsorptionStart s)
    (hs : 2 ≤ s) (hp : 0 < returnProbability X) :
    transientInitialMoment2 (s - 1) (returnConditionedInitial X hs hp) =
      2 * ((∑ j, departureWeight X (otherStateIndex X.i j) *
        (((1 - deletedQ X)⁻¹ ^ 2).mulVec (returnPotential X)) j) /
          returnProbability X) := by
  have h := congrArg (fun z : ℝ => 2 * z)
    (returnConditionedInitial_resolvent_pow X hs hp 2)
  simpa [transientInitialMoment2, transientMoment2, TransientInitial.component,
    pow_two, ← Matrix.mulVec_mulVec, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using h

theorem terminalConditionedInitial_moment2_eq {s : ℕ} (X : AbsorptionStart s)
    (hs : 2 ≤ s) :
    transientInitialMoment2 (s - 1)
        (terminalConditionedInitial X hs (terminalProbability_pos X)) =
      2 * ((∑ j, departureWeight X (otherStateIndex X.i j) *
        (((1 - deletedQ X)⁻¹ ^ 2).mulVec (absorptionPotential X)) j) /
          terminalProbability X) := by
  have h := congrArg (fun z : ℝ => 2 * z)
    (terminalConditionedInitial_resolvent_pow X hs (terminalProbability_pos X) 2)
  simpa [transientInitialMoment2, transientMoment2, TransientInitial.component,
    pow_two, ← Matrix.mulVec_mulVec, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using h

theorem returnConditionedInitial_moment3_eq {s : ℕ} (X : AbsorptionStart s)
    (hs : 2 ≤ s) (hp : 0 < returnProbability X) :
    transientInitialMoment3 (s - 1) (returnConditionedInitial X hs hp) =
      6 * ((∑ j, departureWeight X (otherStateIndex X.i j) *
        (((1 - deletedQ X)⁻¹ ^ 3).mulVec (returnPotential X)) j) /
          returnProbability X) := by
  have h := congrArg (fun z : ℝ => 6 * z)
    (returnConditionedInitial_resolvent_pow X hs hp 3)
  simpa [transientInitialMoment3, transientMoment3, TransientInitial.component,
    pow_three, ← Matrix.mulVec_mulVec, Finset.mul_sum, mul_assoc, mul_comm,
    mul_left_comm] using h

theorem terminalConditionedInitial_moment3_eq {s : ℕ} (X : AbsorptionStart s)
    (hs : 2 ≤ s) :
    transientInitialMoment3 (s - 1)
        (terminalConditionedInitial X hs (terminalProbability_pos X)) =
      6 * ((∑ j, departureWeight X (otherStateIndex X.i j) *
        (((1 - deletedQ X)⁻¹ ^ 3).mulVec (absorptionPotential X)) j) /
          terminalProbability X) := by
  have h := congrArg (fun z : ℝ => 6 * z)
    (terminalConditionedInitial_resolvent_pow X hs (terminalProbability_pos X) 3)
  simpa [transientInitialMoment3, transientMoment3, TransientInitial.component,
    pow_three, ← Matrix.mulVec_mulVec, Finset.mul_sum, mul_assoc, mul_comm,
    mul_left_comm] using h

/-! ## Block resolvent equations for the renewal identities -/

/-- General-transient version of the distinguished-coordinate resolvent equation. -/
theorem transient_resolvent_at_start {s : ℕ} (X : TransientStart s) (v : Fin s → ℝ) :
    ((1 - X.Q)⁻¹.mulVec v) X.i =
      transientHoldingMean X * v X.i +
        ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
          ((1 - X.Q)⁻¹.mulVec v) (otherStateIndex X.i j) := by
  let z := (1 - X.Q)⁻¹.mulVec v
  have hdet : IsUnit (1 - X.Q).det := Matrix.isUnit_iff_isUnit_det _ |>.mp X.hu
  have hsolve : (1 - X.Q).mulVec z = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (1 - X.Q) hdet,
      Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hsolve
  have hi' := congrFun hsolve X.i
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
    (f := fun j => X.Q X.i j * z j) (Finset.mem_univ X.i)
  simp only [Matrix.mulVec, dotProduct, Pi.sub_apply] at hi'
  have heq : transientExitRate X * z X.i -
      ∑ j ∈ (Finset.univ : Finset (Fin s)).erase X.i, X.Q X.i j * z j =
        v X.i := by
    unfold transientExitRate
    rw [← hsplit] at hi'
    linarith
  have hoff :
      ∑ j ∈ (Finset.univ : Finset (Fin s)).erase X.i, X.Q X.i j * z j =
        transientExitRate X *
          ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
            z (otherStateIndex X.i j) := by
    rw [Finset.mul_sum, ← image_otherStateIndex X.i,
      Finset.sum_image (otherStateIndex_injective X.i).injOn]
    apply Finset.sum_congr rfl
    intro j _
    simp only [transientDepartureWeight, otherStateIndex_ne X.i j, if_false]
    field_simp [(transientExitRate_pos X).ne']
  rw [hoff] at heq
  unfold transientHoldingMean
  have hlambda := (transientExitRate_pos X).ne'
  field_simp [hlambda]
  nlinarith

theorem transient_resolvent_at_other {s : ℕ} (X : TransientStart s)
    (v : Fin s → ℝ) (j : Fin (s - 1)) :
    ((1 - X.Q)⁻¹.mulVec v) (otherStateIndex X.i j) =
      ((1 - transientDeletedQ X)⁻¹.mulVec (fun k =>
        v (otherStateIndex X.i k) + transientReturnExitWeight X k *
          ((1 - X.Q)⁻¹.mulVec v) X.i)) j := by
  let z := (1 - X.Q)⁻¹.mulVec v
  let zo : Fin (s - 1) → ℝ := fun k => z (otherStateIndex X.i k)
  let rhs : Fin (s - 1) → ℝ := fun k =>
    v (otherStateIndex X.i k) + transientReturnExitWeight X k * z X.i
  have hdet : IsUnit (1 - X.Q).det := Matrix.isUnit_iff_isUnit_det _ |>.mp X.hu
  have hsolve : (1 - X.Q).mulVec z = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (1 - X.Q) hdet,
      Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hsolve
  have hblock : (1 - transientDeletedQ X).mulVec zo = rhs := by
    funext k
    let r := otherStateIndex X.i k
    have hr := congrFun hsolve r
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.sub_apply] at hr ⊢
    have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
      (f := fun l => X.Q r l * z l) (Finset.mem_univ X.i)
    have hdeleted : ∑ l, transientDeletedQ X k l * zo l =
        ∑ l ∈ (Finset.univ : Finset (Fin s)).erase X.i, X.Q r l * z l := by
      unfold transientDeletedQ zo
      rw [← image_otherStateIndex X.i,
        Finset.sum_image (otherStateIndex_injective X.i).injOn]
      rfl
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib]
    have hone : ∑ l : Fin (s - 1),
        (1 : Matrix (Fin (s - 1)) (Fin (s - 1)) ℝ) k l * zo l = zo k := by
      simp [Matrix.one_apply]
    rw [hone, hdeleted]
    dsimp [rhs, zo, r]
    unfold transientReturnExitWeight
    rw [← hsplit] at hr
    linarith
  have hdetB : IsUnit (1 - transientDeletedQ X).det :=
    Matrix.isUnit_iff_isUnit_det _ |>.mp (transientDeletedQ_isUnit X)
  have hmul := congrArg
    (fun w : Fin (s - 1) → ℝ => (1 - transientDeletedQ X)⁻¹.mulVec w) hblock
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul (1 - transientDeletedQ X) hdetB,
    Matrix.one_mulVec] at hmul
  exact congrFun hmul j

theorem transient_resolvent_at_other_split {s : ℕ} (X : TransientStart s)
    (v : Fin s → ℝ) (j : Fin (s - 1)) :
    ((1 - X.Q)⁻¹.mulVec v) (otherStateIndex X.i j) =
      ((1 - transientDeletedQ X)⁻¹.mulVec
        (fun k => v (otherStateIndex X.i k))) j +
      transientReturnPotential X j * ((1 - X.Q)⁻¹.mulVec v) X.i := by
  rw [transient_resolvent_at_other X v j]
  unfold Matrix.mulVec dotProduct transientReturnPotential
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    ∑ k, (1 - transientDeletedQ X)⁻¹ j k *
        (transientReturnExitWeight X k * ((1 - X.Q)⁻¹.mulVec v) X.i) =
        ∑ k, ((1 - transientDeletedQ X)⁻¹ j k * transientReturnExitWeight X k) *
          ((1 - X.Q)⁻¹.mulVec v) X.i := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = (∑ k, (1 - transientDeletedQ X)⁻¹ j k * transientReturnExitWeight X k) *
        ((1 - X.Q)⁻¹.mulVec v) X.i := by rw [Finset.sum_mul]

theorem transient_departure_average_resolvent_other {s : ℕ} (X : TransientStart s)
    (v : Fin s → ℝ) :
    (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
      ((1 - X.Q)⁻¹.mulVec v) (otherStateIndex X.i j)) =
      (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        ((1 - transientDeletedQ X)⁻¹.mulVec
          (fun k => v (otherStateIndex X.i k))) j) +
      transientReturnProbability X * ((1 - X.Q)⁻¹.mulVec v) X.i := by
  calc
    (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
      ((1 - X.Q)⁻¹.mulVec v) (otherStateIndex X.i j)) =
        ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
          (((1 - transientDeletedQ X)⁻¹.mulVec
            (fun k => v (otherStateIndex X.i k))) j +
            transientReturnPotential X j * ((1 - X.Q)⁻¹.mulVec v) X.i) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [transient_resolvent_at_other_split]
    _ = (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
          ((1 - transientDeletedQ X)⁻¹.mulVec
            (fun k => v (otherStateIndex X.i k))) j) +
        transientReturnProbability X * ((1 - X.Q)⁻¹.mulVec v) X.i := by
      unfold transientReturnProbability
      simp only [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
            (transientReturnPotential X j * ((1 - X.Q)⁻¹.mulVec v) X.i) =
            ∑ j, (transientDepartureWeight X (otherStateIndex X.i j) *
              transientReturnPotential X j) * ((1 - X.Q)⁻¹.mulVec v) X.i := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
              transientReturnPotential X j) * ((1 - X.Q)⁻¹.mulVec v) X.i := by
          rw [Finset.sum_mul]

noncomputable def transientReturnPower {s : ℕ} (X : TransientStart s) (k : ℕ) : ℝ :=
  ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
    (((1 - transientDeletedQ X)⁻¹ ^ k).mulVec (transientReturnPotential X)) j

noncomputable def transientTerminalPower {s : ℕ} (X : TransientStart s) (k : ℕ) : ℝ :=
  ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
    (((1 - transientDeletedQ X)⁻¹ ^ k).mulVec (transientAbsorptionPotential X)) j

theorem transientReturnPower_add_terminalPower {s : ℕ} (X : TransientStart s) (k : ℕ) :
    transientReturnPower X k + transientTerminalPower X k =
      ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        (((1 - transientDeletedQ X)⁻¹ ^ k).mulVec (fun _ => (1 : ℝ))) j := by
  unfold transientReturnPower transientTerminalPower
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_add]
  have hvec : transientReturnPotential X + transientAbsorptionPotential X =
      (fun _ => (1 : ℝ)) := by
    funext l
    exact transientReturnPotential_add_absorptionPotential X l
  rw [← Pi.add_apply, ← Matrix.mulVec_add, hvec]

@[simp] theorem transientReturnPower_zero {s : ℕ} (X : TransientStart s) :
    transientReturnPower X 0 = transientReturnProbability X := by
  simp [transientReturnPower, transientReturnProbability]

theorem transientTerminalPower_zero_add_direct {s : ℕ} (X : TransientStart s) :
    transientTerminalPower X 0 + transientDirectExitWeight X =
      transientTerminalProbability X := by
  simp [transientTerminalPower, transientTerminalProbability, add_comm]

theorem transientReturnPower_eq_zero_of_returnProbability_eq_zero {s : ℕ}
    (X : TransientStart s) (hp0 : transientReturnProbability X = 0) (k : ℕ) :
    transientReturnPower X k = 0 := by
  have hterms : ∀ j, transientDepartureWeight X (otherStateIndex X.i j) *
      transientReturnPotential X j = 0 := by
    have hsum : ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        transientReturnPotential X j = 0 := by
      simpa [transientReturnProbability] using hp0
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin (s - 1)))) =>
        mul_nonneg (transientDepartureWeight_nonneg X _)
          (transientReturnPotential_nonneg X j))).mp hsum
    exact fun j => hall j (Finset.mem_univ j)
  have hraw := weighted_doobResolvent_pow (transientDeletedQ X)
    (transientReturnPotential X) (transientReturnExitWeight X)
    (fun j => transientDepartureWeight X (otherStateIndex X.i j))
    (transientDeletedQ_nonneg X) (transientReturnPotential_nonneg X)
    (transientReturnExitWeight_nonneg X) (transientReturnPotential_harmonic X)
    (transientDeletedQ_isUnit X) k
  rw [show (∑ j, (transientDepartureWeight X (otherStateIndex X.i j) *
      transientReturnPotential X j) *
      (((1 - doobTransform (transientDeletedQ X) (transientReturnPotential X))⁻¹ ^ k).mulVec
        (fun _ => (1 : ℝ))) j) = 0 by simp [hterms]] at hraw
  unfold transientReturnPower
  linarith

theorem mulVec_mul_const {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (u : Fin m → ℝ) (c : ℝ) :
    M.mulVec (fun k => u k * c) = fun j => (M.mulVec u) j * c := by
  funext j
  unfold Matrix.mulVec dotProduct
  calc
    ∑ k, M j k * (u k * c) = ∑ k, (M j k * u k) * c := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = (∑ k, M j k * u k) * c := by rw [Finset.sum_mul]

theorem transient_first_resolvent_renewal {s : ℕ} (X : TransientStart s) :
    transientTerminalProbability X *
        ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i =
      transientHoldingMean X + transientReturnPower X 1 +
        transientTerminalPower X 1 := by
  let z := ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i
  let avg := ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
    ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) (otherStateIndex X.i j)
  have hs : z = transientHoldingMean X + avg := by
    simpa [z, avg] using transient_resolvent_at_start X (fun _ => (1 : ℝ))
  have ha0 := transient_departure_average_resolvent_other X (fun _ => (1 : ℝ))
  have htotal := transientReturnPower_add_terminalPower X 1
  have hkill :
      (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        ((1 - transientDeletedQ X)⁻¹.mulVec (fun _ => (1 : ℝ))) j) =
        transientReturnPower X 1 + transientTerminalPower X 1 := by
    simpa [pow_one] using htotal.symm
  have ha : avg = transientReturnPower X 1 + transientTerminalPower X 1 +
      transientReturnProbability X * z := by
    simpa [avg, z, hkill] using ha0
  have hpqz := congrArg (fun t : ℝ => t * z)
    (transientReturnProbability_add_terminalProbability X)
  change transientTerminalProbability X * z =
    transientHoldingMean X + transientReturnPower X 1 + transientTerminalPower X 1
  nlinarith [hpqz]

theorem transient_second_resolvent_renewal {s : ℕ} (X : TransientStart s) :
    transientTerminalProbability X *
        ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) X.i =
      (transientHoldingMean X + transientReturnPower X 1) *
          ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i +
        transientReturnPower X 2 + transientTerminalPower X 2 := by
  let N := (1 - X.Q)⁻¹
  let NB := (1 - transientDeletedQ X)⁻¹
  let one : Fin s → ℝ := fun _ => 1
  let zvec := N.mulVec one
  let z := zvec X.i
  let y := (N.mulVec zvec) X.i
  let zo : Fin (s - 1) → ℝ := fun k => zvec (otherStateIndex X.i k)
  have hzo : zo = NB.mulVec (fun _ => (1 : ℝ)) +
      fun k => transientReturnPotential X k * z := by
    funext k
    simpa [N, NB, one, zvec, z, zo] using
      transient_resolvent_at_other_split X (fun _ => (1 : ℝ)) k
  have hNBzo : NB.mulVec zo =
      (NB ^ 2).mulVec (fun _ => (1 : ℝ)) +
        fun k => (NB.mulVec (transientReturnPotential X)) k * z := by
    rw [hzo, Matrix.mulVec_add]
    congr 1
    · rw [pow_two, ← Matrix.mulVec_mulVec]
    · exact mulVec_mul_const NB (transientReturnPotential X) z
  have hkill :
      (∑ j, transientDepartureWeight X (otherStateIndex X.i j) * (NB.mulVec zo) j) =
        transientReturnPower X 2 + transientTerminalPower X 2 +
          transientReturnPower X 1 * z := by
    rw [hNBzo]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have htotal := transientReturnPower_add_terminalPower X 2
    have hfirst :
        ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
            ((NB ^ 2).mulVec (fun _ => (1 : ℝ))) j =
          transientReturnPower X 2 + transientTerminalPower X 2 := by
      simpa [NB] using htotal.symm
    rw [hfirst]
    unfold transientReturnPower
    simp only [pow_one]
    congr 1
    calc
      ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
          ((NB.mulVec (transientReturnPotential X)) j * z) =
          ∑ j, (transientDepartureWeight X (otherStateIndex X.i j) *
            (NB.mulVec (transientReturnPotential X)) j) * z := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
          (NB.mulVec (transientReturnPotential X)) j) * z := by rw [Finset.sum_mul]
  have hs0 := transient_resolvent_at_start X zvec
  have ha0 := transient_departure_average_resolvent_other X zvec
  have hs : y = transientHoldingMean X * z +
      ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        (N.mulVec zvec) (otherStateIndex X.i j) := by
    simpa [N, zvec, z, y] using hs0
  have ha :
      (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        (N.mulVec zvec) (otherStateIndex X.i j)) =
        transientReturnPower X 2 + transientTerminalPower X 2 +
          transientReturnPower X 1 * z + transientReturnProbability X * y := by
    simpa [N, NB, zvec, z, y, zo, hkill] using ha0
  have hpqy := congrArg (fun t : ℝ => t * y)
    (transientReturnProbability_add_terminalProbability X)
  change transientTerminalProbability X * y =
    (transientHoldingMean X + transientReturnPower X 1) * z +
      transientReturnPower X 2 + transientTerminalPower X 2
  nlinarith [hpqy]

theorem transient_third_resolvent_renewal {s : ℕ} (X : TransientStart s) :
    transientTerminalProbability X *
        ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
          ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) X.i =
      (transientHoldingMean X + transientReturnPower X 1) *
          ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) X.i +
        transientReturnPower X 2 *
          ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i +
        transientReturnPower X 3 + transientTerminalPower X 3 := by
  let N := (1 - X.Q)⁻¹
  let NB := (1 - transientDeletedQ X)⁻¹
  let one : Fin s → ℝ := fun _ => 1
  let zvec := N.mulVec one
  let yvec := N.mulVec zvec
  let z := zvec X.i
  let y := yvec X.i
  let w := (N.mulVec yvec) X.i
  let zo : Fin (s - 1) → ℝ := fun k => zvec (otherStateIndex X.i k)
  let yo : Fin (s - 1) → ℝ := fun k => yvec (otherStateIndex X.i k)
  have hzo : zo = NB.mulVec (fun _ => (1 : ℝ)) +
      fun k => transientReturnPotential X k * z := by
    funext k
    simpa [N, NB, one, zvec, z, zo] using
      transient_resolvent_at_other_split X (fun _ => (1 : ℝ)) k
  have hNBzo : NB.mulVec zo =
      (NB ^ 2).mulVec (fun _ => (1 : ℝ)) +
        fun k => (NB.mulVec (transientReturnPotential X)) k * z := by
    rw [hzo, Matrix.mulVec_add]
    congr 1
    · rw [pow_two, ← Matrix.mulVec_mulVec]
    · exact mulVec_mul_const NB (transientReturnPotential X) z
  have hyo : yo =
      (NB ^ 2).mulVec (fun _ => (1 : ℝ)) +
        (fun k => (NB.mulVec (transientReturnPotential X)) k * z) +
        fun k => transientReturnPotential X k * y := by
    funext k
    have hk := transient_resolvent_at_other_split X zvec k
    change yo k = (NB.mulVec zo) k + transientReturnPotential X k * y at hk
    rw [hNBzo] at hk
    exact hk
  have hNByo : NB.mulVec yo =
      (NB ^ 3).mulVec (fun _ => (1 : ℝ)) +
        (fun k => ((NB ^ 2).mulVec (transientReturnPotential X)) k * z) +
        fun k => (NB.mulVec (transientReturnPotential X)) k * y := by
    rw [hyo, Matrix.mulVec_add, Matrix.mulVec_add]
    congr 1
    · congr 1
      · simp only [pow_three, pow_two, Matrix.mulVec_mulVec]
      · rw [mulVec_mul_const, pow_two, ← Matrix.mulVec_mulVec]
    · exact mulVec_mul_const NB (transientReturnPotential X) y
  have hkill :
      (∑ j, transientDepartureWeight X (otherStateIndex X.i j) * (NB.mulVec yo) j) =
        transientReturnPower X 3 + transientTerminalPower X 3 +
          transientReturnPower X 2 * z + transientReturnPower X 1 * y := by
    rw [hNByo]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have htotal := transientReturnPower_add_terminalPower X 3
    have hthird :
        ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
            ((NB ^ 3).mulVec (fun _ => (1 : ℝ))) j =
          transientReturnPower X 3 + transientTerminalPower X 3 := by
      simpa [NB] using htotal.symm
    rw [hthird]
    unfold transientReturnPower
    simp only [pow_one]
    have hzsum :
        ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
            (((NB ^ 2).mulVec (transientReturnPotential X)) j * z) =
          (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
            ((NB ^ 2).mulVec (transientReturnPotential X)) j) * z := by
      calc
        _ = ∑ j, (transientDepartureWeight X (otherStateIndex X.i j) *
            ((NB ^ 2).mulVec (transientReturnPotential X)) j) * z := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [Finset.sum_mul]
    have hysum :
        ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
            ((NB.mulVec (transientReturnPotential X)) j * y) =
          (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
            (NB.mulVec (transientReturnPotential X)) j) * y := by
      calc
        _ = ∑ j, (transientDepartureWeight X (otherStateIndex X.i j) *
            (NB.mulVec (transientReturnPotential X)) j) * y := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [Finset.sum_mul]
    rw [hzsum, hysum]
  have hs0 := transient_resolvent_at_start X yvec
  have ha0 := transient_departure_average_resolvent_other X yvec
  have hs : w = transientHoldingMean X * y +
      ∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        (N.mulVec yvec) (otherStateIndex X.i j) := by
    simpa [N, yvec, y, w] using hs0
  have ha :
      (∑ j, transientDepartureWeight X (otherStateIndex X.i j) *
        (N.mulVec yvec) (otherStateIndex X.i j)) =
        transientReturnPower X 3 + transientTerminalPower X 3 +
          transientReturnPower X 2 * z + transientReturnPower X 1 * y +
          transientReturnProbability X * w := by
    simpa [N, NB, yvec, z, y, w, yo, hkill] using ha0
  have hpqw := congrArg (fun t : ℝ => t * w)
    (transientReturnProbability_add_terminalProbability X)
  change transientTerminalProbability X * w =
    (transientHoldingMean X + transientReturnPower X 1) * y +
      transientReturnPower X 2 * z + transientReturnPower X 3 +
        transientTerminalPower X 3
  nlinarith [hpqw]

/-! ## From a canonical similarity to the order-three moment certificate -/

theorem canonicalW1_scaled (x1 x2 x3 x13 : ℝ) (hx1 : 0 < x1)
    (hx2 : 0 < x2) (hx3 : 0 < x3) (hlt : x13 < x1) (i : Fin 3) :
    SSP.Canonical.canW1 x1 x2 x3 x13 i = SSP.Canonical.canDen x1 x2 x3 x13 *
      ((SSP.Canonical.negA x1 x2 x3 x13)⁻¹.mulVec (fun _ => (1 : ℝ))) i := by
  have hc := SSP.Canonical.canDen_pos x1 x2 x3 x13 hx1 hx2 hx3 hlt
  rw [congrFun (SSP.Canonical.canW1_eq_inv x1 x2 x3 x13 hc.ne') i]
  unfold Matrix.mulVec dotProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem canonicalW2_scaled (x1 x2 x3 x13 : ℝ) (hx1 : 0 < x1)
    (hx2 : 0 < x2) (hx3 : 0 < x3) (hlt : x13 < x1) (i : Fin 3) :
    SSP.Canonical.canW2 x1 x2 x3 x13 i = SSP.Canonical.canDen x1 x2 x3 x13 ^ 2 *
      (((SSP.Canonical.negA x1 x2 x3 x13)⁻¹ ^ 2).mulVec
        (fun _ => (1 : ℝ))) i := by
  have hc := SSP.Canonical.canDen_pos x1 x2 x3 x13 hx1 hx2 hx3 hlt
  rw [congrFun (SSP.Canonical.canW2_eq_inv x1 x2 x3 x13 hc.ne') i]
  simp_rw [canonicalW1_scaled x1 x2 x3 x13 hx1 hx2 hx3 hlt]
  simp only [pow_two]
  rw [← Matrix.mulVec_mulVec]
  unfold Matrix.mulVec dotProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem canonicalW3_scaled (x1 x2 x3 x13 : ℝ) (hx1 : 0 < x1)
    (hx2 : 0 < x2) (hx3 : 0 < x3) (hlt : x13 < x1) (i : Fin 3) :
    SSP.Canonical.canW3 x1 x2 x3 x13 i = SSP.Canonical.canDen x1 x2 x3 x13 ^ 3 *
      (((SSP.Canonical.negA x1 x2 x3 x13)⁻¹ ^ 3).mulVec
        (fun _ => (1 : ℝ))) i := by
  have hc := SSP.Canonical.canDen_pos x1 x2 x3 x13 hx1 hx2 hx3 hlt
  rw [congrFun (SSP.Canonical.canW3_eq_inv x1 x2 x3 x13 hc.ne') i]
  simp_rw [canonicalW2_scaled x1 x2 x3 x13 hx1 hx2 hx3 hlt]
  have hp3 : ((SSP.Canonical.negA x1 x2 x3 x13)⁻¹ ^ 3).mulVec
      (fun _ => (1 : ℝ)) =
      (SSP.Canonical.negA x1 x2 x3 x13)⁻¹.mulVec
        (((SSP.Canonical.negA x1 x2 x3 x13)⁻¹ ^ 2).mulVec
          (fun _ => (1 : ℝ))) := by
    rw [pow_succ']
    exact (Matrix.mulVec_mulVec _ _ _).symm
  rw [hp3]
  unfold Matrix.mulVec dotProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem canonicalMoment_eq_resolvent_pow (x1 x2 x3 x13 : ℝ)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3) (hlt : x13 < x1)
    (k i : Fin 3) :
    SSP.Canonical.canMoment x1 x2 x3 x13 k i =
      (((SSP.Canonical.negA x1 x2 x3 x13)⁻¹ ^ (k.val + 1)).mulVec
        (fun _ => (1 : ℝ))) i := by
  have hc := SSP.Canonical.canDen_pos x1 x2 x3 x13 hx1 hx2 hx3 hlt
  fin_cases k
  · rw [SSP.Canonical.canMoment.eq_def]
    change SSP.Canonical.canW1 x1 x2 x3 x13 i /
      SSP.Canonical.canDen x1 x2 x3 x13 = _
    rw [canonicalW1_scaled x1 x2 x3 x13 hx1 hx2 hx3 hlt]
    norm_num
    field_simp [hc.ne']
  · rw [SSP.Canonical.canMoment.eq_def]
    change SSP.Canonical.canW2 x1 x2 x3 x13 i /
      SSP.Canonical.canDen x1 x2 x3 x13 ^ 2 = _
    rw [canonicalW2_scaled x1 x2 x3 x13 hx1 hx2 hx3 hlt]
    norm_num
    field_simp [hc.ne']
  · rw [SSP.Canonical.canMoment.eq_def]
    change SSP.Canonical.canW3 x1 x2 x3 x13 i /
      SSP.Canonical.canDen x1 x2 x3 x13 ^ 3 = _
    rw [canonicalW3_scaled x1 x2 x3 x13 hx1 hx2 hx3 hlt]
    norm_num
    field_simp [hc.ne']

theorem similarity_inverse_intertwine (X : TransientStart 3)
    (c : TransientOrderThreeSimilarityRepresentation X) :
    (1 - X.Q)⁻¹ * c.S =
      c.S * (SSP.Canonical.negA c.x1 c.x2 c.x3 c.x13)⁻¹ := by
  let G := 1 - X.Q
  let A := SSP.Canonical.negA c.x1 c.x2 c.x3 c.x13
  have hGdet : IsUnit G.det := Matrix.isUnit_iff_isUnit_det G |>.mp X.hu
  have hcden := SSP.Canonical.canDen_pos c.x1 c.x2 c.x3 c.x13
    c.x1_pos c.x2_pos c.x3_pos c.x13_lt
  have hAdet : IsUnit A.det := by
    dsimp [A]
    exact SSP.Canonical.negA_isUnit_det c.x1 c.x2 c.x3 c.x13 hcden.ne'
  change G⁻¹ * c.S = c.S * A⁻¹
  calc
    G⁻¹ * c.S = (G⁻¹ * c.S) * 1 := by rw [Matrix.mul_one]
    _ = (G⁻¹ * c.S) * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv A hAdet]
    _ = G⁻¹ * (c.S * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
    _ = G⁻¹ * (G * c.S) * A⁻¹ := by rw [c.intertwine]
    _ = c.S * A⁻¹ := by
      rw [← Matrix.mul_assoc G⁻¹ G c.S, Matrix.nonsing_inv_mul G hGdet,
        Matrix.one_mul]

theorem similarity_inverse_pow_intertwine (X : TransientStart 3)
    (c : TransientOrderThreeSimilarityRepresentation X) (k : ℕ) :
    (1 - X.Q)⁻¹ ^ k * c.S =
      c.S * (SSP.Canonical.negA c.x1 c.x2 c.x3 c.x13)⁻¹ ^ k := by
  have hbase := similarity_inverse_intertwine X c
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ, Matrix.mul_assoc, hbase, ← Matrix.mul_assoc, ih]
      rw [Matrix.mul_assoc]

theorem similarity_resolvent_power_vector (X : TransientStart 3)
    (c : TransientOrderThreeSimilarityRepresentation X) (k : ℕ) :
    ((1 - X.Q)⁻¹ ^ k).mulVec (fun _ => (1 : ℝ)) =
      c.S.mulVec
        (((SSP.Canonical.negA c.x1 c.x2 c.x3 c.x13)⁻¹ ^ k).mulVec
          (fun _ => (1 : ℝ))) := by
  have hp := similarity_inverse_pow_intertwine X c k
  calc
    ((1 - X.Q)⁻¹ ^ k).mulVec (fun _ => (1 : ℝ)) =
        ((1 - X.Q)⁻¹ ^ k).mulVec (c.S.mulVec (fun _ => (1 : ℝ))) := by
      rw [c.preserve_one]
    _ = (((1 - X.Q)⁻¹ ^ k) * c.S).mulVec (fun _ => (1 : ℝ)) :=
      Matrix.mulVec_mulVec _ _ _
    _ = (c.S * (SSP.Canonical.negA c.x1 c.x2 c.x3 c.x13)⁻¹ ^ k).mulVec
        (fun _ => (1 : ℝ)) := by rw [hp]
    _ = c.S.mulVec
        (((SSP.Canonical.negA c.x1 c.x2 c.x3 c.x13)⁻¹ ^ k).mulVec
          (fun _ => (1 : ℝ))) := (Matrix.mulVec_mulVec _ _ _).symm

theorem similarity_resolvent_power_at_start (X : TransientStart 3)
    (c : TransientOrderThreeSimilarityRepresentation X) (k : ℕ) :
    (((1 - X.Q)⁻¹ ^ k).mulVec (fun _ => (1 : ℝ))) X.i =
      ∑ j, c.pi j *
        (((SSP.Canonical.negA c.x1 c.x2 c.x3 c.x13)⁻¹ ^ k).mulVec
          (fun _ => (1 : ℝ))) j := by
  have h := congrFun (similarity_resolvent_power_vector X c k) X.i
  simpa [Matrix.mulVec, dotProduct, c.initial_row] using h

/-- A genuine similarity-form He--Zhang representation supplies the moment certificate used by
the order-three inequality. -/
noncomputable def canonicalCertificateOfSimilarity (X : TransientStart 3)
    (c : TransientOrderThreeSimilarityRepresentation X) :
    TransientOrderThreeCanonicalCertificate X where
  x1 := c.x1
  x2 := c.x2
  x3 := c.x3
  x13 := c.x13
  pi := c.pi
  x1_pos := c.x1_pos
  x2_pos := c.x2_pos
  x3_pos := c.x3_pos
  x13_nonneg := c.x13_nonneg
  x13_lt := c.x13_lt
  pi_nonneg := c.pi_nonneg
  moment1_eq := by
    have h := similarity_resolvent_power_at_start X c 1
    simp only [pow_one] at h
    unfold transientMoment1
    simpa [canonicalMoment_eq_resolvent_pow c.x1 c.x2 c.x3 c.x13
      c.x1_pos c.x2_pos c.x3_pos c.x13_lt 0, pow_one] using h
  moment2_eq := by
    have h := congrArg (fun z : ℝ => 2 * z)
      (similarity_resolvent_power_at_start X c 2)
    unfold transientMoment2
    simpa [pow_two, ← Matrix.mulVec_mulVec,
      canonicalMoment_eq_resolvent_pow c.x1 c.x2 c.x3 c.x13
        c.x1_pos c.x2_pos c.x3_pos c.x13_lt 1,
      Fin.val_one, one_add_one_eq_two] using h
  moment3_eq := by
    have h := congrArg (fun z : ℝ => 6 * z)
      (similarity_resolvent_power_at_start X c 3)
    unfold transientMoment3
    simpa [pow_three, ← Matrix.mulVec_mulVec,
      canonicalMoment_eq_resolvent_pow c.x1 c.x2 c.x3 c.x13
        c.x1_pos c.x2_pos c.x3_pos c.x13_lt 2,
      Fin.val_two, Nat.reduceAdd] using h

/-- The distinguished component of a resolvent solve, written after removing diagonal
self-loops. -/
theorem resolvent_at_start {s : ℕ} (X : AbsorptionStart s) (v : Fin s → ℝ) :
    ((1 - X.Q)⁻¹.mulVec v) X.i =
      holdingMean X * v X.i +
        ∑ j, departureWeight X (otherStateIndex X.i j) *
          ((1 - X.Q)⁻¹.mulVec v) (otherStateIndex X.i j) := by
  let z := (1 - X.Q)⁻¹.mulVec v
  have hdet : IsUnit (1 - X.Q).det := Matrix.isUnit_iff_isUnit_det _ |>.mp X.hu
  have hsolve : (1 - X.Q).mulVec z = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (1 - X.Q) hdet,
      Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hsolve
  have hi' := congrFun hsolve X.i
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
    (f := fun j => X.Q X.i j * z j) (Finset.mem_univ X.i)
  simp only [Matrix.mulVec, dotProduct, Pi.sub_apply] at hi'
  have heq : exitRate X * z X.i -
      ∑ j ∈ (Finset.univ : Finset (Fin s)).erase X.i, X.Q X.i j * z j = v X.i := by
    unfold exitRate
    rw [← hsplit] at hi'
    linarith
  have hoff :
      ∑ j ∈ (Finset.univ : Finset (Fin s)).erase X.i, X.Q X.i j * z j =
        exitRate X *
          ∑ j, departureWeight X (otherStateIndex X.i j) * z (otherStateIndex X.i j) := by
    rw [Finset.mul_sum, ← image_otherStateIndex X.i,
      Finset.sum_image (otherStateIndex_injective X.i).injOn]
    apply Finset.sum_congr rfl
    intro j _
    simp only [departureWeight, otherStateIndex_ne X.i j, if_false]
    field_simp [(exitRate_pos X).ne']
  rw [hoff] at heq
  unfold holdingMean
  have hlambda := (exitRate_pos X).ne'
  field_simp [hlambda]
  nlinarith

/-- The complementary components of a full resolvent solve are obtained by solving on the
deleted block, with the return edge contributing the distinguished component as boundary data. -/
theorem resolvent_at_other {s : ℕ} (X : AbsorptionStart s) (v : Fin s → ℝ)
    (j : Fin (s - 1)) :
    ((1 - X.Q)⁻¹.mulVec v) (otherStateIndex X.i j) =
      ((1 - deletedQ X)⁻¹.mulVec (fun k =>
        v (otherStateIndex X.i k) + returnExitWeight X k *
          ((1 - X.Q)⁻¹.mulVec v) X.i)) j := by
  let z := (1 - X.Q)⁻¹.mulVec v
  let zo : Fin (s - 1) → ℝ := fun k => z (otherStateIndex X.i k)
  let rhs : Fin (s - 1) → ℝ := fun k =>
    v (otherStateIndex X.i k) + returnExitWeight X k * z X.i
  have hdet : IsUnit (1 - X.Q).det := Matrix.isUnit_iff_isUnit_det _ |>.mp X.hu
  have hsolve : (1 - X.Q).mulVec z = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (1 - X.Q) hdet,
      Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hsolve
  have hblock : (1 - deletedQ X).mulVec zo = rhs := by
    funext k
    let r := otherStateIndex X.i k
    have hr := congrFun hsolve r
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.sub_apply] at hr ⊢
    have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin s)))
      (f := fun l => X.Q r l * z l) (Finset.mem_univ X.i)
    have hdeleted : ∑ l, deletedQ X k l * zo l =
        ∑ l ∈ (Finset.univ : Finset (Fin s)).erase X.i, X.Q r l * z l := by
      unfold deletedQ zo
      rw [← image_otherStateIndex X.i,
        Finset.sum_image (otherStateIndex_injective X.i).injOn]
      rfl
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib]
    have hone : ∑ l : Fin (s - 1),
        (1 : Matrix (Fin (s - 1)) (Fin (s - 1)) ℝ) k l * zo l = zo k := by
      simp [Matrix.one_apply]
    rw [hone, hdeleted]
    dsimp [rhs, zo, r]
    unfold returnExitWeight
    rw [← hsplit] at hr
    linarith
  have hdetB : IsUnit (1 - deletedQ X).det :=
    Matrix.isUnit_iff_isUnit_det _ |>.mp
      (isUnit_one_sub_of_norm_lt_one
        (lt_of_le_of_lt ((deletedQ_norm_le X).trans X.hnorm) X.hθ))
  have hmul := congrArg (fun w : Fin (s - 1) → ℝ => (1 - deletedQ X)⁻¹.mulVec w) hblock
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul (1 - deletedQ X) hdetB,
    Matrix.one_mulVec] at hmul
  exact congrFun hmul j

/-- Split the complementary resolvent solve into its killed-chain part and the contribution from
a later return to the distinguished state. -/
theorem resolvent_at_other_split {s : ℕ} (X : AbsorptionStart s) (v : Fin s → ℝ)
    (j : Fin (s - 1)) :
    ((1 - X.Q)⁻¹.mulVec v) (otherStateIndex X.i j) =
      ((1 - deletedQ X)⁻¹.mulVec (fun k => v (otherStateIndex X.i k))) j +
        returnPotential X j * ((1 - X.Q)⁻¹.mulVec v) X.i := by
  rw [resolvent_at_other X v j]
  unfold Matrix.mulVec dotProduct returnPotential
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    ∑ k, (1 - deletedQ X)⁻¹ j k *
        (returnExitWeight X k * ((1 - X.Q)⁻¹.mulVec v) X.i) =
        ∑ k, ((1 - deletedQ X)⁻¹ j k * returnExitWeight X k) *
          ((1 - X.Q)⁻¹.mulVec v) X.i := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = (∑ k, (1 - deletedQ X)⁻¹ j k * returnExitWeight X k) *
        ((1 - X.Q)⁻¹.mulVec v) X.i := by rw [Finset.sum_mul]

/-- Average form of `resolvent_at_other_split` under the genuine-departure distribution. -/
theorem departure_average_resolvent_other {s : ℕ} (X : AbsorptionStart s)
    (v : Fin s → ℝ) :
    (∑ j, departureWeight X (otherStateIndex X.i j) *
      ((1 - X.Q)⁻¹.mulVec v) (otherStateIndex X.i j)) =
      (∑ j, departureWeight X (otherStateIndex X.i j) *
        ((1 - deletedQ X)⁻¹.mulVec (fun k => v (otherStateIndex X.i k))) j) +
        returnProbability X * ((1 - X.Q)⁻¹.mulVec v) X.i := by
  calc
    (∑ j, departureWeight X (otherStateIndex X.i j) *
      ((1 - X.Q)⁻¹.mulVec v) (otherStateIndex X.i j)) =
        ∑ j, departureWeight X (otherStateIndex X.i j) *
          (((1 - deletedQ X)⁻¹.mulVec (fun k => v (otherStateIndex X.i k))) j +
            returnPotential X j * ((1 - X.Q)⁻¹.mulVec v) X.i) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [resolvent_at_other_split]
    _ = (∑ j, departureWeight X (otherStateIndex X.i j) *
          ((1 - deletedQ X)⁻¹.mulVec (fun k => v (otherStateIndex X.i k))) j) +
        returnProbability X * ((1 - X.Q)⁻¹.mulVec v) X.i := by
      unfold returnProbability
      simp only [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        ∑ j, departureWeight X (otherStateIndex X.i j) *
            (returnPotential X j * ((1 - X.Q)⁻¹.mulVec v) X.i) =
            ∑ j, (departureWeight X (otherStateIndex X.i j) * returnPotential X j) *
              ((1 - X.Q)⁻¹.mulVec v) X.i := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (∑ j, departureWeight X (otherStateIndex X.i j) * returnPotential X j) *
            ((1 - X.Q)⁻¹.mulVec v) X.i := by rw [Finset.sum_mul]

/-- Unnormalized return-excursion resolvent power under the departure distribution. -/
noncomputable def returnPower {s : ℕ} (X : AbsorptionStart s) (k : ℕ) : ℝ :=
  ∑ j, departureWeight X (otherStateIndex X.i j) *
    (((1 - deletedQ X)⁻¹ ^ k).mulVec (returnPotential X)) j

/-- Unnormalized terminal-excursion resolvent power under the departure distribution. -/
noncomputable def terminalPower {s : ℕ} (X : AbsorptionStart s) (k : ℕ) : ℝ :=
  ∑ j, departureWeight X (otherStateIndex X.i j) *
    (((1 - deletedQ X)⁻¹ ^ k).mulVec (absorptionPotential X)) j

theorem returnPower_add_terminalPower {s : ℕ} (X : AbsorptionStart s) (k : ℕ) :
    returnPower X k + terminalPower X k =
      ∑ j, departureWeight X (otherStateIndex X.i j) *
        (((1 - deletedQ X)⁻¹ ^ k).mulVec (fun _ => (1 : ℝ))) j := by
  unfold returnPower terminalPower
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_add]
  have hvec : returnPotential X + absorptionPotential X = (fun _ => (1 : ℝ)) := by
    funext l
    exact returnPotential_add_absorptionPotential X l
  rw [← Pi.add_apply, ← Matrix.mulVec_add, hvec]

@[simp] theorem returnPower_zero {s : ℕ} (X : AbsorptionStart s) :
    returnPower X 0 = returnProbability X := by
  simp [returnPower, returnProbability]

theorem terminalPower_zero_add_direct {s : ℕ} (X : AbsorptionStart s) :
    terminalPower X 0 + directExitWeight X = terminalProbability X := by
  simp [terminalPower, terminalProbability, add_comm]

/-- If the return event has probability zero, every unnormalized return-excursion resolvent
moment vanishes. -/
theorem returnPower_eq_zero_of_returnProbability_eq_zero {s : ℕ} (X : AbsorptionStart s)
    (hp0 : returnProbability X = 0) (k : ℕ) : returnPower X k = 0 := by
  have hterms : ∀ j, departureWeight X (otherStateIndex X.i j) * returnPotential X j = 0 := by
    have hsum : ∑ j, departureWeight X (otherStateIndex X.i j) * returnPotential X j = 0 := by
      simpa [returnProbability] using hp0
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin (s - 1)))) =>
        mul_nonneg (departureWeight_nonneg X _) (returnPotential_nonneg X j))).mp hsum
    exact fun j => hall j (Finset.mem_univ j)
  have hraw := weighted_doobResolvent_pow (deletedQ X) (returnPotential X)
    (returnExitWeight X) (fun j => departureWeight X (otherStateIndex X.i j))
    (deletedQ_nonneg X) (returnPotential_nonneg X) (returnExitWeight_nonneg X)
    (returnPotential_harmonic X)
    (isUnit_one_sub_of_norm_lt_one
      (lt_of_le_of_lt ((deletedQ_norm_le X).trans X.hnorm) X.hθ)) k
  rw [show (∑ j, (departureWeight X (otherStateIndex X.i j) * returnPotential X j) *
      (((1 - doobTransform (deletedQ X) (returnPotential X))⁻¹ ^ k).mulVec
        (fun _ => (1 : ℝ))) j) = 0 by simp [hterms]] at hraw
  unfold returnPower
  linarith

/-- First resolvent recurrence at the distinguished state. -/
theorem first_resolvent_renewal {s : ℕ} (X : AbsorptionStart s) :
    terminalProbability X * ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i =
      holdingMean X + returnPower X 1 + terminalPower X 1 := by
  let z := ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i
  let avg := ∑ j, departureWeight X (otherStateIndex X.i j) *
    ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) (otherStateIndex X.i j)
  have hs : z = holdingMean X + avg := by
    simpa [z, avg] using resolvent_at_start X (fun _ => (1 : ℝ))
  have ha0 := departure_average_resolvent_other X (fun _ => (1 : ℝ))
  have htotal := returnPower_add_terminalPower X 1
  have hkill :
      (∑ j, departureWeight X (otherStateIndex X.i j) *
        ((1 - deletedQ X)⁻¹.mulVec (fun _ => (1 : ℝ))) j) =
        returnPower X 1 + terminalPower X 1 := by
    simpa [pow_one] using htotal.symm
  have ha : avg = returnPower X 1 + terminalPower X 1 + returnProbability X * z := by
    simpa [avg, z, hkill] using ha0
  have hpqz := congrArg (fun t : ℝ => t * z) (returnProbability_add_terminalProbability X)
  change terminalProbability X * z = holdingMean X + returnPower X 1 + terminalPower X 1
  nlinarith [hpqz]

/-- Second iterated-resolvent recurrence at the distinguished state. -/
theorem second_resolvent_renewal {s : ℕ} (X : AbsorptionStart s) :
    terminalProbability X *
        ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) X.i =
      (holdingMean X + returnPower X 1) *
          ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i +
        returnPower X 2 + terminalPower X 2 := by
  let N := (1 - X.Q)⁻¹
  let NB := (1 - deletedQ X)⁻¹
  let one : Fin s → ℝ := fun _ => 1
  let zvec := N.mulVec one
  let z := zvec X.i
  let y := (N.mulVec zvec) X.i
  let zo : Fin (s - 1) → ℝ := fun k => zvec (otherStateIndex X.i k)
  have hzo : zo = NB.mulVec (fun _ => (1 : ℝ)) + fun k => returnPotential X k * z := by
    funext k
    simpa [N, NB, one, zvec, z, zo] using
      resolvent_at_other_split X (fun _ => (1 : ℝ)) k
  have hNBzo : NB.mulVec zo =
      (NB ^ 2).mulVec (fun _ => (1 : ℝ)) +
        fun k => (NB.mulVec (returnPotential X)) k * z := by
    rw [hzo, Matrix.mulVec_add]
    congr 1
    · rw [pow_two, ← Matrix.mulVec_mulVec]
    · unfold Matrix.mulVec dotProduct
      funext j
      calc
        ∑ k, NB j k * (returnPotential X k * z) =
            ∑ k, (NB j k * returnPotential X k) * z := by
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = (∑ k, NB j k * returnPotential X k) * z := by rw [Finset.sum_mul]
  have hkill :
      (∑ j, departureWeight X (otherStateIndex X.i j) * (NB.mulVec zo) j) =
        returnPower X 2 + terminalPower X 2 + returnPower X 1 * z := by
    rw [hNBzo]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have htotal := returnPower_add_terminalPower X 2
    have hfirst :
        ∑ j, departureWeight X (otherStateIndex X.i j) *
            ((NB ^ 2).mulVec (fun _ => (1 : ℝ))) j =
          returnPower X 2 + terminalPower X 2 := by
      simpa [NB] using htotal.symm
    rw [hfirst]
    unfold returnPower
    simp only [pow_one]
    congr 1
    calc
      ∑ j, departureWeight X (otherStateIndex X.i j) *
          ((NB.mulVec (returnPotential X)) j * z) =
          ∑ j, (departureWeight X (otherStateIndex X.i j) *
            (NB.mulVec (returnPotential X)) j) * z := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (∑ j, departureWeight X (otherStateIndex X.i j) *
          (NB.mulVec (returnPotential X)) j) * z := by rw [Finset.sum_mul]
  have hs0 := resolvent_at_start X zvec
  have ha0 := departure_average_resolvent_other X zvec
  have hs : y = holdingMean X * z +
      ∑ j, departureWeight X (otherStateIndex X.i j) *
        (N.mulVec zvec) (otherStateIndex X.i j) := by
    simpa [N, zvec, z, y] using hs0
  have ha :
      (∑ j, departureWeight X (otherStateIndex X.i j) *
        (N.mulVec zvec) (otherStateIndex X.i j)) =
        returnPower X 2 + terminalPower X 2 + returnPower X 1 * z +
          returnProbability X * y := by
    simpa [N, NB, zvec, z, y, zo, hkill] using ha0
  have hpqy := congrArg (fun t : ℝ => t * y) (returnProbability_add_terminalProbability X)
  change terminalProbability X * y =
    (holdingMean X + returnPower X 1) * z + returnPower X 2 + terminalPower X 2
  nlinarith [hpqy]

/-- Third iterated-resolvent recurrence at the distinguished state. -/
theorem third_resolvent_renewal {s : ℕ} (X : AbsorptionStart s) :
    terminalProbability X *
        ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
          ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) X.i =
      (holdingMean X + returnPower X 1) *
          ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) X.i +
        returnPower X 2 * ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i +
        returnPower X 3 + terminalPower X 3 := by
  let N := (1 - X.Q)⁻¹
  let NB := (1 - deletedQ X)⁻¹
  let one : Fin s → ℝ := fun _ => 1
  let zvec := N.mulVec one
  let yvec := N.mulVec zvec
  let z := zvec X.i
  let y := yvec X.i
  let w := (N.mulVec yvec) X.i
  let zo : Fin (s - 1) → ℝ := fun k => zvec (otherStateIndex X.i k)
  let yo : Fin (s - 1) → ℝ := fun k => yvec (otherStateIndex X.i k)
  have hzo : zo = NB.mulVec (fun _ => (1 : ℝ)) + fun k => returnPotential X k * z := by
    funext k
    simpa [N, NB, one, zvec, z, zo] using
      resolvent_at_other_split X (fun _ => (1 : ℝ)) k
  have hNBzo : NB.mulVec zo =
      (NB ^ 2).mulVec (fun _ => (1 : ℝ)) +
        fun k => (NB.mulVec (returnPotential X)) k * z := by
    rw [hzo, Matrix.mulVec_add]
    congr 1
    · rw [pow_two, ← Matrix.mulVec_mulVec]
    · exact mulVec_mul_const NB (returnPotential X) z
  have hyo : yo =
      (NB ^ 2).mulVec (fun _ => (1 : ℝ)) +
        (fun k => (NB.mulVec (returnPotential X)) k * z) +
        fun k => returnPotential X k * y := by
    funext k
    have hk := resolvent_at_other_split X zvec k
    change yo k = (NB.mulVec zo) k + returnPotential X k * y at hk
    rw [hNBzo] at hk
    exact hk
  have hNByo : NB.mulVec yo =
      (NB ^ 3).mulVec (fun _ => (1 : ℝ)) +
        (fun k => ((NB ^ 2).mulVec (returnPotential X)) k * z) +
        fun k => (NB.mulVec (returnPotential X)) k * y := by
    rw [hyo, Matrix.mulVec_add, Matrix.mulVec_add]
    congr 1
    · congr 1
      · simp only [pow_three, pow_two, Matrix.mulVec_mulVec]
      · rw [mulVec_mul_const, pow_two, ← Matrix.mulVec_mulVec]
    · exact mulVec_mul_const NB (returnPotential X) y
  have hkill :
      (∑ j, departureWeight X (otherStateIndex X.i j) * (NB.mulVec yo) j) =
        returnPower X 3 + terminalPower X 3 + returnPower X 2 * z +
          returnPower X 1 * y := by
    rw [hNByo]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have htotal := returnPower_add_terminalPower X 3
    have hthird :
        ∑ j, departureWeight X (otherStateIndex X.i j) *
            ((NB ^ 3).mulVec (fun _ => (1 : ℝ))) j =
          returnPower X 3 + terminalPower X 3 := by
      simpa [NB] using htotal.symm
    rw [hthird]
    unfold returnPower
    simp only [pow_one]
    have hzsum :
        ∑ j, departureWeight X (otherStateIndex X.i j) *
            (((NB ^ 2).mulVec (returnPotential X)) j * z) =
          (∑ j, departureWeight X (otherStateIndex X.i j) *
            ((NB ^ 2).mulVec (returnPotential X)) j) * z := by
      calc
        _ = ∑ j, (departureWeight X (otherStateIndex X.i j) *
            ((NB ^ 2).mulVec (returnPotential X)) j) * z := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [Finset.sum_mul]
    have hysum :
        ∑ j, departureWeight X (otherStateIndex X.i j) *
            ((NB.mulVec (returnPotential X)) j * y) =
          (∑ j, departureWeight X (otherStateIndex X.i j) *
            (NB.mulVec (returnPotential X)) j) * y := by
      calc
        _ = ∑ j, (departureWeight X (otherStateIndex X.i j) *
            (NB.mulVec (returnPotential X)) j) * y := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [Finset.sum_mul]
    rw [hzsum, hysum]
  have hs0 := resolvent_at_start X yvec
  have ha0 := departure_average_resolvent_other X yvec
  have hs : w = holdingMean X * y +
      ∑ j, departureWeight X (otherStateIndex X.i j) *
        (N.mulVec yvec) (otherStateIndex X.i j) := by
    simpa [N, yvec, y, w] using hs0
  have ha :
      (∑ j, departureWeight X (otherStateIndex X.i j) *
        (N.mulVec yvec) (otherStateIndex X.i j)) =
        returnPower X 3 + terminalPower X 3 + returnPower X 2 * z +
          returnPower X 1 * y + returnProbability X * w := by
    simpa [N, NB, yvec, z, y, w, yo, hkill] using ha0
  have hpqw := congrArg (fun t : ℝ => t * w) (returnProbability_add_terminalProbability X)
  change terminalProbability X * w =
    (holdingMean X + returnPower X 1) * y + returnPower X 2 * z +
      returnPower X 3 + terminalPower X 3
  nlinarith [hpqw]

/-- The first raw moment has exactly the renewal form when the return branch has positive
probability. -/
theorem moment1_renewal_of_return_pos {s : ℕ} (X : AbsorptionStart s) (hs : 2 ≤ s)
    (hp : 0 < returnProbability X) :
    moment1 s X = SSP.K2AllStages.renewalM1 (holdingMean X)
      (transientInitialMoment1 (s - 1) (returnConditionedInitial X hs hp))
      (transientInitialMoment1 (s - 1)
        (terminalConditionedInitial X hs (terminalProbability_pos X)))
      (returnProbability X) (terminalProbability X) := by
  rw [moment1_eq, returnConditionedInitial_moment1_eq,
    terminalConditionedInitial_moment1_eq]
  unfold SSP.K2AllStages.renewalM1 SSP.K2AllStages.renewalX1
    SSP.K2AllStages.kernelM1
  have hrec := first_resolvent_renewal X
  unfold returnPower terminalPower at hrec
  simp only [pow_one] at hrec
  have hpne := hp.ne'
  have hqne := (terminalProbability_pos X).ne'
  field_simp [hpne, hqne]
  have hpqx := congrArg (fun t : ℝ => t * holdingMean X)
    (returnProbability_add_terminalProbability X)
  nlinarith [hrec, hpqx]

theorem renewalM2_from_power_recursions
    (x p q R1 A1 R2 A2 z y : ℝ) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : p + q = 1) (hz : q * z = x + R1 + A1)
    (hy : q * y = (x + R1) * z + R2 + A2) :
    2 * y = SSP.K2AllStages.renewalM2 x (R1 / p) (A1 / q) p q
      (2 * (R2 / p)) (2 * (A2 / q)) := by
  have peq : p = 1 - q := by linarith
  have zEq : z = (x + R1 + A1) / q := (eq_div_iff hq).2 (by linarith)
  have yEq : y = ((x + R1) * z + R2 + A2) / q :=
    (eq_div_iff hq).2 (by linarith)
  have honeq : 1 - q ≠ 0 := by rw [← peq]; exact hp
  rw [peq, yEq, zEq]
  unfold SSP.K2AllStages.renewalM2 SSP.K2AllStages.renewalX2
    SSP.K2AllStages.kernelM1 SSP.K2AllStages.kernelM2
  field_simp [honeq, hq]
  ring

/-- The second raw moment has the exact renewal form. -/
theorem moment2_renewal_of_return_pos {s : ℕ} (X : AbsorptionStart s) (hs : 2 ≤ s)
    (hp : 0 < returnProbability X) :
    moment2 s X = SSP.K2AllStages.renewalM2 (holdingMean X)
      (transientInitialMoment1 (s - 1) (returnConditionedInitial X hs hp))
      (transientInitialMoment1 (s - 1)
        (terminalConditionedInitial X hs (terminalProbability_pos X)))
      (returnProbability X) (terminalProbability X)
      (transientInitialMoment2 (s - 1) (returnConditionedInitial X hs hp))
      (transientInitialMoment2 (s - 1)
        (terminalConditionedInitial X hs (terminalProbability_pos X))) := by
  rw [moment2_eq, returnConditionedInitial_moment1_eq,
    terminalConditionedInitial_moment1_eq, returnConditionedInitial_moment2_eq,
    terminalConditionedInitial_moment2_eq]
  have hpne := hp.ne'
  have hqne := (terminalProbability_pos X).ne'
  have hmain := renewalM2_from_power_recursions
    (holdingMean X) (returnProbability X) (terminalProbability X)
    (returnPower X 1) (terminalPower X 1) (returnPower X 2) (terminalPower X 2)
    (((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i)
    (((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) X.i)
    hpne hqne (returnProbability_add_terminalProbability X)
    (first_resolvent_renewal X) (second_resolvent_renewal X)
  simpa [returnPower, terminalPower, pow_one] using hmain

theorem renewalM3_from_power_recursions
    (x p q R1 A1 R2 A2 R3 A3 z y w : ℝ) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : p + q = 1) (hz : q * z = x + R1 + A1)
    (hy : q * y = (x + R1) * z + R2 + A2)
    (hw : q * w = (x + R1) * y + R2 * z + R3 + A3) :
    6 * w = SSP.K2AllStages.renewalM3 x (R1 / p) (A1 / q) p q
      (2 * (R2 / p)) (2 * (A2 / q))
      (6 * (R3 / p)) (6 * (A3 / q)) := by
  have peq : p = 1 - q := by linarith
  have honeq : 1 - q ≠ 0 := by rw [← peq]; exact hp
  have zEq : z = (x + R1 + A1) / q := (eq_div_iff hq).2 (by linarith)
  have yEq : y = ((x + R1) * z + R2 + A2) / q :=
    (eq_div_iff hq).2 (by linarith)
  have wEq : w = ((x + R1) * y + R2 * z + R3 + A3) / q :=
    (eq_div_iff hq).2 (by linarith)
  rw [peq, wEq, yEq, zEq]
  unfold SSP.K2AllStages.renewalM3 SSP.K2AllStages.renewalX3
    SSP.K2AllStages.kernelM1 SSP.K2AllStages.kernelM2 SSP.K2AllStages.kernelM3
  field_simp [honeq, hq]
  ring

/-- The third raw moment has the exact renewal form. -/
theorem moment3_renewal_of_return_pos {s : ℕ} (X : AbsorptionStart s) (hs : 2 ≤ s)
    (hp : 0 < returnProbability X) :
    moment3 s X = SSP.K2AllStages.renewalM3 (holdingMean X)
      (transientInitialMoment1 (s - 1) (returnConditionedInitial X hs hp))
      (transientInitialMoment1 (s - 1)
        (terminalConditionedInitial X hs (terminalProbability_pos X)))
      (returnProbability X) (terminalProbability X)
      (transientInitialMoment2 (s - 1) (returnConditionedInitial X hs hp))
      (transientInitialMoment2 (s - 1)
        (terminalConditionedInitial X hs (terminalProbability_pos X)))
      (transientInitialMoment3 (s - 1) (returnConditionedInitial X hs hp))
      (transientInitialMoment3 (s - 1)
        (terminalConditionedInitial X hs (terminalProbability_pos X))) := by
  rw [moment3_eq, returnConditionedInitial_moment1_eq,
    terminalConditionedInitial_moment1_eq, returnConditionedInitial_moment2_eq,
    terminalConditionedInitial_moment2_eq, returnConditionedInitial_moment3_eq,
    terminalConditionedInitial_moment3_eq]
  have hpne := hp.ne'
  have hqne := (terminalProbability_pos X).ne'
  have hmain := renewalM3_from_power_recursions
    (holdingMean X) (returnProbability X) (terminalProbability X)
    (returnPower X 1) (terminalPower X 1) (returnPower X 2) (terminalPower X 2)
    (returnPower X 3) (terminalPower X 3)
    (((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i)
    (((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) X.i)
    (((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
      ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) X.i)
    hpne hqne (returnProbability_add_terminalProbability X)
    (first_resolvent_renewal X) (second_resolvent_renewal X) (third_resolvent_renewal X)
  simpa [returnPower, terminalPower, pow_one] using hmain

/-- When return is impossible, the renewal formulas reduce to one holding time followed by the
terminal excursion; the placeholder return law is immaterial. -/
theorem renewal_moments_of_return_zero {s : ℕ} (X : AbsorptionStart s) (hs : 2 ≤ s)
    (hp0 : returnProbability X = 0) (U : TransientInitial (s - 1)) :
    moment1 s X = SSP.K2AllStages.renewalM1 (holdingMean X)
        (transientInitialMoment1 (s - 1) U)
        (transientInitialMoment1 (s - 1)
          (terminalConditionedInitial X hs (terminalProbability_pos X)))
        (returnProbability X) (terminalProbability X) ∧
    moment2 s X = SSP.K2AllStages.renewalM2 (holdingMean X)
        (transientInitialMoment1 (s - 1) U)
        (transientInitialMoment1 (s - 1)
          (terminalConditionedInitial X hs (terminalProbability_pos X)))
        (returnProbability X) (terminalProbability X)
        (transientInitialMoment2 (s - 1) U)
        (transientInitialMoment2 (s - 1)
          (terminalConditionedInitial X hs (terminalProbability_pos X))) ∧
    moment3 s X = SSP.K2AllStages.renewalM3 (holdingMean X)
        (transientInitialMoment1 (s - 1) U)
        (transientInitialMoment1 (s - 1)
          (terminalConditionedInitial X hs (terminalProbability_pos X)))
        (returnProbability X) (terminalProbability X)
        (transientInitialMoment2 (s - 1) U)
        (transientInitialMoment2 (s - 1)
          (terminalConditionedInitial X hs (terminalProbability_pos X)))
        (transientInitialMoment3 (s - 1) U)
        (transientInitialMoment3 (s - 1)
          (terminalConditionedInitial X hs (terminalProbability_pos X))) := by
  have hq1 : terminalProbability X = 1 := by
    linarith [returnProbability_add_terminalProbability X]
  have hR1 := returnPower_eq_zero_of_returnProbability_eq_zero X hp0 1
  have hR2 := returnPower_eq_zero_of_returnProbability_eq_zero X hp0 2
  have hR3 := returnPower_eq_zero_of_returnProbability_eq_zero X hp0 3
  have hrec1 := first_resolvent_renewal X
  have hrec2 := second_resolvent_renewal X
  have hrec3 := third_resolvent_renewal X
  simp only [hq1, one_mul, hR1, hR2, hR3, add_zero, zero_mul] at hrec1 hrec2 hrec3
  unfold terminalPower at hrec1 hrec2 hrec3
  simp only [pow_one] at hrec1 hrec2 hrec3
  constructor
  · rw [moment1_eq, terminalConditionedInitial_moment1_eq]
    unfold SSP.K2AllStages.renewalM1 SSP.K2AllStages.renewalX1
      SSP.K2AllStages.kernelM1
    rw [hp0, hq1]
    norm_num at hrec1 ⊢
    exact hrec1
  constructor
  · rw [moment2_eq, terminalConditionedInitial_moment1_eq,
      terminalConditionedInitial_moment2_eq]
    unfold SSP.K2AllStages.renewalM2 SSP.K2AllStages.renewalX2
      SSP.K2AllStages.kernelM1 SSP.K2AllStages.kernelM2
    rw [hp0, hq1]
    norm_num at hrec1 hrec2 ⊢
    linear_combination 2 * hrec2 + 2 * holdingMean X * hrec1
  · rw [moment3_eq, terminalConditionedInitial_moment1_eq,
      terminalConditionedInitial_moment2_eq, terminalConditionedInitial_moment3_eq]
    unfold SSP.K2AllStages.renewalM3 SSP.K2AllStages.renewalX3
      SSP.K2AllStages.kernelM1 SSP.K2AllStages.kernelM2 SSP.K2AllStages.kernelM3
    rw [hp0, hq1]
    norm_num at hrec1 hrec2 hrec3 ⊢
    linear_combination 6 * hrec3 + 6 * holdingMean X * hrec2 +
      6 * holdingMean X ^ 2 * hrec1

/-- Exact renewal form of the first moment for a general transient start with positive return
probability. -/
theorem transientMoment1_renewal_of_return_pos {s : ℕ} (X : TransientStart s)
    (hs : 2 ≤ s) (hp : 0 < transientReturnProbability X) :
    transientMoment1 s X = SSP.K2AllStages.renewalM1 (transientHoldingMean X)
      (transientInitialMoment1 (s - 1) (transientReturnConditionedInitial X hs hp))
      (transientInitialMoment1 (s - 1)
        (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X)))
      (transientReturnProbability X) (transientTerminalProbability X) := by
  rw [transientReturnConditionedInitial_moment1_eq,
    transientTerminalConditionedInitial_moment1_eq]
  unfold transientMoment1 SSP.K2AllStages.renewalM1 SSP.K2AllStages.renewalX1
    SSP.K2AllStages.kernelM1
  have hrec := transient_first_resolvent_renewal X
  unfold transientReturnPower transientTerminalPower at hrec
  simp only [pow_one] at hrec
  have hpne := hp.ne'
  have hqne := (transientTerminalProbability_pos X).ne'
  field_simp [hpne, hqne]
  have hpqx := congrArg (fun t : ℝ => t * transientHoldingMean X)
    (transientReturnProbability_add_terminalProbability X)
  nlinarith [hrec, hpqx]

theorem transientMoment2_renewal_of_return_pos {s : ℕ} (X : TransientStart s)
    (hs : 2 ≤ s) (hp : 0 < transientReturnProbability X) :
    transientMoment2 s X = SSP.K2AllStages.renewalM2 (transientHoldingMean X)
      (transientInitialMoment1 (s - 1) (transientReturnConditionedInitial X hs hp))
      (transientInitialMoment1 (s - 1)
        (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X)))
      (transientReturnProbability X) (transientTerminalProbability X)
      (transientInitialMoment2 (s - 1) (transientReturnConditionedInitial X hs hp))
      (transientInitialMoment2 (s - 1)
        (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X))) := by
  rw [transientReturnConditionedInitial_moment1_eq,
    transientTerminalConditionedInitial_moment1_eq,
    transientReturnConditionedInitial_moment2_eq,
    transientTerminalConditionedInitial_moment2_eq]
  have hpne := hp.ne'
  have hqne := (transientTerminalProbability_pos X).ne'
  have hmain := renewalM2_from_power_recursions
    (transientHoldingMean X) (transientReturnProbability X)
    (transientTerminalProbability X) (transientReturnPower X 1)
    (transientTerminalPower X 1) (transientReturnPower X 2)
    (transientTerminalPower X 2)
    (((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i)
    (((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) X.i)
    hpne hqne (transientReturnProbability_add_terminalProbability X)
    (transient_first_resolvent_renewal X) (transient_second_resolvent_renewal X)
  simpa [transientMoment2, transientReturnPower, transientTerminalPower, pow_one] using hmain

theorem transientMoment3_renewal_of_return_pos {s : ℕ} (X : TransientStart s)
    (hs : 2 ≤ s) (hp : 0 < transientReturnProbability X) :
    transientMoment3 s X = SSP.K2AllStages.renewalM3 (transientHoldingMean X)
      (transientInitialMoment1 (s - 1) (transientReturnConditionedInitial X hs hp))
      (transientInitialMoment1 (s - 1)
        (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X)))
      (transientReturnProbability X) (transientTerminalProbability X)
      (transientInitialMoment2 (s - 1) (transientReturnConditionedInitial X hs hp))
      (transientInitialMoment2 (s - 1)
        (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X)))
      (transientInitialMoment3 (s - 1) (transientReturnConditionedInitial X hs hp))
      (transientInitialMoment3 (s - 1)
        (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X))) := by
  rw [transientReturnConditionedInitial_moment1_eq,
    transientTerminalConditionedInitial_moment1_eq,
    transientReturnConditionedInitial_moment2_eq,
    transientTerminalConditionedInitial_moment2_eq,
    transientReturnConditionedInitial_moment3_eq,
    transientTerminalConditionedInitial_moment3_eq]
  have hpne := hp.ne'
  have hqne := (transientTerminalProbability_pos X).ne'
  have hmain := renewalM3_from_power_recursions
    (transientHoldingMean X) (transientReturnProbability X)
    (transientTerminalProbability X) (transientReturnPower X 1)
    (transientTerminalPower X 1) (transientReturnPower X 2)
    (transientTerminalPower X 2) (transientReturnPower X 3)
    (transientTerminalPower X 3)
    (((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i)
    (((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) X.i)
    (((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
      ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) X.i)
    hpne hqne (transientReturnProbability_add_terminalProbability X)
    (transient_first_resolvent_renewal X) (transient_second_resolvent_renewal X)
    (transient_third_resolvent_renewal X)
  simpa [transientMoment3, transientReturnPower, transientTerminalPower, pow_one] using hmain

/-- When return is impossible, the placeholder return law disappears from all three renewal
formulas. -/
theorem transient_renewal_moments_of_return_zero {s : ℕ} (X : TransientStart s)
    (hs : 2 ≤ s) (hp0 : transientReturnProbability X = 0)
    (U : TransientInitial (s - 1)) :
    transientMoment1 s X = SSP.K2AllStages.renewalM1 (transientHoldingMean X)
        (transientInitialMoment1 (s - 1) U)
        (transientInitialMoment1 (s - 1)
          (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X)))
        (transientReturnProbability X) (transientTerminalProbability X) ∧
    transientMoment2 s X = SSP.K2AllStages.renewalM2 (transientHoldingMean X)
        (transientInitialMoment1 (s - 1) U)
        (transientInitialMoment1 (s - 1)
          (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X)))
        (transientReturnProbability X) (transientTerminalProbability X)
        (transientInitialMoment2 (s - 1) U)
        (transientInitialMoment2 (s - 1)
          (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X))) ∧
    transientMoment3 s X = SSP.K2AllStages.renewalM3 (transientHoldingMean X)
        (transientInitialMoment1 (s - 1) U)
        (transientInitialMoment1 (s - 1)
          (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X)))
        (transientReturnProbability X) (transientTerminalProbability X)
        (transientInitialMoment2 (s - 1) U)
        (transientInitialMoment2 (s - 1)
          (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X)))
        (transientInitialMoment3 (s - 1) U)
        (transientInitialMoment3 (s - 1)
          (transientTerminalConditionedInitial X hs (transientTerminalProbability_pos X))) := by
  have hq1 : transientTerminalProbability X = 1 := by
    linarith [transientReturnProbability_add_terminalProbability X]
  have hR1 := transientReturnPower_eq_zero_of_returnProbability_eq_zero X hp0 1
  have hR2 := transientReturnPower_eq_zero_of_returnProbability_eq_zero X hp0 2
  have hR3 := transientReturnPower_eq_zero_of_returnProbability_eq_zero X hp0 3
  have hrec1 := transient_first_resolvent_renewal X
  have hrec2 := transient_second_resolvent_renewal X
  have hrec3 := transient_third_resolvent_renewal X
  simp only [hq1, one_mul, hR1, hR2, hR3, add_zero, zero_mul] at hrec1 hrec2 hrec3
  unfold transientTerminalPower at hrec1 hrec2 hrec3
  simp only [pow_one] at hrec1 hrec2 hrec3
  constructor
  · rw [transientTerminalConditionedInitial_moment1_eq]
    unfold transientMoment1 SSP.K2AllStages.renewalM1 SSP.K2AllStages.renewalX1
      SSP.K2AllStages.kernelM1
    rw [hp0, hq1]
    norm_num at hrec1 ⊢
    exact hrec1
  constructor
  · rw [transientTerminalConditionedInitial_moment1_eq,
      transientTerminalConditionedInitial_moment2_eq]
    unfold transientMoment2 SSP.K2AllStages.renewalM2 SSP.K2AllStages.renewalX2
      SSP.K2AllStages.kernelM1 SSP.K2AllStages.kernelM2
    rw [hp0, hq1]
    norm_num at hrec1 hrec2 ⊢
    linear_combination 2 * hrec2 + 2 * transientHoldingMean X * hrec1
  · rw [transientTerminalConditionedInitial_moment1_eq,
      transientTerminalConditionedInitial_moment2_eq,
      transientTerminalConditionedInitial_moment3_eq]
    unfold transientMoment3 SSP.K2AllStages.renewalM3 SSP.K2AllStages.renewalX3
      SSP.K2AllStages.kernelM1 SSP.K2AllStages.kernelM2 SSP.K2AllStages.kernelM3
    rw [hp0, hq1]
    norm_num at hrec1 hrec2 hrec3 ⊢
    linear_combination 6 * hrec3 + 6 * transientHoldingMean X * hrec2 +
      6 * transientHoldingMean X ^ 2 * hrec1

/-- The deterministic component of a general initial law. -/
def AbsorptionInitial.component {s : ℕ} (X : AbsorptionInitial s)
    (i : Fin s) : AbsorptionStart s :=
  withStart X.model i

/-- First raw moment of a general initial law. -/
noncomputable def initialMoment1 (s : ℕ) (X : AbsorptionInitial s) : ℝ :=
  ∑ i, X.weight i * moment1 s (X.component i)

/-- Second raw moment of a general initial law. -/
noncomputable def initialMoment2 (s : ℕ) (X : AbsorptionInitial s) : ℝ :=
  ∑ i, X.weight i * moment2 s (X.component i)

/-- Third raw moment of a general initial law. -/
noncomputable def initialMoment3 (s : ℕ) (X : AbsorptionInitial s) : ℝ :=
  ∑ i, X.weight i * moment3 s (X.component i)

theorem initialMoment1_nonneg {s : ℕ} (X : AbsorptionInitial s) :
    0 ≤ initialMoment1 s X := by
  unfold initialMoment1
  exact sum_nonneg fun i _ => mul_nonneg (X.weight_nonneg i) (moment1_nonneg (X.component i))

theorem initialMoment2_nonneg {s : ℕ} (X : AbsorptionInitial s) :
    0 ≤ initialMoment2 s X := by
  unfold initialMoment2
  exact sum_nonneg fun i _ => mul_nonneg (X.weight_nonneg i) (moment2_nonneg (X.component i))

theorem initialMoment3_nonneg {s : ℕ} (X : AbsorptionInitial s) :
    0 ≤ initialMoment3 s X := by
  unfold initialMoment3
  exact sum_nonneg fun i _ => mul_nonneg (X.weight_nonneg i) (moment3_nonneg (X.component i))

/-- If the first moment of a general initial law is zero, all of its transient-state weights
vanish.  Each deterministic component has strictly positive mean. -/
theorem initial_weights_eq_zero_of_moment1_eq_zero {s : ℕ} (X : AbsorptionInitial s)
    (h : initialMoment1 s X = 0) : ∀ i, X.weight i = 0 := by
  unfold initialMoment1 at h
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin s))) =>
    mul_nonneg (X.weight_nonneg i) (moment1_nonneg (X.component i)))).mp h
  intro i
  exact (mul_eq_zero.mp (hall i (Finset.mem_univ i))).resolve_right
    (ne_of_gt (moment1_pos (X.component i)))

/-- Positive transient initial mass gives a strictly positive first moment. -/
theorem initialMoment1_pos_of_weight_sum_pos {s : ℕ} (X : AbsorptionInitial s)
    (hwpos : 0 < ∑ i, X.weight i) : 0 < initialMoment1 s X := by
  by_contra hnot
  have hm0 : initialMoment1 s X = 0 :=
    le_antisymm (le_of_not_gt hnot) (initialMoment1_nonneg X)
  have hw0 := initial_weights_eq_zero_of_moment1_eq_zero X hm0
  have : (∑ i, X.weight i) = 0 := by simp [hw0]
  linarith

/-- Zero first moment forces the two higher moments used here to vanish.  This also covers the
pure atom at zero, represented by an all-zero transient initial vector. -/
theorem initial_higher_moments_eq_zero_of_moment1_eq_zero {s : ℕ}
    (X : AbsorptionInitial s) (h : initialMoment1 s X = 0) :
    initialMoment2 s X = 0 ∧ initialMoment3 s X = 0 := by
  have hw0 := initial_weights_eq_zero_of_moment1_eq_zero X h
  constructor
  · unfold initialMoment2
    simp [hw0]
  · unfold initialMoment3
    simp [hw0]

/-- Weighted Cauchy--Schwarz in the form needed to pass the second-moment
Aldous--Shepp inequality from deterministic starts to a subprobability initial vector. -/
theorem weighted_sum_sq_le_sum_weighted_sq {s : ℕ} (w u : Fin s → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i ≤ 1) :
    (∑ i, w i * u i) ^ 2 ≤ ∑ i, w i * (u i) ^ 2 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin s))
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * u i)
  have e1 : ∑ i, Real.sqrt (w i) * (Real.sqrt (w i) * u i) =
      ∑ i, w i * u i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
  have e2 : ∑ i, (Real.sqrt (w i)) ^ 2 = ∑ i, w i := by
    apply Finset.sum_congr rfl
    intro i _
    exact Real.sq_sqrt (hw i)
  have e3 : ∑ i, (Real.sqrt (w i) * u i) ^ 2 = ∑ i, w i * (u i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, Real.sq_sqrt (hw i)]
  rw [e1, e2, e3] at hcs
  calc
    (∑ i, w i * u i) ^ 2
        ≤ (∑ i, w i) * ∑ i, w i * (u i) ^ 2 := hcs
    _ ≤ 1 * ∑ i, w i * (u i) ^ 2 := by
      apply mul_le_mul_of_nonneg_right hw1
      exact sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
    _ = ∑ i, w i * (u i) ^ 2 := one_mul _

theorem transientInitial_weights_eq_zero_of_moment1_eq_zero {s : ℕ}
    (X : TransientInitial s) (h : transientInitialMoment1 s X = 0) :
    ∀ i, X.weight i = 0 := by
  unfold transientInitialMoment1 at h
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin s))) =>
      mul_nonneg (X.weight_nonneg i) (transientMoment1_nonneg (X.component i)))).mp h
  intro i
  exact (mul_eq_zero.mp (hall i (Finset.mem_univ i))).resolve_right
    (ne_of_gt (transientMoment1_pos (X.component i)))

theorem transientInitialMoment1_pos_of_weight_sum_pos {s : ℕ} (X : TransientInitial s)
    (hwpos : 0 < ∑ i, X.weight i) : 0 < transientInitialMoment1 s X := by
  by_contra hnot
  have hm0 : transientInitialMoment1 s X = 0 :=
    le_antisymm (le_of_not_gt hnot) (transientInitialMoment1_nonneg X)
  have hw0 := transientInitial_weights_eq_zero_of_moment1_eq_zero X hm0
  have : (∑ i, X.weight i) = 0 := by simp [hw0]
  linarith

theorem transientInitial_higher_moments_eq_zero_of_moment1_eq_zero {s : ℕ}
    (X : TransientInitial s) (h : transientInitialMoment1 s X = 0) :
    transientInitialMoment2 s X = 0 ∧ transientInitialMoment3 s X = 0 := by
  have hw0 := transientInitial_weights_eq_zero_of_moment1_eq_zero X h
  constructor
  · unfold transientInitialMoment2
    simp [hw0]
  · unfold transientInitialMoment3
    simp [hw0]

/-- Aldous--Shepp is closed under subprobability mixtures in the general transient model. -/
theorem transientInitialAldousSheppMoment {s : ℕ} (hs : 1 ≤ s)
    (X : TransientInitial s) :
    ((s : ℝ) + 1) / s * (transientInitialMoment1 s X) ^ 2 ≤
      transientInitialMoment2 s X := by
  have hcoef : 0 ≤ ((s : ℝ) + 1) / s := by positivity
  have hcs := weighted_sum_sq_le_sum_weighted_sq X.weight
    (fun i => transientMoment1 s (X.component i)) X.weight_nonneg X.weight_sum_le_one
  calc
    ((s : ℝ) + 1) / s * (transientInitialMoment1 s X) ^ 2
        ≤ ((s : ℝ) + 1) / s *
            ∑ i, X.weight i * (transientMoment1 s (X.component i)) ^ 2 :=
      mul_le_mul_of_nonneg_left hcs hcoef
    _ = ∑ i, X.weight i *
          (((s : ℝ) + 1) / s * (transientMoment1 s (X.component i)) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, X.weight i * transientMoment2 s (X.component i) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (transientAldousSheppMoment hs (X.component i)) (X.weight_nonneg i)
    _ = transientInitialMoment2 s X := rfl

theorem transientInitialAldousSheppForParent {r n : ℕ} (hr : 1 ≤ r) (hrn : r < n)
    (X : TransientInitial r) :
    (n : ℝ) / (n - 1) * (transientInitialMoment1 r X) ^ 2 ≤
      transientInitialMoment2 r X := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hrnNat : r + 1 ≤ n := by omega
  have hrnR : (r : ℝ) + 1 ≤ n := by exact_mod_cast hrnNat
  have hrn' : (r : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hcoef : (n : ℝ) / (n - 1) ≤ ((r : ℝ) + 1) / r := by
    rw [div_le_div_iff₀ hn1 hr0]
    nlinarith
  calc
    (n : ℝ) / (n - 1) * (transientInitialMoment1 r X) ^ 2
        ≤ ((r : ℝ) + 1) / r * (transientInitialMoment1 r X) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ ≤ transientInitialMoment2 r X := transientInitialAldousSheppMoment hr X

theorem transientInitialStageBound_of_components {s : ℕ} (X : TransientInitial s)
    (hdet : ∀ i, SSP.K2AllStages.StageBound s
      (transientMoment1 s (X.component i)) (transientMoment2 s (X.component i))
      (transientMoment3 s (X.component i))) :
    SSP.K2AllStages.StageBound s
      (transientInitialMoment1 s X) (transientInitialMoment2 s X)
      (transientInitialMoment3 s X) := by
  unfold SSP.K2AllStages.StageBound transientInitialMoment1 transientInitialMoment2
    transientInitialMoment3
  have hm := SSP.K2AllStages.mixture_closure Finset.univ X.weight
    (fun i => transientMoment1 s (X.component i))
    (fun i => transientMoment2 s (X.component i))
    (fun i => transientMoment3 s (X.component i)) (s : ℝ)
    (by positivity)
    (fun i _ => X.weight_nonneg i)
    (fun i _ => transientMoment1_nonneg (X.component i))
    (fun i _ => transientMoment2_nonneg (X.component i))
    (fun i _ => transientMoment3_nonneg (X.component i))
    (fun i _ => by simpa [SSP.K2AllStages.StageBound, mul_assoc] using hdet i)
  simpa [mul_assoc] using hm

theorem transientInitialStageBound_one (X : TransientInitial 1) :
    SSP.K2AllStages.StageBound 1
      (transientInitialMoment1 1 X) (transientInitialMoment2 1 X)
      (transientInitialMoment3 1 X) := by
  exact transientInitialStageBound_of_components X
    (fun i => transientStageBound_one (X.component i))

theorem transientInitialStageBound_two (X : TransientInitial 2) :
    SSP.K2AllStages.StageBound 2
      (transientInitialMoment1 2 X) (transientInitialMoment2 2 X)
      (transientInitialMoment3 2 X) := by
  exact transientInitialStageBound_of_components X
    (fun i => transientStageBound_two (X.component i))

theorem transientInitialStageBound_three_of_canonical (X : TransientInitial 3)
    (hcanonical : ∀ Y : TransientStart 3, TransientOrderThreeCanonicalCertificate Y) :
    SSP.K2AllStages.StageBound 3
      (transientInitialMoment1 3 X) (transientInitialMoment2 3 X)
      (transientInitialMoment3 3 X) := by
  exact transientInitialStageBound_of_components X
    (fun i => transientStageBound_three_of_canonical (X.component i)
      (hcanonical (X.component i)))

/-- Aldous--Shepp for a general subprobability initial vector. -/
theorem initialAldousSheppMoment {s : ℕ} (hs : 1 ≤ s) (X : AbsorptionInitial s) :
    ((s : ℝ) + 1) / s * (initialMoment1 s X) ^ 2 ≤ initialMoment2 s X := by
  have hcoef : 0 ≤ ((s : ℝ) + 1) / s := by positivity
  have hcs := weighted_sum_sq_le_sum_weighted_sq X.weight
    (fun i => moment1 s (X.component i)) X.weight_nonneg X.weight_sum_le_one
  calc
    ((s : ℝ) + 1) / s * (initialMoment1 s X) ^ 2
        ≤ ((s : ℝ) + 1) / s *
            ∑ i, X.weight i * (moment1 s (X.component i)) ^ 2 :=
      mul_le_mul_of_nonneg_left hcs hcoef
    _ = ∑ i, X.weight i *
          (((s : ℝ) + 1) / s * (moment1 s (X.component i)) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, X.weight i * moment2 s (X.component i) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (aldousSheppMoment hs (X.component i))
        (X.weight_nonneg i)
    _ = initialMoment2 s X := rfl

/-- The induction coefficient weakens monotonically when a lower-order initial law is used in a
parent of larger order. -/
theorem initialAldousSheppForParent {r n : ℕ} (hr : 1 ≤ r) (hrn : r < n)
    (X : AbsorptionInitial r) :
    (n : ℝ) / (n - 1) * (initialMoment1 r X) ^ 2 ≤ initialMoment2 r X := by
  have hn2 : 2 ≤ n := by omega
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hrnNat : r + 1 ≤ n := by omega
  have hrnR : (r : ℝ) + 1 ≤ n := by exact_mod_cast hrnNat
  have hrn' : (r : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hcoef : (n : ℝ) / (n - 1) ≤ ((r : ℝ) + 1) / r := by
    rw [div_le_div_iff₀ hn1 hr0]
    nlinarith
  calc
    (n : ℝ) / (n - 1) * (initialMoment1 r X) ^ 2
        ≤ ((r : ℝ) + 1) / r * (initialMoment1 r X) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ ≤ initialMoment2 r X := initialAldousSheppMoment hr X

/-- The `k = 2` inequality is inherited from all deterministic starts of the same matrix. -/
theorem initialStageBound_of_components {s : ℕ} (X : AbsorptionInitial s)
    (hdet : ∀ i, SSP.K2AllStages.StageBound s
      (moment1 s (X.component i)) (moment2 s (X.component i))
      (moment3 s (X.component i))) :
    SSP.K2AllStages.StageBound s
      (initialMoment1 s X) (initialMoment2 s X) (initialMoment3 s X) := by
  unfold SSP.K2AllStages.StageBound
  simpa [initialMoment1, initialMoment2, initialMoment3,
    AbsorptionInitial.component, mul_assoc] using
    initial_mixture_bound X.model X.weight X.weight_nonneg hdet

theorem initialStageBound_one (X : AbsorptionInitial 1) :
    SSP.K2AllStages.StageBound 1
      (initialMoment1 1 X) (initialMoment2 1 X) (initialMoment3 1 X) := by
  exact initialStageBound_of_components X (fun i => stageBound_one (X.component i))

theorem initialStageBound_two (X : AbsorptionInitial 2) :
    SSP.K2AllStages.StageBound 2
      (initialMoment1 2 X) (initialMoment2 2 X) (initialMoment3 2 X) := by
  exact initialStageBound_of_components X (fun i => stageBound_two (X.component i))

theorem initialStageBound_three_of_canonical (X : AbsorptionInitial 3)
    (hcanonical : ∀ Y : AbsorptionStart 3, OrderThreeCanonicalCertificate Y) :
    SSP.K2AllStages.StageBound 3
      (initialMoment1 3 X) (initialMoment2 3 X) (initialMoment3 3 X) := by
  exact initialStageBound_of_components X
    (fun i => stageBound_three_of_canonical (X.component i) (hcanonical (X.component i)))

/-! ## The correctly typed deterministic-start induction

The proof decomposes a deterministic start at the current order.  Its two conditioned
excursions have general initial distributions on smaller state spaces.  Thus the following
heterogeneous certificate is the exact interface needed by the probabilistic construction. -/

/-- State-return data in the general transient chart.  This is the certificate type appropriate
for the two Doob-conditioned excursion laws constructed above. -/
structure TransientStateReturnData (n : ℕ) (X : TransientStart n) where
  su : ℕ
  sv : ℕ
  su_pos : 1 ≤ su
  sv_pos : 1 ≤ sv
  su_lt : su < n
  sv_lt : sv < n
  U : TransientInitial su
  V : TransientInitial sv
  x : ℝ
  p : ℝ
  q : ℝ
  x_pos : 0 < x
  p_nonneg : 0 ≤ p
  q_pos : 0 < q
  prob_sum : p + q = 1
  return_weight_pos : 0 < ∑ i, U.weight i
  moment1_decomp : transientMoment1 n X = SSP.K2AllStages.renewalM1 x
    (transientInitialMoment1 su U) (transientInitialMoment1 sv V) p q
  moment2_decomp : transientMoment2 n X = SSP.K2AllStages.renewalM2 x
    (transientInitialMoment1 su U) (transientInitialMoment1 sv V) p q
      (transientInitialMoment2 su U) (transientInitialMoment2 sv V)
  moment3_decomp : transientMoment3 n X = SSP.K2AllStages.renewalM3 x
    (transientInitialMoment1 su U) (transientInitialMoment1 sv V) p q
      (transientInitialMoment2 su U) (transientInitialMoment2 sv V)
      (transientInitialMoment3 su U) (transientInitialMoment3 sv V)

/-- The state-return construction gives the exact transient induction certificate for every
strict-contraction absorption model.  Both excursions use the `n - 1` states complementary to
the distinguished state. -/
noncomputable def concreteTransientStateReturnData {n : ℕ} (hn : 4 ≤ n)
    (X : AbsorptionStart n) : TransientStateReturnData n X.toTransient := by
  have hn2 : 2 ≤ n := by omega
  by_cases hp : 0 < returnProbability X
  · refine
      { su := n - 1
        sv := n - 1
        su_pos := by omega
        sv_pos := by omega
        su_lt := by omega
        sv_lt := by omega
        U := returnConditionedInitial X hn2 hp
        V := terminalConditionedInitial X hn2 (terminalProbability_pos X)
        x := holdingMean X
        p := returnProbability X
        q := terminalProbability X
        x_pos := holdingMean_pos X
        p_nonneg := returnProbability_nonneg X
        q_pos := terminalProbability_pos X
        prob_sum := returnProbability_add_terminalProbability X
        return_weight_pos := by
          rw [returnConditionedInitial_weight_sum X hn2 hp]
          norm_num
        moment1_decomp := ?_
        moment2_decomp := ?_
        moment3_decomp := ?_ }
    · simpa only [toTransient_moment1] using moment1_renewal_of_return_pos X hn2 hp
    · simpa only [toTransient_moment2] using moment2_renewal_of_return_pos X hn2 hp
    · simpa only [toTransient_moment3] using moment3_renewal_of_return_pos X hn2 hp
  · have hp0 : returnProbability X = 0 :=
      le_antisymm (not_lt.mp hp) (returnProbability_nonneg X)
    let U := pureTransientInitial (returnConditionedStart X ⟨0, by omega⟩)
    have hm := renewal_moments_of_return_zero X hn2 hp0 U
    refine
      { su := n - 1
        sv := n - 1
        su_pos := by omega
        sv_pos := by omega
        su_lt := by omega
        sv_lt := by omega
        U := U
        V := terminalConditionedInitial X hn2 (terminalProbability_pos X)
        x := holdingMean X
        p := returnProbability X
        q := terminalProbability X
        x_pos := holdingMean_pos X
        p_nonneg := returnProbability_nonneg X
        q_pos := terminalProbability_pos X
        prob_sum := returnProbability_add_terminalProbability X
        return_weight_pos := by
          dsimp [U]
          simp [pureTransientInitial]
        moment1_decomp := ?_
        moment2_decomp := ?_
        moment3_decomp := ?_ }
    · simpa only [toTransient_moment1] using hm.1
    · simpa only [toTransient_moment2] using hm.2.1
    · simpa only [toTransient_moment3] using hm.2.2

/-- The fully general state-return certificate.  Unlike
`concreteTransientStateReturnData`, this construction may be iterated after conditioning, since
its parent is an arbitrary finite transient substochastic model. -/
noncomputable def generalTransientStateReturnData {n : ℕ} (hn : 4 ≤ n)
    (X : TransientStart n) : TransientStateReturnData n X := by
  have hn2 : 2 ≤ n := by omega
  by_cases hp : 0 < transientReturnProbability X
  · refine
      { su := n - 1
        sv := n - 1
        su_pos := by omega
        sv_pos := by omega
        su_lt := by omega
        sv_lt := by omega
        U := transientReturnConditionedInitial X hn2 hp
        V := transientTerminalConditionedInitial X hn2 (transientTerminalProbability_pos X)
        x := transientHoldingMean X
        p := transientReturnProbability X
        q := transientTerminalProbability X
        x_pos := transientHoldingMean_pos X
        p_nonneg := transientReturnProbability_nonneg X
        q_pos := transientTerminalProbability_pos X
        prob_sum := transientReturnProbability_add_terminalProbability X
        return_weight_pos := by
          rw [transientReturnConditionedInitial_weight_sum X hn2 hp]
          norm_num
        moment1_decomp := transientMoment1_renewal_of_return_pos X hn2 hp
        moment2_decomp := transientMoment2_renewal_of_return_pos X hn2 hp
        moment3_decomp := transientMoment3_renewal_of_return_pos X hn2 hp }
  · have hp0 : transientReturnProbability X = 0 :=
      le_antisymm (not_lt.mp hp) (transientReturnProbability_nonneg X)
    let U := pureTransientInitial (transientReturnConditionedStart X ⟨0, by omega⟩)
    have hm := transient_renewal_moments_of_return_zero X hn2 hp0 U
    refine
      { su := n - 1
        sv := n - 1
        su_pos := by omega
        sv_pos := by omega
        su_lt := by omega
        sv_lt := by omega
        U := U
        V := transientTerminalConditionedInitial X hn2 (transientTerminalProbability_pos X)
        x := transientHoldingMean X
        p := transientReturnProbability X
        q := transientTerminalProbability X
        x_pos := transientHoldingMean_pos X
        p_nonneg := transientReturnProbability_nonneg X
        q_pos := transientTerminalProbability_pos X
        prob_sum := transientReturnProbability_add_terminalProbability X
        return_weight_pos := by
          dsimp [U]
          simp [pureTransientInitial]
        moment1_decomp := hm.1
        moment2_decomp := hm.2.1
        moment3_decomp := hm.2.2 }

/-- One renewal step for general transient conditioned excursions. -/
theorem transientStageBound_of_state_return {n : ℕ} (hn : 4 ≤ n)
    {X : TransientStart n} (d : TransientStateReturnData n X)
    (hU0 : SSP.K2AllStages.StageBound d.su
      (transientInitialMoment1 d.su d.U) (transientInitialMoment2 d.su d.U)
      (transientInitialMoment3 d.su d.U))
    (hV0 : SSP.K2AllStages.StageBound d.sv
      (transientInitialMoment1 d.sv d.V) (transientInitialMoment2 d.sv d.V)
      (transientInitialMoment3 d.sv d.V)) :
    SSP.K2AllStages.StageBound n
      (transientMoment1 n X) (transientMoment2 n X) (transientMoment3 n X) := by
  have hsuN : d.su ≤ n - 1 := Nat.le_sub_one_of_lt d.su_lt
  have hsvN : d.sv ≤ n - 1 := Nat.le_sub_one_of_lt d.sv_lt
  have hU := SSP.K2AllStages.stageBound_mono d.su_pos hsuN
    (transientInitialMoment1_nonneg d.U) (transientInitialMoment2_nonneg d.U)
    (transientInitialMoment3_nonneg d.U) hU0
  have hV := SSP.K2AllStages.stageBound_mono d.sv_pos hsvN
    (transientInitialMoment1_nonneg d.V) (transientInitialMoment2_nonneg d.V)
    (transientInitialMoment3_nonneg d.V) hV0
  have hUc : (n + 1) * (transientInitialMoment2 d.su d.U) ^ 2 ≤
      (n : ℝ) * transientInitialMoment1 d.su d.U * transientInitialMoment3 d.su d.U := by
    unfold SSP.K2AllStages.StageBound at hU
    have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hncast] at hU
    norm_num at hU
    nlinarith
  have hVc : (n + 1) * (transientInitialMoment2 d.sv d.V) ^ 2 ≤
      (n : ℝ) * transientInitialMoment1 d.sv d.V * transientInitialMoment3 d.sv d.V := by
    unfold SSP.K2AllStages.StageBound at hV
    have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hncast] at hV
    norm_num at hV
    nlinarith
  have hASU := transientInitialAldousSheppForParent d.su_pos d.su_lt d.U
  have hASV := transientInitialAldousSheppForParent d.sv_pos d.sv_lt d.V
  have hreturn : 0 < transientInitialMoment1 d.su d.U :=
    transientInitialMoment1_pos_of_weight_sum_pos d.U d.return_weight_pos
  rcases eq_or_lt_of_le d.p_nonneg with hp0 | hp0
  · have hq1 : d.q = 1 := by linarith [d.prob_sum]
    rcases eq_or_lt_of_le (transientInitialMoment1_nonneg d.V) with hv0 | hv0
    · have hv23 := transientInitial_higher_moments_eq_zero_of_moment1_eq_zero d.V hv0.symm
      have hstrict := SSP.K2AllStages.no_return_atom_strict n (by omega) d.x d.x_pos
      unfold SSP.K2AllStages.StageBound
      rw [d.moment1_decomp, d.moment2_decomp, d.moment3_decomp,
        ← hp0, hq1, ← hv0, hv23.1, hv23.2]
      simpa [SSP.K2AllStages.renewalM1, SSP.K2AllStages.renewalM2,
        SSP.K2AllStages.renewalM3, SSP.K2AllStages.renewalX1,
        SSP.K2AllStages.renewalX2, SSP.K2AllStages.renewalX3,
        SSP.K2AllStages.kernelM1, SSP.K2AllStages.kernelM2,
        SSP.K2AllStages.kernelM3] using le_of_lt hstrict
    · have hnr := SSP.K2AllStages.no_return_moment_inequality n hn d.x
        (transientInitialMoment1 d.sv d.V) (transientInitialMoment2 d.sv d.V)
        (transientInitialMoment3 d.sv d.V) d.x_pos hv0 hASV hVc
      unfold SSP.K2AllStages.StageBound
      rw [d.moment1_decomp, d.moment2_decomp, d.moment3_decomp, ← hp0, hq1]
      simpa [SSP.K2AllStages.renewalM1, SSP.K2AllStages.renewalM2,
        SSP.K2AllStages.renewalM3, SSP.K2AllStages.renewalX1,
        SSP.K2AllStages.renewalX2, SSP.K2AllStages.renewalX3,
        SSP.K2AllStages.kernelM1, SSP.K2AllStages.kernelM2,
        SSP.K2AllStages.kernelM3] using hnr
  · rcases eq_or_lt_of_le (transientInitialMoment1_nonneg d.V) with hv0 | hv0
    · have hv23 := transientInitial_higher_moments_eq_zero_of_moment1_eq_zero d.V hv0.symm
      have hstrict := SSP.K2AllStages.renewalGap_pos_vzero n hn d.x
        (transientInitialMoment1 d.su d.U) d.p d.q
        (transientInitialMoment2 d.su d.U) (transientInitialMoment3 d.su d.U)
        d.x_pos hreturn hp0 d.q_pos d.prob_sum hASU hUc
      unfold SSP.K2AllStages.StageBound
      rw [d.moment1_decomp, d.moment2_decomp, d.moment3_decomp, ← hv0, hv23.1, hv23.2]
      have hunscale := SSP.K2AllStages.renewalGap_unscale n d.x
        (transientInitialMoment1 d.su d.U) 0 d.p d.q
        (transientInitialMoment2 d.su d.U) 0
        (transientInitialMoment3 d.su d.U) 0 (ne_of_gt d.q_pos)
      unfold SSP.K2AllStages.gap at hunscale
      have hpos : 0 < SSP.K2AllStages.renewalGap (n : ℝ) d.x
          (transientInitialMoment1 d.su d.U) 0 d.p d.q
          (transientInitialMoment2 d.su d.U) 0
          (transientInitialMoment3 d.su d.U) 0 / d.q ^ 4 :=
        div_pos hstrict (pow_pos d.q_pos 4)
      linarith
    · have hmain := SSP.K2AllStages.renewal_moment_inequality n hn d.x
        (transientInitialMoment1 d.su d.U) (transientInitialMoment1 d.sv d.V) d.p d.q
        (transientInitialMoment2 d.su d.U) (transientInitialMoment2 d.sv d.V)
        (transientInitialMoment3 d.su d.U) (transientInitialMoment3 d.sv d.V)
        d.x_pos hreturn hv0 hp0 d.q_pos d.prob_sum hASU hASV hUc hVc
      unfold SSP.K2AllStages.StageBound
      rwa [d.moment1_decomp, d.moment2_decomp, d.moment3_decomp]

/-- A concrete strict-contraction start satisfies the stage bound as soon as the bound is known
for every deterministic component of its two conditioned lower-order excursions. -/
theorem stageBound_of_conditioned_excursions {n : ℕ} (hn : 4 ≤ n)
    (X : AbsorptionStart n)
    (hlower : ∀ m, m < n → ∀ Y : TransientStart m,
      SSP.K2AllStages.StageBound m
        (transientMoment1 m Y) (transientMoment2 m Y) (transientMoment3 m Y)) :
    SSP.K2AllStages.StageBound n (moment1 n X) (moment2 n X) (moment3 n X) := by
  let d := concreteTransientStateReturnData hn X
  have hU : SSP.K2AllStages.StageBound d.su
      (transientInitialMoment1 d.su d.U) (transientInitialMoment2 d.su d.U)
      (transientInitialMoment3 d.su d.U) := by
    apply transientInitialStageBound_of_components
    intro i
    exact hlower d.su d.su_lt (d.U.component i)
  have hV : SSP.K2AllStages.StageBound d.sv
      (transientInitialMoment1 d.sv d.V) (transientInitialMoment2 d.sv d.V)
      (transientInitialMoment3 d.sv d.V) := by
    apply transientInitialStageBound_of_components
    intro i
    exact hlower d.sv d.sv_lt (d.V.component i)
  simpa only [toTransient_moment1, toTransient_moment2, toTransient_moment3] using
    transientStageBound_of_state_return hn d hU hV

/-- Strong induction entirely in the general transient chart. -/
theorem all_transient_starts_of_state_return
    (hcanonical : ∀ Y : TransientStart 3, TransientOrderThreeCanonicalCertificate Y)
    (hreturn : ∀ n, 4 ≤ n → ∀ X : TransientStart n, TransientStateReturnData n X) :
    ∀ n, 1 ≤ n → ∀ X : TransientStart n,
      SSP.K2AllStages.StageBound n
        (transientMoment1 n X) (transientMoment2 n X) (transientMoment3 n X) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hnpos X
      by_cases hn3 : n ≤ 3
      · have hs : n = 1 ∨ n = 2 ∨ n = 3 := by omega
        rcases hs with rfl | rfl | rfl
        · exact transientStageBound_one X
        · exact transientStageBound_two X
        · exact transientStageBound_three_of_canonical X (hcanonical X)
      · have hn4 : 4 ≤ n := by omega
        let d := hreturn n hn4 X
        have hU : SSP.K2AllStages.StageBound d.su
            (transientInitialMoment1 d.su d.U) (transientInitialMoment2 d.su d.U)
            (transientInitialMoment3 d.su d.U) := by
          apply transientInitialStageBound_of_components
          intro i
          exact ih d.su d.su_lt d.su_pos (d.U.component i)
        have hV : SSP.K2AllStages.StageBound d.sv
            (transientInitialMoment1 d.sv d.V) (transientInitialMoment2 d.sv d.V)
            (transientInitialMoment3 d.sv d.V) := by
          apply transientInitialStageBound_of_components
          intro i
          exact ih d.sv d.sv_lt d.sv_pos (d.V.component i)
        exact transientStageBound_of_state_return hn4 d hU hV

theorem all_transient_initial_laws_of_state_return
    (hcanonical : ∀ Y : TransientStart 3, TransientOrderThreeCanonicalCertificate Y)
    (hreturn : ∀ n, 4 ≤ n → ∀ X : TransientStart n, TransientStateReturnData n X)
    {s : ℕ} (hs : 1 ≤ s) (X : TransientInitial s) :
    SSP.K2AllStages.StageBound s
      (transientInitialMoment1 s X) (transientInitialMoment2 s X)
      (transientInitialMoment3 s X) := by
  apply transientInitialStageBound_of_components
  intro i
  exact all_transient_starts_of_state_return hcanonical hreturn s hs (X.component i)

/-- The state-return hypothesis in the abstract transient induction is discharged by the
concrete deleted-chain/Doob-transform construction. -/
theorem all_transient_starts
    (hcanonical : ∀ Y : TransientStart 3, TransientOrderThreeCanonicalCertificate Y) :
    ∀ n, 1 ≤ n → ∀ X : TransientStart n,
      SSP.K2AllStages.StageBound n
        (transientMoment1 n X) (transientMoment2 n X) (transientMoment3 n X) := by
  exact all_transient_starts_of_state_return hcanonical
    (fun n hn X => generalTransientStateReturnData hn X)

theorem all_transient_initial_laws
    (hcanonical : ∀ Y : TransientStart 3, TransientOrderThreeCanonicalCertificate Y)
    {s : ℕ} (hs : 1 ≤ s) (X : TransientInitial s) :
    SSP.K2AllStages.StageBound s
      (transientInitialMoment1 s X) (transientInitialMoment2 s X)
      (transientInitialMoment3 s X) := by
  exact all_transient_initial_laws_of_state_return hcanonical
    (fun n hn Y => generalTransientStateReturnData hn Y) hs X

/-- The complete induction step specialized back to the original strict-contraction model. -/
theorem all_absorption_starts
    (hcanonical : ∀ Y : TransientStart 3, TransientOrderThreeCanonicalCertificate Y)
    {s : ℕ} (hs : 1 ≤ s) (X : AbsorptionStart s) :
    SSP.K2AllStages.StageBound s (moment1 s X) (moment2 s X) (moment3 s X) := by
  simpa only [toTransient_moment1, toTransient_moment2, toTransient_moment3] using
    all_transient_starts hcanonical s hs X.toTransient

/-- The all-stage bound for an arbitrary subprobability initial distribution; missing mass is
the permitted atom at zero. -/
theorem all_absorption_initial_laws
    (hcanonical : ∀ Y : TransientStart 3, TransientOrderThreeCanonicalCertificate Y)
    {s : ℕ} (hs : 1 ≤ s) (X : AbsorptionInitial s) :
    SSP.K2AllStages.StageBound s
      (initialMoment1 s X) (initialMoment2 s X) (initialMoment3 s X) := by
  apply initialStageBound_of_components
  intro i
  exact all_absorption_starts hcanonical hs (X.component i)

/-- Concrete resolvent form of the all-stage `k = 2` inequality, now with the recursive
state-return hypothesis completely discharged. -/
theorem all_initial_resolvent_bound
    (hcanonical : ∀ Y : TransientStart 3, TransientOrderThreeCanonicalCertificate Y)
    {s : ℕ} (hs : 1 ≤ s) (X : AbsorptionInitial s) :
    ((s : ℝ) + 2) *
        (∑ i, X.weight i *
          (2 * ((1 - X.model.Q)⁻¹.mulVec ((1 - X.model.Q)⁻¹.mulVec
            (fun _ => (1 : ℝ)))) i)) ^ 2
      ≤ ((s : ℝ) + 1) *
        ((∑ i, X.weight i *
          ((1 - X.model.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) i) *
        (∑ i, X.weight i *
          (6 * ((1 - X.model.Q)⁻¹.mulVec ((1 - X.model.Q)⁻¹.mulVec
            ((1 - X.model.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i))) := by
  have h := all_absorption_initial_laws hcanonical hs X
  unfold SSP.K2AllStages.StageBound at h
  simpa [initialMoment1, initialMoment2, initialMoment3,
    AbsorptionInitial.component, withStart, moment1_eq, moment2_eq, moment3_eq,
    mul_assoc] using h

/-- End-to-end `k = 2` theorem stated with exactly the cited order-three representation theorem
as input. -/
theorem k2_all_stages_of_order_three_representation
    (hrep : OrderThreeCanonicalRepresentationTheorem)
    {s : ℕ} (hs : 1 ≤ s) (X : AbsorptionInitial s) :
    SSP.K2AllStages.StageBound s
      (initialMoment1 s X) (initialMoment2 s X) (initialMoment3 s X) := by
  apply all_absorption_initial_laws (fun Y => Classical.choice (hrep Y)) hs X

/-- Resolvent form of `k2_all_stages_of_order_three_representation`. -/
theorem k2_all_stages_resolvent_of_order_three_representation
    (hrep : OrderThreeCanonicalRepresentationTheorem)
    {s : ℕ} (hs : 1 ≤ s) (X : AbsorptionInitial s) :
    ((s : ℝ) + 2) *
        (∑ i, X.weight i *
          (2 * ((1 - X.model.Q)⁻¹.mulVec ((1 - X.model.Q)⁻¹.mulVec
            (fun _ => (1 : ℝ)))) i)) ^ 2
      ≤ ((s : ℝ) + 1) *
        ((∑ i, X.weight i *
          ((1 - X.model.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) i) *
        (∑ i, X.weight i *
          (6 * ((1 - X.model.Q)⁻¹.mulVec ((1 - X.model.Q)⁻¹.mulVec
            ((1 - X.model.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i))) := by
  exact all_initial_resolvent_bound (fun Y => Classical.choice (hrep Y)) hs X

/-- The standard similarity formulation of He--Zhang implies the moment formulation used by
the induction. -/
theorem orderThreeCanonicalRepresentation_of_heZhang
    (hrep : HeZhangOrderThreeRepresentationTheorem) :
    OrderThreeCanonicalRepresentationTheorem := by
  intro X
  exact ⟨canonicalCertificateOfSimilarity X (Classical.choice (hrep X))⟩

/-- The all-stage theorem for the full algebraic class of finite transient substochastic
matrices.  Unlike `AbsorptionStart`, this class permits rows of sum one and therefore contains
the serial Erlang chain on the sharp boundary. -/
theorem k2_all_stages_transient_of_heZhang
    (hrep : HeZhangOrderThreeRepresentationTheorem)
    {s : ℕ} (hs : 1 ≤ s) (X : TransientStart s) :
    SSP.K2AllStages.StageBound s
      (transientMoment1 s X) (transientMoment2 s X) (transientMoment3 s X) := by
  exact all_transient_starts
    (fun Y => canonicalCertificateOfSimilarity Y (Classical.choice (hrep Y))) s hs X

/-- The preceding theorem for a subprobability initial row; its missing mass is an atom at
zero. -/
theorem k2_all_stages_transient_initial_of_heZhang
    (hrep : HeZhangOrderThreeRepresentationTheorem)
    {s : ℕ} (hs : 1 ≤ s) (X : TransientInitial s) :
    SSP.K2AllStages.StageBound s
      (transientInitialMoment1 s X) (transientInitialMoment2 s X)
      (transientInitialMoment3 s X) := by
  exact all_transient_initial_laws
    (fun Y => canonicalCertificateOfSimilarity Y (Classical.choice (hrep Y))) hs X

/-- Resolvent form on the full transient class. -/
theorem k2_all_stages_transient_resolvent_of_heZhang
    (hrep : HeZhangOrderThreeRepresentationTheorem)
    {s : ℕ} (hs : 1 ≤ s) (X : TransientStart s) :
    ((s : ℝ) + 2) *
        (2 * ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
          (fun _ => (1 : ℝ)))) X.i) ^ 2
      ≤ ((s : ℝ) + 1) *
        (((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i *
          (6 * ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
            ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) X.i)) := by
  simpa [SSP.K2AllStages.StageBound, transientMoment1, transientMoment2,
    transientMoment3, mul_assoc] using
      (k2_all_stages_transient_of_heZhang hrep hs X)

/-- Sharpness of the all-stage constant: an atom of mass `1 - w` at zero mixed with an
`s`-stage Erlang law of stage mean `θ` makes the final inequality an equality.  The identity is
algebraic; the probabilistic parameter restrictions `0 ≤ w ≤ 1` and `0 < θ` may therefore be
imposed by callers without changing the proof. -/
theorem k2_erlang_mixture_equality (s : ℕ) (w θ : ℝ) :
    ((s : ℝ) + 2) * (SSP.K2AllStages.erlangMixMoment s w θ 2) ^ 2 =
      ((s : ℝ) + 1) *
        (SSP.K2AllStages.erlangMixMoment s w θ 1 *
          SSP.K2AllStages.erlangMixMoment s w θ 3) := by
  have h := SSP.K2AllStages.erlang_mixture_sharp s w θ
  unfold SSP.K2AllStages.gap at h
  linarith

/-- End-to-end all-stage theorem from the standard He--Zhang similarity statement. -/
theorem k2_all_stages_of_heZhang
    (hrep : HeZhangOrderThreeRepresentationTheorem)
    {s : ℕ} (hs : 1 ≤ s) (X : AbsorptionInitial s) :
    SSP.K2AllStages.StageBound s
      (initialMoment1 s X) (initialMoment2 s X) (initialMoment3 s X) := by
  exact k2_all_stages_of_order_three_representation
    (orderThreeCanonicalRepresentation_of_heZhang hrep) hs X

/-- The original deterministic-start formulation of the all-stage theorem. -/
theorem k2_all_stages_deterministic_of_heZhang
    (hrep : HeZhangOrderThreeRepresentationTheorem)
    {s : ℕ} (hs : 1 ≤ s) (X : AbsorptionStart s) :
    SSP.K2AllStages.StageBound s (moment1 s X) (moment2 s X) (moment3 s X) := by
  exact all_absorption_starts
    (fun Y => canonicalCertificateOfSimilarity Y (Classical.choice (hrep Y))) hs X

/-- The original deterministic-start inequality, written entirely in resolvent coordinates. -/
theorem k2_all_stages_deterministic_resolvent_of_heZhang
    (hrep : HeZhangOrderThreeRepresentationTheorem)
    {s : ℕ} (hs : 1 ≤ s) (X : AbsorptionStart s) :
    ((s : ℝ) + 2) *
        (2 * ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
          (fun _ => (1 : ℝ)))) X.i) ^ 2
      ≤ ((s : ℝ) + 1) *
        (((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) X.i *
          (6 * ((1 - X.Q)⁻¹.mulVec ((1 - X.Q)⁻¹.mulVec
            ((1 - X.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) X.i)) := by
  simpa [mul_assoc] using
    (resolvent_bound_of_stageBound X
      (k2_all_stages_deterministic_of_heZhang hrep hs X))

/-- Concrete resolvent inequality obtained from the standard He--Zhang similarity statement. -/
theorem k2_all_stages_resolvent_of_heZhang
    (hrep : HeZhangOrderThreeRepresentationTheorem)
    {s : ℕ} (hs : 1 ≤ s) (X : AbsorptionInitial s) :
    ((s : ℝ) + 2) *
        (∑ i, X.weight i *
          (2 * ((1 - X.model.Q)⁻¹.mulVec ((1 - X.model.Q)⁻¹.mulVec
            (fun _ => (1 : ℝ)))) i)) ^ 2
      ≤ ((s : ℝ) + 1) *
        ((∑ i, X.weight i *
          ((1 - X.model.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) i) *
        (∑ i, X.weight i *
          (6 * ((1 - X.model.Q)⁻¹.mulVec ((1 - X.model.Q)⁻¹.mulVec
            ((1 - X.model.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i))) := by
  exact k2_all_stages_resolvent_of_order_three_representation
    (orderThreeCanonicalRepresentation_of_heZhang hrep) hs X

/-- State-return data for a deterministic order-`n` law whose two lower-order excursion laws
have subprobability initial vectors. -/
structure DeterministicStateReturnData (n : ℕ) (X : AbsorptionStart n) where
  su : ℕ
  sv : ℕ
  su_pos : 1 ≤ su
  sv_pos : 1 ≤ sv
  su_lt : su < n
  sv_lt : sv < n
  U : AbsorptionInitial su
  V : AbsorptionInitial sv
  x : ℝ
  p : ℝ
  q : ℝ
  x_pos : 0 < x
  p_nonneg : 0 ≤ p
  q_pos : 0 < q
  prob_sum : p + q = 1
  return_weight_pos : 0 < ∑ i, U.weight i
  moment1_decomp : moment1 n X = SSP.K2AllStages.renewalM1 x
    (initialMoment1 su U) (initialMoment1 sv V) p q
  moment2_decomp : moment2 n X = SSP.K2AllStages.renewalM2 x
    (initialMoment1 su U) (initialMoment1 sv V) p q
      (initialMoment2 su U) (initialMoment2 sv V)
  moment3_decomp : moment3 n X = SSP.K2AllStages.renewalM3 x
    (initialMoment1 su U) (initialMoment1 sv V) p q
      (initialMoment2 su U) (initialMoment2 sv V)
      (initialMoment3 su U) (initialMoment3 sv V)

/-- One heterogeneous renewal step.  The lower-order inequalities are supplied for the mixed
excursion laws; all positivity, zero-moment, and Aldous--Shepp side conditions are discharged
from their concrete definitions. -/
theorem stageBound_of_deterministic_state_return {n : ℕ} (hn : 4 ≤ n)
    {X : AbsorptionStart n} (d : DeterministicStateReturnData n X)
    (hU0 : SSP.K2AllStages.StageBound d.su
      (initialMoment1 d.su d.U) (initialMoment2 d.su d.U) (initialMoment3 d.su d.U))
    (hV0 : SSP.K2AllStages.StageBound d.sv
      (initialMoment1 d.sv d.V) (initialMoment2 d.sv d.V) (initialMoment3 d.sv d.V)) :
    SSP.K2AllStages.StageBound n (moment1 n X) (moment2 n X) (moment3 n X) := by
  have hsuN : d.su ≤ n - 1 := Nat.le_sub_one_of_lt d.su_lt
  have hsvN : d.sv ≤ n - 1 := Nat.le_sub_one_of_lt d.sv_lt
  have hU := SSP.K2AllStages.stageBound_mono d.su_pos hsuN
    (initialMoment1_nonneg d.U) (initialMoment2_nonneg d.U)
    (initialMoment3_nonneg d.U) hU0
  have hV := SSP.K2AllStages.stageBound_mono d.sv_pos hsvN
    (initialMoment1_nonneg d.V) (initialMoment2_nonneg d.V)
    (initialMoment3_nonneg d.V) hV0
  have hUc : (n + 1) * (initialMoment2 d.su d.U) ^ 2
      ≤ (n : ℝ) * initialMoment1 d.su d.U * initialMoment3 d.su d.U := by
    unfold SSP.K2AllStages.StageBound at hU
    have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hncast] at hU
    norm_num at hU
    nlinarith
  have hVc : (n + 1) * (initialMoment2 d.sv d.V) ^ 2
      ≤ (n : ℝ) * initialMoment1 d.sv d.V * initialMoment3 d.sv d.V := by
    unfold SSP.K2AllStages.StageBound at hV
    have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hncast] at hV
    norm_num at hV
    nlinarith
  have hASU := initialAldousSheppForParent d.su_pos d.su_lt d.U
  have hASV := initialAldousSheppForParent d.sv_pos d.sv_lt d.V
  have hreturn : 0 < initialMoment1 d.su d.U :=
    initialMoment1_pos_of_weight_sum_pos d.U d.return_weight_pos
  rcases eq_or_lt_of_le d.p_nonneg with hp0 | hp0
  · have hq1 : d.q = 1 := by linarith [d.prob_sum]
    rcases eq_or_lt_of_le (initialMoment1_nonneg d.V) with hv0 | hv0
    · have hv23 := initial_higher_moments_eq_zero_of_moment1_eq_zero d.V hv0.symm
      have hstrict := SSP.K2AllStages.no_return_atom_strict n (by omega) d.x d.x_pos
      unfold SSP.K2AllStages.StageBound
      rw [d.moment1_decomp, d.moment2_decomp, d.moment3_decomp,
        ← hp0, hq1, ← hv0, hv23.1, hv23.2]
      simpa [SSP.K2AllStages.renewalM1, SSP.K2AllStages.renewalM2,
        SSP.K2AllStages.renewalM3, SSP.K2AllStages.renewalX1,
        SSP.K2AllStages.renewalX2, SSP.K2AllStages.renewalX3,
        SSP.K2AllStages.kernelM1, SSP.K2AllStages.kernelM2,
        SSP.K2AllStages.kernelM3] using le_of_lt hstrict
    · have hnr := SSP.K2AllStages.no_return_moment_inequality n hn d.x
        (initialMoment1 d.sv d.V) (initialMoment2 d.sv d.V)
        (initialMoment3 d.sv d.V) d.x_pos hv0 hASV hVc
      unfold SSP.K2AllStages.StageBound
      rw [d.moment1_decomp, d.moment2_decomp, d.moment3_decomp, ← hp0, hq1]
      simpa [SSP.K2AllStages.renewalM1, SSP.K2AllStages.renewalM2,
        SSP.K2AllStages.renewalM3, SSP.K2AllStages.renewalX1,
        SSP.K2AllStages.renewalX2, SSP.K2AllStages.renewalX3,
        SSP.K2AllStages.kernelM1, SSP.K2AllStages.kernelM2,
        SSP.K2AllStages.kernelM3] using hnr
  · rcases eq_or_lt_of_le (initialMoment1_nonneg d.V) with hv0 | hv0
    · have hv23 := initial_higher_moments_eq_zero_of_moment1_eq_zero d.V hv0.symm
      have hstrict := SSP.K2AllStages.renewalGap_pos_vzero n hn d.x
        (initialMoment1 d.su d.U) d.p d.q (initialMoment2 d.su d.U)
        (initialMoment3 d.su d.U) d.x_pos hreturn hp0 d.q_pos d.prob_sum hASU hUc
      unfold SSP.K2AllStages.StageBound
      rw [d.moment1_decomp, d.moment2_decomp, d.moment3_decomp, ← hv0, hv23.1, hv23.2]
      have hunscale := SSP.K2AllStages.renewalGap_unscale n d.x
        (initialMoment1 d.su d.U) 0 d.p d.q (initialMoment2 d.su d.U) 0
        (initialMoment3 d.su d.U) 0 (ne_of_gt d.q_pos)
      unfold SSP.K2AllStages.gap at hunscale
      have hpos : 0 < SSP.K2AllStages.renewalGap (n : ℝ) d.x
          (initialMoment1 d.su d.U) 0 d.p d.q (initialMoment2 d.su d.U) 0
          (initialMoment3 d.su d.U) 0 / d.q ^ 4 :=
        div_pos hstrict (pow_pos d.q_pos 4)
      linarith
    · have hmain := SSP.K2AllStages.renewal_moment_inequality n hn d.x
        (initialMoment1 d.su d.U) (initialMoment1 d.sv d.V) d.p d.q
        (initialMoment2 d.su d.U) (initialMoment2 d.sv d.V)
        (initialMoment3 d.su d.U) (initialMoment3 d.sv d.V)
        d.x_pos hreturn hv0 hp0 d.q_pos d.prob_sum hASU hASV hUc hVc
      unfold SSP.K2AllStages.StageBound
      rwa [d.moment1_decomp, d.moment2_decomp, d.moment3_decomp]

/-- Strong induction for deterministic starts using mixed lower-order excursion laws.  This is
the exact logical form of the argument in the paper. -/
theorem all_deterministic_starts_of_state_return
    (hcanonical : ∀ Y : AbsorptionStart 3, OrderThreeCanonicalCertificate Y)
    (hreturn : ∀ n, 4 ≤ n → ∀ X : AbsorptionStart n,
      DeterministicStateReturnData n X) :
    ∀ n, 1 ≤ n → ∀ X : AbsorptionStart n,
      SSP.K2AllStages.StageBound n (moment1 n X) (moment2 n X) (moment3 n X) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hnpos X
      by_cases hn3 : n ≤ 3
      · have hs : n = 1 ∨ n = 2 ∨ n = 3 := by omega
        rcases hs with rfl | rfl | rfl
        · exact stageBound_one X
        · exact stageBound_two X
        · exact stageBound_three_of_canonical X (hcanonical X)
      · have hn4 : 4 ≤ n := by omega
        let d := hreturn n hn4 X
        have hU : SSP.K2AllStages.StageBound d.su
            (initialMoment1 d.su d.U) (initialMoment2 d.su d.U)
            (initialMoment3 d.su d.U) := by
          apply initialStageBound_of_components
          intro i
          exact ih d.su d.su_lt d.su_pos (d.U.component i)
        have hV : SSP.K2AllStages.StageBound d.sv
            (initialMoment1 d.sv d.V) (initialMoment2 d.sv d.V)
            (initialMoment3 d.sv d.V) := by
          apply initialStageBound_of_components
          intro i
          exact ih d.sv d.sv_lt d.sv_pos (d.V.component i)
        exact stageBound_of_deterministic_state_return hn4 d hU hV

/-- Final arbitrary-initial-distribution inequality obtained after the deterministic induction. -/
theorem all_initial_laws_of_deterministic_state_return
    (hcanonical : ∀ Y : AbsorptionStart 3, OrderThreeCanonicalCertificate Y)
    (hreturn : ∀ n, 4 ≤ n → ∀ X : AbsorptionStart n,
      DeterministicStateReturnData n X)
    {s : ℕ} (hs : 1 ≤ s) (X : AbsorptionInitial s) :
    SSP.K2AllStages.StageBound s
      (initialMoment1 s X) (initialMoment2 s X) (initialMoment3 s X) := by
  apply initialStageBound_of_components
  intro i
  exact all_deterministic_starts_of_state_return hcanonical hreturn s hs (X.component i)

/-- Fully concrete resolvent statement obtained from the correctly typed deterministic
state-return induction, followed by the final mixture step. -/
theorem all_initial_resolvent_bound_of_deterministic_state_return
    (hcanonical : ∀ Y : AbsorptionStart 3, OrderThreeCanonicalCertificate Y)
    (hreturn : ∀ n, 4 ≤ n → ∀ X : AbsorptionStart n,
      DeterministicStateReturnData n X)
    {s : ℕ} (hs : 1 ≤ s) (X : AbsorptionInitial s) :
    ((s : ℝ) + 2) *
        (∑ i, X.weight i *
          (2 * ((1 - X.model.Q)⁻¹.mulVec ((1 - X.model.Q)⁻¹.mulVec
            (fun _ => (1 : ℝ)))) i)) ^ 2
      ≤ ((s : ℝ) + 1) *
        ((∑ i, X.weight i *
          ((1 - X.model.Q)⁻¹.mulVec (fun _ => (1 : ℝ))) i) *
        (∑ i, X.weight i *
          (6 * ((1 - X.model.Q)⁻¹.mulVec ((1 - X.model.Q)⁻¹.mulVec
            ((1 - X.model.Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i))) := by
  have h := all_initial_laws_of_deterministic_state_return hcanonical hreturn hs X
  unfold SSP.K2AllStages.StageBound at h
  simpa [initialMoment1, initialMoment2, initialMoment3,
    AbsorptionInitial.component, withStart, moment1_eq, moment2_eq, moment3_eq,
    mul_assoc] using h

/-- Embed a deterministic start as a general initial law. -/
noncomputable def pureInitial {s : ℕ} (X : AbsorptionStart s) : AbsorptionInitial s where
  model := X
  weight := fun j => if j = X.i then 1 else 0
  weight_nonneg := by intro j; split_ifs <;> positivity
  weight_sum_le_one := by simp

@[simp] theorem pureInitial_moment1 {s : ℕ} (X : AbsorptionStart s) :
    initialMoment1 s (pureInitial X) = moment1 s X := by
  simp [initialMoment1, pureInitial, AbsorptionInitial.component, withStart]

@[simp] theorem pureInitial_moment2 {s : ℕ} (X : AbsorptionStart s) :
    initialMoment2 s (pureInitial X) = moment2 s X := by
  simp [initialMoment2, pureInitial, AbsorptionInitial.component, withStart]

@[simp] theorem pureInitial_moment3 {s : ℕ} (X : AbsorptionStart s) :
    initialMoment3 s (pureInitial X) = moment3 s X := by
  simp [initialMoment3, pureInitial, AbsorptionInitial.component, withStart]

end SSP.K2Concrete
