import SSPLean.MatrixMomentReduction

/-! Duhamel's formula for the actual exponential of an upper triangular block matrix. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 12
open scoped Matrix.Norms.Operator
open Matrix NormedSpace MeasureTheory

namespace SSP.BlockTriangular

abbrev Mat (n : Type*) := Matrix n n ℝ

noncomputable local instance (n : Type*) [Fintype n] : AddCommGroup (Mat n) := Matrix.linftyOpNormedAddCommGroup.toAddCommGroup
noncomputable local instance (n : Type*) [Fintype n] : TopologicalSpace (Mat n) :=
  Matrix.linftyOpNormedAddCommGroup.toUniformSpace.toTopologicalSpace
noncomputable local instance (n : Type*) [Fintype n] : Module ℝ (Mat n) := Matrix.linftyOpNormedSpace.toModule
noncomputable local instance (n : Type*) [Fintype n] : NormedAddCommGroup (Mat n) := Matrix.linftyOpNormedAddCommGroup
noncomputable local instance (n : Type*) [Fintype n] : SeminormedAddCommGroup (Mat n) := Matrix.linftyOpSeminormedAddCommGroup
noncomputable local instance (n : Type*) [Fintype n] : NormedSpace ℝ (Mat n) := Matrix.linftyOpNormedSpace

variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

noncomputable def entryCLM (i j : n) : Mat n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] theorem entryCLM_apply (i j : n) (A : Mat n) : entryCLM i j A = A i j := rfl

noncomputable def expEntry (A : Mat n) (i j : n) (t : ℝ) : ℝ :=
  NormedSpace.exp (t • A) i j

theorem expEntry_hasDerivAt (A : Mat n) (i j : n) (t : ℝ) :
    HasDerivAt (expEntry A i j) ((NormedSpace.exp (t • A)*A) i j) t := by
  convert (entryCLM i j).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) A t) using 1 <;> rfl

theorem expEntry_continuous (A : Mat n) (i j : n) : Continuous (expEntry A i j) :=
  continuous_iff_continuousAt.mpr fun t => (expEntry_hasDerivAt A i j t).continuousAt

theorem expEntry_series (A : Mat n) (i j : n) (t : ℝ) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹*t^k)*(A^k) i j) (expEntry A i j t) := by
  have hs : Summable (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • (t • A)^k) :=
    (NormedSpace.expSeries_summable (𝕂 := ℝ) (t • A)).congr fun k => by
      rw [NormedSpace.expSeries_apply_eq]
  have hm := (entryCLM i j).hasSum hs.hasSum
  rw [← congrFun (NormedSpace.exp_eq_tsum ℝ) (t • A)] at hm
  simpa only [smul_pow,map_smul,smul_smul,smul_eq_mul,entryCLM_apply,
    Matrix.smul_apply,expEntry] using hm

theorem block_powers (B : Mat n) (C : Matrix n m ℝ) (E : Mat m) (k : ℕ) :
    ∃ U : Matrix n m ℝ, (fromBlocks B C 0 E)^k = fromBlocks (B^k) U 0 (E^k) := by
  induction k with
  | zero => exact ⟨0,by simp [Matrix.fromBlocks_one]⟩
  | succ k ih =>
    obtain ⟨U,hU⟩ := ih
    refine ⟨B^k*C+U*E,?_⟩
    rw [pow_succ,hU,fromBlocks_multiply]
    simp [pow_succ]

theorem block_exp_inl_inl (B : Mat n) (C : Matrix n m ℝ) (E : Mat m)
    (i j : n) (t : ℝ) :
    expEntry (fromBlocks B C 0 E) (Sum.inl i) (Sum.inl j) t = expEntry B i j t := by
  apply HasSum.unique (expEntry_series _ _ _ t)
  convert expEntry_series B i j t using 1
  funext k
  obtain ⟨U,hU⟩ := block_powers B C E k
  rw [hU,fromBlocks_apply₁₁]

theorem block_exp_inr_inr (B : Mat n) (C : Matrix n m ℝ) (E : Mat m)
    (i j : m) (t : ℝ) :
    expEntry (fromBlocks B C 0 E) (Sum.inr i) (Sum.inr j) t = expEntry E i j t := by
  apply HasSum.unique (expEntry_series _ _ _ t)
  convert expEntry_series E i j t using 1
  funext k
  obtain ⟨U,hU⟩ := block_powers B C E k
  rw [hU,fromBlocks_apply₂₂]

theorem block_exp_inr_inl (B : Mat n) (C : Matrix n m ℝ) (E : Mat m)
    (i : m) (j : n) (t : ℝ) :
    expEntry (fromBlocks B C 0 E) (Sum.inr i) (Sum.inl j) t = 0 := by
  apply HasSum.unique (expEntry_series _ _ _ t)
  convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) using 1
  funext k
  obtain ⟨U,hU⟩ := block_powers B C E k
  simp [hU]

theorem diagonal_exp (B : Mat n) (E : Mat m) (t : ℝ) :
    NormedSpace.exp (t • fromBlocks B 0 0 E) =
      fromBlocks (NormedSpace.exp (t • B)) 0 0 (NormedSpace.exp (t • E)) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => exact block_exp_inl_inl B 0 E i j t
    | inr j =>
      have hs := expEntry_series (fromBlocks B (0 : Matrix n m ℝ) 0 E) (Sum.inl i) (Sum.inr j) t
      have hz : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹*t^k)*
          ((fromBlocks B (0 : Matrix n m ℝ) 0 E)^k) (Sum.inl i) (Sum.inr j)) 0 := by
        simp [Matrix.fromBlocks_diagonal_pow, hasSum_zero]
      exact hs.unique hz
  | inr i =>
    cases j with
    | inl j => exact block_exp_inr_inl B 0 E i j t
    | inr j => exact block_exp_inr_inr B 0 E i j t

/-- Duhamel's variation-of-constants identity, before extracting blocks. -/
theorem exp_duhamel (A D : Mat n) (t : ℝ) :
    NormedSpace.exp (t • A)-NormedSpace.exp (t • D) =
      ∫ x in (0 : ℝ)..t,
        NormedSpace.exp ((t-x) • D)*(A-D)*NormedSpace.exp (x • A) := by
  let F := fun x : ℝ => NormedSpace.exp ((t-x) • D)*NormedSpace.exp (x • A)
  let G := fun x : ℝ => NormedSpace.exp ((t-x) • D)*(A-D)*NormedSpace.exp (x • A)
  have hd : ∀ x, HasDerivAt F (G x) x := by
    intro x
    have houter : HasDerivAt (fun y : ℝ => NormedSpace.exp (y • D))
        (NormedSpace.exp ((t-x) • D)*D) (t-x) := by
      convert hasDerivAt_exp_smul_const (𝕂 := ℝ) D (t-x) using 1
    have hinner : HasDerivAt (fun y : ℝ => t-y) (-1) x := by
      convert (hasDerivAt_const x t).sub (hasDerivAt_id x) using 1 <;> first | rfl | norm_num
    have hleft := houter.scomp x hinner
    have hh := hleft.mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) A x)
    convert hh using 1 <;> try rfl
    dsimp [G]
    simp only [neg_smul,one_smul,neg_mul,mul_sub,mul_assoc]
    have hcomm : NormedSpace.exp (x • A)*A = A*NormedSpace.exp (x • A) := by
      exact ((Commute.refl A).smul_right x).exp_right.eq.symm
    rw [hcomm]
    noncomm_ring
  have hint : IntervalIntegrable G volume 0 t := by
    apply Continuous.intervalIntegrable
    dsimp [G]
    exact ((NormedSpace.exp_continuous.comp (by fun_prop)).mul continuous_const).mul
      (NormedSpace.exp_continuous.comp (by fun_prop))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hint
  simpa [F,G] using h.symm

/-- The upper-right block of the exponential is the sum of entrywise convolutions. -/
theorem block_exp_inl_inr (B : Mat n) (C : Matrix n m ℝ) (E : Mat m)
    (i : n) (j : m) (t : ℝ) :
    expEntry (fromBlocks B C 0 E) (Sum.inl i) (Sum.inr j) t =
      ∑ a, ∑ b, C a b*(∫ x in (0 : ℝ)..t, expEntry B i a (t-x)*expEntry E b j x) := by
  let A := fromBlocks B C 0 E
  let D := fromBlocks B (0 : Matrix n m ℝ) 0 E
  have h := congrArg (fun M : Mat (n ⊕ m) => M (Sum.inl i) (Sum.inr j)) (exp_duhamel A D t)
  have hmap : (∫ x in (0 : ℝ)..t,
      NormedSpace.exp ((t-x) • D)*(A-D)*NormedSpace.exp (x • A)) (Sum.inl i) (Sum.inr j) =
      ∫ x in (0 : ℝ)..t,
        (NormedSpace.exp ((t-x) • D)*(A-D)*NormedSpace.exp (x • A)) (Sum.inl i) (Sum.inr j) := by
    exact (entryCLM (Sum.inl i) (Sum.inr j)).intervalIntegral_comp_comm
      (show IntervalIntegrable (fun x : ℝ => NormedSpace.exp ((t-x) • D)*(A-D)*NormedSpace.exp (x • A)) volume 0 t from
        Continuous.intervalIntegrable (by fun_prop) 0 t) |>.symm
  rw [hmap] at h
  have hAD : A-D = fromBlocks (0 : Mat n) C 0 (0 : Mat m) := by
    dsimp [A,D]; ext u v; cases u <;> cases v <;> simp
  have hentry : ∀ x : ℝ,
      (NormedSpace.exp ((t-x) • D)*(A-D)*NormedSpace.exp (x • A)) (Sum.inl i) (Sum.inr j) =
      ∑ a, ∑ b, C a b*(expEntry B i a (t-x)*expEntry E b j x) := by
    intro x
    rw [hAD,diagonal_exp,fromBlocks_multiply]
    simp only [Matrix.mul_zero,Matrix.zero_mul,add_zero]
    simp only [Matrix.mul_apply,Fintype.sum_sum_type,fromBlocks_apply₁₁,
      fromBlocks_apply₁₂,Matrix.zero_apply,
      zero_mul,Finset.sum_const_zero,zero_add]
    change (∑ b, (∑ a, expEntry B i a (t-x)*C a b)*expEntry A (Sum.inr b) (Sum.inr j) x) = _
    simp only [A,block_exp_inr_inr,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp only [Matrix.sub_apply] at h
  have hDzero : NormedSpace.exp (t • D) (Sum.inl i) (Sum.inr j) = 0 := by
    rw [diagonal_exp]; rfl
  rw [hDzero,sub_zero] at h
  change expEntry A (Sum.inl i) (Sum.inr j) t = _ at h
  rw [h]
  simp_rw [hentry]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro b _
      rw [intervalIntegral.integral_const_mul]
    · intro b _
      apply Continuous.intervalIntegrable
      exact ((expEntry_continuous B i a).comp (by fun_prop) |>.mul
        (expEntry_continuous E b j)).const_mul (C a b)
  · intro a _
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro b _
    exact ((expEntry_continuous B i a).comp (by fun_prop) |>.mul
      (expEntry_continuous E b j)).const_mul (C a b)

end SSP.BlockTriangular
