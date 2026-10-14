import SSPLean.K3CyclicComplexFirstDegreeBounds
import SSPLean.K3CyclicComplexFirstNegativeCoefficient

/-! # Structural degree bounds for the negative-m compact chart -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.NegativeCoeff

open Dense ComplexCoeff

theorem bounded_bone : Bounded bone 0 0 := by
  simp [bone, Bounded, brat]

theorem bounded_trace : Bounded trace 0 1 := by
  exact (bounded_bone.mono (by omega) (by omega)).sub bounded_br

theorem bounded_z : Bounded z 1 2 := by
  have htwo : Bounded (brat 2) 0 1 :=
    (bounded_brat 2).mono (by omega) (by omega)
  have hgap : Bounded (bsub (brat 2) br) 0 1 := htwo.sub bounded_br
  have hlower :
      Bounded (bmul (brat (1 / 3)) (bmul br (bsub (brat 2) br))) 1 2 :=
    ((bounded_brat (1 / 3)).mul (bounded_br.mul hgap)).mono
      (by omega) (by omega)
  have hone : Bounded bone 0 1 := bounded_bone.mono (by omega) (by omega)
  have honeSub : Bounded (bsub bone br) 0 1 := hone.sub bounded_br
  have hsquare : Bounded (bpow (bsub bone br) 2) 0 2 := by
    simpa using honeSub.pow 2
  have hupper :
      Bounded (bmul (brat (1 / 4))
        (bmul btau (bpow (bsub bone br) 2))) 1 2 := by
    simpa using (bounded_brat (1 / 4)).mul (bounded_btau.mul hsquare)
  exact hlower.add hupper

theorem bounded_pair : Bounded pair 1 2 := by
  have hr2 : Bounded (bpow br 2) 1 2 :=
    (bounded_br.pow 2).mono (by omega) (by omega)
  have hfirst : Bounded (bmul (brat (1 / 3)) (bpow br 2)) 1 2 :=
    ((bounded_brat (1 / 3)).mul hr2).mono (by omega) (by omega)
  have hsecond : Bounded (bmul (brat (2 / 3)) br) 1 2 :=
    ((bounded_brat (2 / 3)).mul bounded_br).mono (by omega) (by omega)
  exact (hfirst.sub hsecond).add bounded_z

theorem bounded_feedback : Bounded feedback 1 3 := by
  have hone : Bounded bone 0 1 := bounded_bone.mono (by omega) (by omega)
  have hleft : Bounded (bsub bone (bmul (brat (1 / 3)) br)) 0 1 :=
    hone.sub ((bounded_brat (1 / 3)).mul bounded_br)
  have hr2 : Bounded (bpow br 2) 1 2 :=
    (bounded_br.pow 2).mono (by omega) (by omega)
  have hright :
      Bounded (badd (bmul (brat (1 / 9)) (bpow br 2)) z) 1 2 :=
    (((bounded_brat (1 / 9)).mul hr2).mono (by omega) (by omega)).add bounded_z
  exact hleft.mul hright

theorem derivativeTriple_bounded (n : ℕ) :
    Bounded (derivativeTriple n).1 (n / 2) n ∧
      Bounded (derivativeTriple n).2.1 ((n + 1) / 2) (n + 1) ∧
      Bounded (derivativeTriple n).2.2 ((n + 2) / 2) (n + 2) := by
  induction n with
  | zero =>
      simp only [derivativeTriple, initialTriple]
      exact ⟨bounded_bone, bounded_bzero 0 1, bounded_bzero 1 2⟩
  | succ n ih =>
      simp only [derivativeTriple, nextTriple]
      refine ⟨ih.2.1, ih.2.2, ?_⟩
      have ht := bounded_trace.mul ih.2.2
      have hp := bounded_pair.mul ih.2.1
      have hf := bounded_feedback.mul ih.1
      exact ((ht.mono (by omega) (by omega)).sub
        (hp.mono (by omega) (by omega))).add
          (hf.mono (by omega) (by omega))

theorem derivative_bounded (n : ℕ) :
    Bounded (derivativeTriple n).1 (n / 2) n :=
  (derivativeTriple_bounded n).1

theorem derivativeTableAux_spec (n : ℕ) :
    (derivativeTableAux n).1.reverse =
        (List.range n).map (fun k => (derivativeTriple k).1) ∧
      (derivativeTableAux n).2 = derivativeTriple n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      simp only [derivativeTableAux]
      rw [ih.2]
      constructor
      · rw [List.reverse_cons, ih.1, List.range_succ, List.map_append]
        simp
      · rfl

theorem derivativeTable_getD {count j : ℕ} (hj : j < count) :
    (derivativeTable count).getD j bzero = (derivativeTriple j).1 := by
  unfold derivativeTable
  rw [(derivativeTableAux_spec count).1,
    List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem curvatureTerm_bounded {N j : ℕ} (hj : j ≤ N) :
    Bounded
      (bmul (brat (ComplexCoeff.kernel N j))
        (bmul (derivativeTriple j).1 (derivativeTriple (N - j)).1))
      (N / 2) N := by
  have hp := (derivative_bounded j).mul (derivative_bounded (N - j))
  have hp' : Bounded
      (bmul (derivativeTriple j).1 (derivativeTriple (N - j)).1)
      (N / 2) N := hp.mono (by omega) (by omega)
  simpa using (bounded_brat (ComplexCoeff.kernel N j)).mul hp'

theorem curvatureCoefficient_bounded (N : ℕ) :
    Bounded (curvatureCoefficient N) (N / 2) N := by
  unfold curvatureCoefficient
  dsimp only
  apply foldl_badd_bounded (bounded_bzero (N / 2) N)
  intro j hj
  have hjN : j ≤ N := Nat.le_of_lt_succ (List.mem_range.mp hj)
  rw [derivativeTable_getD (Nat.lt_succ_of_le hjN),
    derivativeTable_getD (Nat.lt_succ_of_le (Nat.sub_le N j))]
  exact curvatureTerm_bounded hjN

theorem curvatureCoefficient_outer_degree {N : ℕ} :
    (curvatureCoefficient N).length ≤ N / 2 + 1 :=
  (curvatureCoefficient_bounded N).1

theorem curvatureCoefficient_inner_degree {N b : ℕ} :
    ((curvatureCoefficient N).getD b []).length ≤ N + 1 := by
  by_cases hb : b < (curvatureCoefficient N).length
  · apply (curvatureCoefficient_bounded N).2
    rw [List.getD_eq_getElem _ _ hb]
    exact List.getElem_mem hb
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

end SSP.K3CyclicComplex.NegativeCoeff
