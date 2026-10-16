import SSPLean.LogConvexTransforms
import SSPLean.LogConvexCurvature

/-! Closure rules that allow identically zero summands, as needed for sparse blocks. -/
set_option autoImplicit false
open Set
namespace SSP.LogConvexIntegral

/-- A function is either identically zero, or positive at positive times with
logarithmically convex dimension-corrected quotient. -/
def PositiveLogConvex (p : ℕ) (f : ℝ → ℝ) : Prop :=
  f = 0 ∨ ((∀ t, 0 < t → 0 < f t) ∧
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (f t/t^p)))

theorem PositiveLogConvex.zero (p : ℕ) : PositiveLogConvex p 0 := Or.inl rfl

theorem PositiveLogConvex.nonneg {p : ℕ} {f : ℝ → ℝ} (h : PositiveLogConvex p f)
    (t : ℝ) (ht : 0 < t) : 0 ≤ f t := by
  rcases h with h | ⟨hp,_⟩
  · simp [h]
  · exact (hp t ht).le

theorem PositiveLogConvex.convex {p : ℕ} {f : ℝ → ℝ} (h : PositiveLogConvex p f) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (f t/t^p)) := by
  rcases h with h | ⟨_,hc⟩
  · simpa [h] using convexOn_const (0 : ℝ) (convex_Ioi (0 : ℝ))
  · exact hc

theorem PositiveLogConvex.mono {p q : ℕ} {f : ℝ → ℝ} (h : PositiveLogConvex p f)
    (hpq : p ≤ q) : PositiveLogConvex q f := by
  rcases h with h | ⟨hp,hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨hp,log_quotient_convex_mono f hpq hp hc⟩

theorem PositiveLogConvex.const_mul {p : ℕ} {f : ℝ → ℝ} (h : PositiveLogConvex p f)
    {c : ℝ} (hc : 0 ≤ c) : PositiveLogConvex p (fun t => c*f t) := by
  rcases h with h | ⟨hp,hconv⟩
  · left; ext t; simp [h]
  · by_cases hc0 : c = 0
    · left; ext t; simp [hc0]
    · have hcpos := lt_of_le_of_ne hc (Ne.symm hc0)
      exact Or.inr ⟨fun t ht => mul_pos hcpos (hp t ht),
        log_quotient_const_mul_convex f p c hcpos hp hconv⟩

theorem PositiveLogConvex.add {p : ℕ} {f g : ℝ → ℝ}
    (hf : PositiveLogConvex p f) (hg : PositiveLogConvex p g) :
    PositiveLogConvex p (fun t => f t+g t) := by
  rcases hf with hf | ⟨hfp,hfc⟩
  · simpa [hf] using hg
  rcases hg with hg | ⟨hgp,hgc⟩
  · simpa [hg,PositiveLogConvex] using Or.inr (show (∀ t, 0 < t → 0 < f t) ∧
        ConvexOn ℝ (Ioi 0) (fun t => Real.log (f t/t^p)) from ⟨hfp,hfc⟩)
  right
  refine ⟨fun t ht => add_pos (hfp t ht) (hgp t ht),?_⟩
  have hc := log_nonneg_combination_convex (fun t => f t/t^p) (fun t => g t/t^p)
    1 1 (by norm_num) (by norm_num) (by norm_num)
    (fun t ht => div_pos (hfp t ht) (pow_pos ht _))
    (fun t ht => div_pos (hgp t ht) (pow_pos ht _)) hfc hgc
  simpa only [one_mul,add_div] using hc

theorem PositiveLogConvex.sum {α : Type*} {p : ℕ} (s : Finset α) (f : α → ℝ → ℝ)
    (h : ∀ i ∈ s, PositiveLogConvex p (f i)) :
    PositiveLogConvex p (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => left; ext t; simp
  | @insert a s ha ih =>
    simpa [Finset.sum_insert ha] using
      (h a (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem PositiveLogConvex.convolution {p q : ℕ} {f g : ℝ → ℝ}
    (hf : PositiveLogConvex p f) (hg : PositiveLogConvex q g)
    (hfc : Continuous f) (hgc : Continuous g) :
    PositiveLogConvex (p+q+1) (convolution f g) := by
  rcases hf with hf | ⟨hfp,hfv⟩
  · left; ext t; simp [hf,SSP.LogConvexIntegral.convolution]
  rcases hg with hg | ⟨hgp,hgv⟩
  · left; ext t; simp [hg,SSP.LogConvexIntegral.convolution]
  exact Or.inr ⟨convolution_pos f g hfc hgc hfp hgp,
    log_convolution_quotient_convex f g p q hfc hgc hfp hgp hfv hgv⟩

end SSP.LogConvexIntegral
