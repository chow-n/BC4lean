import BC4lean.EuclideanLocalization
import BC4lean.EuclideanSL
import BC4lean.ReducedOperatorK1
import BC4lean.OddFredholmPolarUnitary
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Instances.Matrix

/-! # The winding number on `K₁` of a C⋆-algebra isomorphic to `C(𝕋)`

Here `𝕋` is `AddCircle (1 : ℝ)`.

1. **Winding number.** A nonvanishing `f : C(𝕋, ℂ)`, read along `[0, 1]`, is a path in `ℂ \ {0}`;
   lift it through the covering map `exp` (`isCoveringMap_exp`, `IsCoveringMap.liftPath`) and divide
   the change of the lift by `2πi` (`winding`). It is additive on products, `n` on `fourier n`, zero on
   functions with values in the slit plane, hence locally constant in the sup norm and constant along
   norm-continuous paths.
2. **Determinant.** For a star homomorphism `φ : A →⋆ₐ[ℂ] C(𝕋, ℂ)` and a matrix unitary `u` over `A`,
   `det (φ u)` is unitary in `C(𝕋, ℂ)`, so nowhere zero. Its winding number is invariant under a change
   of coordinates and a norm homotopy, additive on block sums and zero on identities, so it descends to
   an additive map `windingHom φ : K₁ A →+ ℤ`: the moves defining BC4lean's stable quotient `K1` are
   exactly these.
3. **Rational functions on the circle.** `circleEval : CircleLoc →+* C(𝕋, ℂ)` sends `p / s` to
   `θ ↦ p(e^{2πiθ}) / s(e^{2πiθ})`; `s` has no zero on the circle. An element of `CircleLoc` is a unit
   iff its image is, so a matrix over `CircleLoc` is invertible iff its image in `M_n(C(𝕋))` has
   invertible determinant (`isUnit_det_iff`).
4. **Paths in `GL_n(C(𝕋))`.** `circleGL n` is open, so it contains a sup-metric ball around `U`;
   trigonometric polynomials are dense and are values of `circleEval`, so the straight segment from `U`
   to some `G.map circleEval` stays in `circleGL n` (`exists_joinedIn_circleEval`). Over the Euclidean
   domain `CircleLoc`, `G = (∏ transvections) * diag(det G, 1, …)`, and scaling every transvection
   parameter by `s ∈ [0, 1]` is a path with constant determinant (`joinedIn_diagonal_of_circleLoc`).
5. **Winding number zero.** A nowhere-zero `d` with winding number `0` has a continuous logarithm `L`
   (the lift closes up), and `s ↦ diag(exp (s L), 1, …)` joins `diag(d, 1, …)` to `1`. The winding
   number of `det` is constant along paths in `GL_n(C(𝕋))`, so a matrix in `GL_n(C(𝕋))` whose
   determinant has winding number `0` is joined to `1` (`joinedIn_one_of_winding_eq_zero`).
6. **Injectivity.** For `φ : A ≃⋆ₐ[ℂ] C(𝕋, ℂ)` apply `φ⁻¹` entrywise to such a path and normalise it
   with `oddFredholmPolarUnitaryPath` (`g ↦ g (g⋆g)^{-1/2}`, which fixes unitaries). So a matrix
   unitary whose determinant has winding number `0` is homotopic to `1` among unitaries, and
   `windingHom φ` is injective (`windingHom_injective`).
-/

noncomputable section
open scoped CStarAlgebra

universe u

namespace BC4lean.OperatorKTheory.CircleWinding

open EuclideanLocalization EuclideanSL

section Winding

open Complex Real

/-! ## The winding number of a nonvanishing function on the circle -/

theorem continuous_circleParam : Continuous fun s : unitInterval => ((s : ℝ) : AddCircle (1 : ℝ)) :=
  (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val

/-- A nonvanishing function on the circle, read along `[0, 1]` as a path in `ℂ \ {0}`. -/
def circlePath (f : C(AddCircle (1 : ℝ), ℂ)) (hf : ∀ t, f t ≠ 0) : C(unitInterval, {z : ℂ // z ≠ 0}) :=
  ⟨fun s => ⟨f ((s : ℝ) : AddCircle (1 : ℝ)), hf _⟩,
    (f.continuous.comp continuous_circleParam : Continuous fun s : unitInterval => f ((s : ℝ) : AddCircle (1 : ℝ))).subtype_mk _⟩

/-- The lift of `circlePath f` through `exp`, starting at `log (f 0)`. -/
def windingLift (f : C(AddCircle (1 : ℝ), ℂ)) (hf : ∀ t, f t ≠ 0) : C(unitInterval, ℂ) :=
  isCoveringMap_exp.liftPath (circlePath f hf) (log (f 0)) (by
    apply Subtype.ext
    change f (((0 : unitInterval) : ℝ) : AddCircle (1 : ℝ)) = exp (log (f 0))
    rw [exp_log (hf 0)]
    simp)

theorem exp_windingLift (f : C(AddCircle (1 : ℝ), ℂ)) (hf : ∀ t, f t ≠ 0) (s : unitInterval) :
    exp (windingLift f hf s) = f ((s : ℝ) : AddCircle (1 : ℝ)) :=
  congrArg Subtype.val (congrFun (isCoveringMap_exp.liftPath_lifts (circlePath f hf) _ _) s)

theorem windingLift_zero (f : C(AddCircle (1 : ℝ), ℂ)) (hf : ∀ t, f t ≠ 0) : windingLift f hf 0 = log (f 0) :=
  isCoveringMap_exp.liftPath_zero _ _ _

theorem exists_winding (f : C(AddCircle (1 : ℝ), ℂ)) (hf : ∀ t, f t ≠ 0) :
    ∃ n : ℤ, windingLift f hf 1 = windingLift f hf 0 + (n : ℂ) * (2 * π * I) := by
  rw [← exp_eq_exp_iff_exists_int, exp_windingLift, exp_windingLift]
  simp [AddCircle.coe_period]

/-- The winding number of a nonvanishing function on the circle. -/
def winding (f : C(AddCircle (1 : ℝ), ℂ)) (hf : ∀ t, f t ≠ 0) : ℤ := (exists_winding f hf).choose

theorem winding_spec (f : C(AddCircle (1 : ℝ), ℂ)) (hf : ∀ t, f t ≠ 0) :
    windingLift f hf 1 = windingLift f hf 0 + (winding f hf : ℂ) * (2 * π * I) :=
  (exists_winding f hf).choose_spec

/-- Any continuous logarithm of `f` along `[0, 1]` computes the winding number. -/
theorem winding_eq_of_lift (f : C(AddCircle (1 : ℝ), ℂ)) (hf : ∀ t, f t ≠ 0) (Γ : unitInterval → ℂ) (hΓ : Continuous Γ)
    (hexp : ∀ s, exp (Γ s) = f ((s : ℝ) : AddCircle (1 : ℝ))) (n : ℤ) (hn : Γ 1 = Γ 0 + (n : ℂ) * (2 * π * I)) :
    winding f hf = n := by
  have h0 : exp (Γ 0) = exp (windingLift f hf 0) := by
    rw [hexp, exp_windingLift]
  have hΓ' : (fun s => Γ s - Γ 0 + windingLift f hf 0) = ⇑(windingLift f hf) := by
    refine (isCoveringMap_exp.eq_liftPath_iff (γ := circlePath f hf) (e := log (f 0)) _).2
      ⟨by fun_prop, ?_, ?_⟩
    · funext s
      apply Subtype.ext
      change exp (Γ s - Γ 0 + windingLift f hf 0) = f ((s : ℝ) : AddCircle (1 : ℝ))
      rw [Complex.exp_add, Complex.exp_sub, h0, div_mul_cancel₀ _ (Complex.exp_ne_zero _), hexp s]
    · simp [windingLift_zero]
  have h1 : Γ 1 - Γ 0 + windingLift f hf 0 = windingLift f hf 1 := congrFun hΓ' 1
  have key : (winding f hf : ℂ) * (2 * π * I) = (n : ℂ) * (2 * π * I) := by
    linear_combination -(winding_spec f hf) - h1 + hn
  have hne : (2 * π * I : ℂ) ≠ 0 := by simp [pi_ne_zero]
  exact_mod_cast mul_right_cancel₀ hne key

theorem winding_congr {f g : C(AddCircle (1 : ℝ), ℂ)} (h : f = g) (hf : ∀ t, f t ≠ 0) (hg : ∀ t, g t ≠ 0) :
    winding f hf = winding g hg := by
  subst h; rfl

theorem winding_mul (f g : C(AddCircle (1 : ℝ), ℂ)) (hf : ∀ t, f t ≠ 0) (hg : ∀ t, g t ≠ 0) :
    winding (f * g) (fun t => mul_ne_zero (hf t) (hg t)) = winding f hf + winding g hg := by
  apply winding_eq_of_lift _ _ (fun s => windingLift f hf s + windingLift g hg s) (by fun_prop)
  · intro s
    simp only [Complex.exp_add, exp_windingLift, ContinuousMap.mul_apply]
  · rw [winding_spec f hf, winding_spec g hg]
    push_cast
    ring

theorem winding_one : winding 1 (fun _ => one_ne_zero) = 0 := by
  apply winding_eq_of_lift _ _ (fun _ => 0) continuous_const
  · simp
  · simp

theorem fourier_ne_zero (n : ℤ) (t : AddCircle (1 : ℝ)) : fourier n t ≠ 0 := by
  rw [fourier_apply]
  exact Circle.coe_ne_zero _

theorem winding_fourier (n : ℤ) : winding (fourier n) (fourier_ne_zero n) = n := by
  apply winding_eq_of_lift _ _ (fun s => 2 * π * I * n * ((s : ℝ) : ℂ)) (by fun_prop)
  · intro s
    rw [fourier_coe_apply, Complex.ofReal_one, div_one]
  · simp only [Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one, Complex.ofReal_zero,
      mul_one, mul_zero, zero_add]
    ring

/-- A function with values in the slit plane has a continuous logarithm, hence winding zero. -/
theorem winding_eq_zero_of_slitPlane (h : C(AddCircle (1 : ℝ), ℂ)) (hs : ∀ t, h t ∈ slitPlane) :
    winding h (fun t => slitPlane_ne_zero (hs t)) = 0 := by
  apply winding_eq_of_lift _ _ (fun s => log (h ((s : ℝ) : AddCircle (1 : ℝ))))
  · exact Continuous.clog (h.continuous.comp continuous_circleParam :
      Continuous fun s : unitInterval => h ((s : ℝ) : AddCircle (1 : ℝ))) (fun s => hs _)
  · intro s
    exact exp_log (slitPlane_ne_zero (hs _))
  · simp [AddCircle.coe_period]

/-- Local constancy: a function closer to `f` than `min |f|` has the same winding number. -/
theorem winding_eq_of_norm_sub_lt (f g : C(AddCircle (1 : ℝ), ℂ)) (hf : ∀ t, f t ≠ 0) (hg : ∀ t, g t ≠ 0)
    (hfg : ∀ t, ‖g - f‖ < ‖f t‖) : winding g hg = winding f hf := by
  let h : C(AddCircle (1 : ℝ), ℂ) := ⟨fun t => g t / f t, g.continuous.div f.continuous hf⟩
  have hs : ∀ t, h t ∈ slitPlane := by
    intro t
    have hlt : ‖(g t - f t) / f t‖ < 1 := by
      rw [norm_div, div_lt_one (norm_pos_iff.2 (hf t))]
      exact lt_of_le_of_lt (by simpa using (g - f).norm_coe_le_norm t) (hfg t)
    have : h t = 1 + (g t - f t) / f t := by
      simp only [h, ContinuousMap.coe_mk]
      field_simp [hf t]
      ring
    rw [this]
    exact mem_slitPlane_of_norm_lt_one hlt
  have hgh : g = h * f := by
    ext t
    simp [h, div_mul_cancel₀ _ (hf t)]
  rw [winding_congr hgh hg (fun t => mul_ne_zero (slitPlane_ne_zero (hs t)) (hf t)),
    winding_mul h f (fun t => slitPlane_ne_zero (hs t)) hf, winding_eq_zero_of_slitPlane h hs,
    zero_add]

/-- The winding number is constant along a norm-continuous path of nonvanishing functions. -/
theorem winding_eq_of_path (F : unitInterval → C(AddCircle (1 : ℝ), ℂ)) (hF : Continuous F) (hne : ∀ s t, F s t ≠ 0) :
    winding (F 0) (hne 0) = winding (F 1) (hne 1) := by
  have hloc : IsLocallyConstant fun s => winding (F s) (hne s) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s
    obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
      (continuous_norm.comp (F s).continuous).continuousOn
    have hδ : 0 < ‖F s t₀‖ := norm_pos_iff.2 (hne s t₀)
    filter_upwards [Metric.tendsto_nhds.1 (hF.tendsto s) _ hδ] with s' hs'
    refine winding_eq_of_norm_sub_lt _ _ _ _ fun t => ?_
    rw [← dist_eq_norm]
    exact lt_of_lt_of_le hs' (isMinOn_iff.1 ht₀ t (Set.mem_univ t))
  exact hloc.apply_eq_of_preconnectedSpace 0 1


/-! ## The winding number of the determinant, on `K₁` -/

section K1
open OperatorKTheory
variable {A : Type u} [CStarAlgebra A]
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable (φ : A →⋆ₐ[ℂ] C(AddCircle (1 : ℝ), ℂ))

/-- The matrix of functions on the circle obtained by applying `φ` entrywise. -/
def circleMatrix (a : CStarMatrix ι ι A) : Matrix ι ι C(AddCircle (1 : ℝ), ℂ) :=
  CStarMatrix.ofMatrix.symm (matrixMap φ a)

@[simp] theorem circleMatrix_apply (a : CStarMatrix ι ι A) (i j : ι) :
    circleMatrix φ a i j = φ (a i j) := rfl

/-- The determinant of `φ` applied entrywise. -/
def circleDet (a : CStarMatrix ι ι A) : C(AddCircle (1 : ℝ), ℂ) := (circleMatrix φ a).det

theorem ne_zero_of_mem_unitary {f : C(AddCircle (1 : ℝ), ℂ)} (hf : f ∈ unitary C(AddCircle (1 : ℝ), ℂ)) (t : AddCircle (1 : ℝ)) : f t ≠ 0 := by
  intro h
  have := congrArg (fun g : C(AddCircle (1 : ℝ), ℂ) => g t) (Unitary.star_mul_self_of_mem hf)
  simp [h] at this

theorem continuous_circleMatrix : Continuous (circleMatrix φ (ι := ι)) :=
  continuous_matrix fun i j => (map_continuous φ).comp
    ((CStarMatrix.ofMatrixL (m := ι) (n := ι) (A := A)).symm.continuous.matrix_elem i j)

theorem continuous_circleDet : Continuous (circleDet φ : CStarMatrix ι ι A → C(AddCircle (1 : ℝ), ℂ)) :=
  (continuous_circleMatrix φ).matrix_det

theorem circleDet_one : circleDet φ (1 : CStarMatrix ι ι A) = 1 := by
  have : circleMatrix φ (1 : CStarMatrix ι ι A) = 1 := by
    ext i j
    rw [circleMatrix_apply, CStarMatrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [circleDet, this, Matrix.det_one]

variable [PartialOrder A] [StarOrderedRing A]

theorem circleDet_mem_unitary (u : MatrixUnitary A ι) :
    circleDet φ (u : CStarMatrix ι ι A) ∈ unitary C(AddCircle (1 : ℝ), ℂ) :=
  Matrix.det_of_mem_unitary (Unitary.map_mem CStarMatrix.ofMatrixStarAlgEquiv.symm
    (Unitary.map_mem (matrixMap φ) u.property))

theorem circleDet_ne_zero (u : MatrixUnitary A ι) (t : AddCircle (1 : ℝ)) :
    circleDet φ (u : CStarMatrix ι ι A) t ≠ 0 :=
  ne_zero_of_mem_unitary (circleDet_mem_unitary φ u) t

theorem circleDet_reindex (e : ι ≃ κ) (u : MatrixUnitary A ι) :
    circleDet φ (unitaryReindex e u : CStarMatrix κ κ A) = circleDet φ (u : CStarMatrix ι ι A) := by
  have : circleMatrix φ (unitaryReindex e u : CStarMatrix κ κ A) =
      Matrix.reindex e e (circleMatrix φ (u : CStarMatrix ι ι A)) := by
    ext i j
    rfl
  rw [circleDet, this, Matrix.det_reindex_self, circleDet]

theorem circleDet_blockSum (u : MatrixUnitary A ι) (v : MatrixUnitary A κ) :
    circleDet φ (unitaryBlockSum u v : CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A) =
      circleDet φ (u : CStarMatrix ι ι A) * circleDet φ (v : CStarMatrix κ κ A) := by
  have : circleMatrix φ (unitaryBlockSum u v : CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A) =
      Matrix.fromBlocks (circleMatrix φ (u : CStarMatrix ι ι A)) 0 0
        (circleMatrix φ (v : CStarMatrix κ κ A)) := by
    ext i j
    cases i <;> cases j <;> simp [unitaryBlockSum, matrixBlockSum, Matrix.fromBlocks]
  rw [circleDet, this, Matrix.det_fromBlocks_zero₂₁, circleDet, circleDet]

/-- The winding number of the determinant of a matrix unitary. -/
def unitaryWinding (u : MatrixUnitary A ι) : ℤ :=
  winding (circleDet φ (u : CStarMatrix ι ι A)) (circleDet_ne_zero φ u)

theorem unitaryWinding_reindex (e : ι ≃ κ) (u : MatrixUnitary A ι) :
    unitaryWinding φ (unitaryReindex e u) = unitaryWinding φ u :=
  winding_congr (circleDet_reindex φ e u) _ _

theorem unitaryWinding_blockSum (u : MatrixUnitary A ι) (v : MatrixUnitary A κ) :
    unitaryWinding φ (unitaryBlockSum u v) = unitaryWinding φ u + unitaryWinding φ v :=
  (winding_congr (circleDet_blockSum φ u v) _
    (fun t => mul_ne_zero (circleDet_ne_zero φ u t) (circleDet_ne_zero φ v t))).trans
    (winding_mul _ _ _ _)

theorem unitaryWinding_one : unitaryWinding φ (1 : MatrixUnitary A ι) = 0 :=
  (winding_congr (circleDet_one φ) _ (fun _ => one_ne_zero)).trans winding_one

theorem unitaryWinding_of_homotopic {u v : MatrixUnitary A ι} (h : UnitaryHomotopic u v) :
    unitaryWinding φ u = unitaryWinding φ v := by
  obtain ⟨γ⟩ := h
  let F : unitInterval → C(AddCircle (1 : ℝ), ℂ) := fun s => circleDet φ (γ s : CStarMatrix ι ι A)
  have hF : Continuous F := (continuous_circleDet φ).comp (continuous_subtype_val.comp γ.continuous)
  have hne : ∀ s t, F s t ≠ 0 := fun s => circleDet_ne_zero φ (γ s)
  calc unitaryWinding φ u = winding (F 0) (hne 0) := winding_congr (by simp [F]) _ _
    _ = winding (F 1) (hne 1) := winding_eq_of_path F hF hne
    _ = unitaryWinding φ v := winding_congr (by simp [F]) _ _

theorem unitaryWinding_equivalent {a b : FiniteUnitary A} (h : FiniteUnitary.Equivalent a b) :
    unitaryWinding φ a.val = unitaryWinding φ b.val := by
  induction h with
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h k ih ik => exact ih.trans ik
  | rel a b h =>
    cases h with
    | homotopy b e h =>
      exact (unitaryWinding_reindex φ e a.val).symm.trans (unitaryWinding_of_homotopic φ h)
    | stabilize κ =>
      change unitaryWinding φ a.val = unitaryWinding φ (unitaryBlockSum a.val (1 : MatrixUnitary A κ))
      rw [unitaryWinding_blockSum, unitaryWinding_one, add_zero]

/-- The winding number of the determinant, `K₁ A →+ ℤ`, for `φ : A →⋆ₐ[ℂ] C(𝕋, ℂ)`. -/
def windingHom : K1 A →+ ℤ where
  toFun := Quotient.lift (fun a : FiniteUnitary A => unitaryWinding φ a.val)
    (fun _ _ h => unitaryWinding_equivalent φ h)
  map_zero' := unitaryWinding_one φ (ι := Empty)
  map_add' a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro a b
    exact unitaryWinding_blockSum φ a.val b.val

@[simp] theorem windingHom_of (a : FiniteUnitary A) :
    windingHom φ (K1.of a) = unitaryWinding φ a.val := rfl

end K1

end Winding

/-! ## Evaluating `CircleLoc` on the circle -/

section Evaluation

open Polynomial

/-- Evaluation of a polynomial at `z = e^{2πiθ}`. -/
def polyEval : ℂ[X] →+* C(AddCircle (1 : ℝ), ℂ) := (Polynomial.aeval (fourier 1 : C(AddCircle (1 : ℝ), ℂ))).toRingHom

theorem polyEval_apply (p : ℂ[X]) (θ : AddCircle (1 : ℝ)) : polyEval p θ = p.eval (fourier 1 θ) :=
  aeval_continuousMap_apply p _ θ

theorem fourier_one_mem_sphere (θ : AddCircle (1 : ℝ)) : fourier 1 θ ∈ Metric.sphere (0 : ℂ) 1 := by
  rw [fourier_one, mem_sphere_zero_iff_norm]
  exact Circle.norm_coe _

theorem exists_fourier_one_eq {α : ℂ} (hα : α ∈ Metric.sphere (0 : ℂ) 1) :
    ∃ θ : AddCircle (1 : ℝ), fourier 1 θ = α := by
  refine ⟨((Complex.arg α / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ)), ?_⟩
  have hn : ‖α‖ = 1 := by simpa using hα
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [fourier_coe_apply]
  conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I α, hn]
  push_cast
  rw [one_mul]
  congr 1
  field_simp

theorem isUnit_polyEval {s : ℂ[X]} (hs : s ∈ awaySubmonoid (Metric.sphere (0 : ℂ) 1)) :
    IsUnit (polyEval s) := by
  rw [ContinuousMap.isUnit_iff_forall_ne_zero]
  intro θ h
  rw [polyEval_apply] at h
  exact hs.2 _ (fourier_one_mem_sphere θ) h

/-- Evaluation of `CircleLoc` on the circle. -/
def circleEval : CircleLoc →+* C(AddCircle (1 : ℝ), ℂ) :=
  IsLocalization.lift (M := awaySubmonoid (Metric.sphere (0 : ℂ) 1))
    (fun s : awaySubmonoid (Metric.sphere (0 : ℂ) 1) => isUnit_polyEval s.2)

theorem circleEval_algebraMap (p : ℂ[X]) :
    circleEval (algebraMap ℂ[X] CircleLoc p) = polyEval p :=
  IsLocalization.lift_eq _ _

theorem circleEval_X : circleEval (algebraMap ℂ[X] CircleLoc X) = fourier 1 := by
  rw [circleEval_algebraMap]
  ext θ
  simp [polyEval_apply]

theorem circleEval_mk' (p : ℂ[X]) (s : awaySubmonoid (Metric.sphere (0 : ℂ) 1)) :
    circleEval (IsLocalization.mk' CircleLoc p s) * polyEval s = polyEval p := by
  rw [← circleEval_algebraMap, ← circleEval_algebraMap, ← map_mul, IsLocalization.mk'_spec]

/-- An element of `CircleLoc` is a unit iff it has no zero on the circle. -/
theorem isUnit_iff_isUnit_circleEval (x : CircleLoc) : IsUnit x ↔ IsUnit (circleEval x) := by
  refine ⟨fun h => h.map _, fun h => ?_⟩
  rw [← mk'_rep _ x] at h ⊢
  set p := (rep (Metric.sphere (0 : ℂ) 1) x).1
  set s := (rep (Metric.sphere (0 : ℂ) 1) x).2
  have hp : IsUnit (polyEval p) := by
    rw [← circleEval_mk' p s]
    exact h.mul (isUnit_polyEval s.2)
  have hp0 : p ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hp
    exact not_isUnit_zero hp
  have hmem : p ∈ awaySubmonoid (Metric.sphere (0 : ℂ) 1) := by
    refine ⟨hp0, fun α hα hroot => ?_⟩
    obtain ⟨θ, hθ⟩ := exists_fourier_one_eq hα
    rw [ContinuousMap.isUnit_iff_forall_ne_zero] at hp
    exact hp θ (by rw [polyEval_apply, hθ]; exact hroot)
  exact isUnit_iff_exists_mk'.mpr ⟨⟨p, hmem⟩, s, rfl⟩

/-- A matrix over `CircleLoc` is invertible iff its evaluation on the circle has invertible
determinant. -/
theorem isUnit_det_iff {n : Type*} [Fintype n] [DecidableEq n] (g : Matrix n n CircleLoc) :
    IsUnit g.det ↔ IsUnit (g.map circleEval).det := by
  rw [isUnit_iff_isUnit_circleEval, RingHom.map_det]
  rfl

end Evaluation

section GeneralLinear

open Polynomial Matrix

/-! ## Trigonometric polynomials are values of `circleEval` -/

theorem X_mem_awaySubmonoid : (X : ℂ[X]) ∈ awaySubmonoid (Metric.sphere (0 : ℂ) 1) := by
  refine ⟨X_ne_zero, fun a ha h => ?_⟩
  rw [IsRoot, eval_X] at h
  subst h
  simp at ha

theorem fourier_add_eq_mul (m k : ℤ) :
    (fourier (m + k) : C(AddCircle (1 : ℝ), ℂ)) = fourier m * fourier k := by
  ext θ
  rw [fourier_add, ContinuousMap.mul_apply]

theorem fourier_neg_one_mem_range : (fourier (-1) : C(AddCircle (1 : ℝ), ℂ)) ∈ circleEval.range := by
  let s : awaySubmonoid (Metric.sphere (0 : ℂ) 1) := ⟨X, X_mem_awaySubmonoid⟩
  refine ⟨IsLocalization.mk' CircleLoc (1 : ℂ[X]) s, ?_⟩
  have h1 : circleEval (IsLocalization.mk' CircleLoc (1 : ℂ[X]) s) * fourier 1 = 1 := by
    have := circleEval_mk' 1 s
    rwa [map_one, ← circleEval_algebraMap, circleEval_X] at this
  have h2 : (fourier (-1) : C(AddCircle (1 : ℝ), ℂ)) * fourier 1 = 1 := by
    rw [← fourier_add_eq_mul]
    ext θ
    simp
  have hu : IsUnit (fourier 1 : C(AddCircle (1 : ℝ), ℂ)) :=
    ⟨⟨fourier 1, fourier (-1), by rw [mul_comm]; exact h2, h2⟩, rfl⟩
  exact hu.mul_left_inj.1 (h1.trans h2.symm)

theorem fourier_mem_range (k : ℤ) : (fourier k : C(AddCircle (1 : ℝ), ℂ)) ∈ circleEval.range := by
  have h1 : (fourier 1 : C(AddCircle (1 : ℝ), ℂ)) ∈ circleEval.range := ⟨_, circleEval_X⟩
  induction k using Int.induction_on with
  | zero =>
    have : (fourier 0 : C(AddCircle (1 : ℝ), ℂ)) = 1 := by ext θ; simp
    rw [this]
    exact one_mem _
  | succ k ih =>
    rw [fourier_add_eq_mul]
    exact mul_mem ih h1
  | pred k ih =>
    rw [sub_eq_add_neg, fourier_add_eq_mul]
    exact mul_mem ih fourier_neg_one_mem_range

theorem span_fourier_le_range {f : C(AddCircle (1 : ℝ), ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range (fourier (T := 1)))) : f ∈ circleEval.range := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, rfl⟩ := hf
    exact fourier_mem_range k
  | zero => exact zero_mem _
  | add f g _ _ hf hg => exact add_mem hf hg
  | smul c f _ hf =>
    have hc : (algebraMap ℂ C(AddCircle (1 : ℝ), ℂ) c) ∈ circleEval.range :=
      ⟨algebraMap ℂ[X] CircleLoc (C c), by
        rw [circleEval_algebraMap]
        exact aeval_C _ c⟩
    rw [show c • f = algebraMap ℂ C(AddCircle (1 : ℝ), ℂ) c * f from by ext t; simp]
    exact mul_mem hc hf

/-- Every continuous function on the circle is uniformly close to a value of `circleEval`. -/
theorem exists_dist_circleEval_lt (f : C(AddCircle (1 : ℝ), ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : CircleLoc, dist (circleEval r) f < ε := by
  have hd : f ∈ closure (Submodule.span ℂ (Set.range (fourier (T := 1))) : Set C(AddCircle (1 : ℝ), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.1 hd ε hε
  obtain ⟨r, rfl⟩ := span_fourier_le_range hg
  exact ⟨r, by rwa [dist_comm]⟩

/-! ## `GL_n(C(𝕋))` and approximation by `CircleLoc` -/

variable {n : Type} [Fintype n] [DecidableEq n]

/-- `GL_n(C(𝕋))`: matrices over `C(𝕋, ℂ)` with invertible determinant. -/
def circleGL (n : Type) [Fintype n] [DecidableEq n] : Set (Matrix n n C(AddCircle (1 : ℝ), ℂ)) :=
  {M | IsUnit M.det}

theorem isOpen_circleGL : IsOpen (circleGL n) :=
  Units.isOpen.preimage continuous_id.matrix_det

section Approximation

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- A matrix in `GL_n(C(𝕋))` is joined, inside `GL_n(C(𝕋))`, to the evaluation of a matrix
over `CircleLoc` (by a straight segment). -/
theorem exists_joinedIn_circleEval (U : Matrix n n C(AddCircle (1 : ℝ), ℂ)) (hU : U ∈ circleGL n) :
    ∃ G : Matrix n n CircleLoc, JoinedIn (circleGL n) U (G.map circleEval) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_circleGL U hU
  choose G hG using fun i j => exists_dist_circleEval_lt (U i j) hε
  refine ⟨Matrix.of G, JoinedIn.of_segment_subset
    (((convex_ball U ε).segment_subset (Metric.mem_ball_self hε) ?_).trans hball)⟩
  rw [Metric.mem_ball]
  exact (dist_pi_lt_iff hε).2 fun i => (dist_pi_lt_iff hε).2 fun j => hG i j

end Approximation

/-! ## Transvection paths -/

section TransvectionPaths

variable {R S : Type*} [CommRing R] [CommRing S]

omit [Fintype n] in
theorem map_transvection (f : R →+* S) (i j : n) (c : R) :
    (transvection i j c).map f = transvection i j (f c) := by
  ext a b
  simp only [transvection, map_apply, Matrix.add_apply, one_apply, single_apply]
  split_ifs <;> simp_all

omit [Fintype n] in
theorem map_diagonal_update_one (f : R →+* S) (i₀ : n) (x : R) :
    (diagonal (Function.update 1 i₀ x)).map f = diagonal (Function.update 1 i₀ (f x)) := by
  ext a b
  simp only [map_apply, diagonal_apply, Function.update_apply, Pi.one_apply]
  split_ifs <;> simp

theorem det_diagonal_update_one (i₀ : n) (x : R) :
    (diagonal (Function.update 1 i₀ x)).det = x := by
  rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i₀)]
  simp

/-- The transvection `T`, evaluated on the circle, with parameter scaled by `s`. -/
def tvScaled (T : TransvectionStruct n CircleLoc) (s : ℝ) : Matrix n n C(AddCircle (1 : ℝ), ℂ) :=
  transvection T.i T.j ((s : ℂ) • circleEval T.c)

omit [Fintype n] in
theorem continuous_tvScaled (T : TransvectionStruct n CircleLoc) : Continuous (tvScaled T) := by
  refine continuous_matrix fun a b => ?_
  simp only [tvScaled, transvection, Matrix.add_apply, one_apply, single_apply]
  split_ifs <;> fun_prop

/-- The product of the scaled transvections of a list. -/
def tvListScaled (L : List (TransvectionStruct n CircleLoc)) (s : ℝ) : Matrix n n C(AddCircle (1 : ℝ), ℂ) :=
  (L.map fun T => tvScaled T s).prod

theorem continuous_tvListScaled (L : List (TransvectionStruct n CircleLoc)) :
    Continuous (tvListScaled L) := by
  induction L with
  | nil =>
    have : tvListScaled ([] : List (TransvectionStruct n CircleLoc)) = fun _ => 1 := by
      funext s; simp [tvListScaled]
    rw [this]
    exact continuous_const
  | cons T L ih =>
    have : tvListScaled (T :: L) = fun s => tvScaled T s * tvListScaled L s := by
      funext s; simp [tvListScaled]
    rw [this]
    exact (continuous_tvScaled T).mul ih

theorem det_tvListScaled (L : List (TransvectionStruct n CircleLoc)) (s : ℝ) :
    (tvListScaled L s).det = 1 := by
  induction L with
  | nil => simp [tvListScaled]
  | cons T L ih =>
    simp only [tvListScaled, List.map_cons, List.prod_cons] at ih ⊢
    rw [det_mul, ih, tvScaled, det_transvection_of_ne _ _ T.hij, one_mul]

theorem tvListScaled_zero (L : List (TransvectionStruct n CircleLoc)) : tvListScaled L 0 = 1 := by
  induction L with
  | nil => simp [tvListScaled]
  | cons T L ih =>
    simp only [tvListScaled, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, mul_one, tvScaled]
    convert transvection_zero T.i T.j using 2
    ext t
    simp

theorem tvListScaled_one (L : List (TransvectionStruct n CircleLoc)) :
    tvListScaled L 1 = (L.map TransvectionStruct.toMatrix).prod.map circleEval := by
  induction L with
  | nil => simp [tvListScaled]
  | cons T L ih =>
    simp only [tvListScaled, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, Matrix.map_mul]
    congr 1
    simp [tvScaled, TransvectionStruct.toMatrix, map_transvection]

/-- An evaluated matrix over `CircleLoc` in `GL_n(C(𝕋))` is joined, inside `GL_n(C(𝕋))`, to
`diag(det, 1, …, 1)`. -/
theorem joinedIn_diagonal_of_circleLoc (i₀ : n) (G : Matrix n n CircleLoc)
    (hG : G.map circleEval ∈ circleGL n) :
    JoinedIn (circleGL n) (G.map circleEval) (diagonal (Function.update 1 i₀ (circleEval G.det))) := by
  have hGdet : IsUnit G.det := (isUnit_det_iff G).2 hG
  obtain ⟨L, hL⟩ := exists_list_transvec_mul_diagonal_eq i₀ G hGdet
  set D : Matrix n n C(AddCircle (1 : ℝ), ℂ) := diagonal (Function.update 1 i₀ (circleEval G.det))
  let γ : Path D (G.map circleEval) :=
    { toFun := fun s => tvListScaled L (s : ℝ) * D
      continuous_toFun := ((continuous_tvListScaled L).comp continuous_subtype_val).mul continuous_const
      source' := by simp only [Set.Icc.coe_zero, tvListScaled_zero, one_mul]
      target' := by
        simp only [Set.Icc.coe_one, tvListScaled_one, D, ← map_diagonal_update_one, ← Matrix.map_mul, hL] }
  refine JoinedIn.symm ⟨γ, fun s => ?_⟩
  change IsUnit (tvListScaled L (s : ℝ) * D).det
  rw [det_mul, det_tvListScaled, one_mul, det_diagonal_update_one]
  exact hGdet.map circleEval

end TransvectionPaths

/-- Every element of `GL_n(C(𝕋))` is joined inside `GL_n(C(𝕋))` to some
`diag(d, 1, …, 1)`. -/
theorem exists_joinedIn_diagonal (i₀ : n) (U : Matrix n n C(AddCircle (1 : ℝ), ℂ)) (hU : U ∈ circleGL n) :
    ∃ d : C(AddCircle (1 : ℝ), ℂ), JoinedIn (circleGL n) U (diagonal (Function.update 1 i₀ d)) := by
  obtain ⟨G, hUG⟩ := exists_joinedIn_circleEval U hU
  exact ⟨_, hUG.trans (joinedIn_diagonal_of_circleLoc i₀ G hUG.target_mem)⟩

end GeneralLinear

section Injectivity

open Matrix

/-! ## Winding number zero gives a logarithm and a path to `1` -/

/-- A nowhere-zero function on the circle with winding number zero is `exp` of a continuous
function. -/
theorem exists_log_of_winding_eq_zero (h : C(AddCircle (1 : ℝ), ℂ)) (hh : ∀ t, h t ≠ 0) (hw : winding h hh = 0) :
    ∃ L : C(AddCircle (1 : ℝ), ℂ), ∀ t, Complex.exp (L t) = h t := by
  set Γ := windingLift h hh
  have hΓ : Γ 1 = Γ 0 := by
    have := winding_spec h hh
    rw [hw] at this
    simpa using this
  let f : ℝ → ℂ := fun x => Γ (Set.projIcc 0 1 zero_le_one x)
  have hf : Continuous f := Γ.continuous.comp continuous_projIcc
  have hf01 : f 0 = f (0 + 1) := by
    simp only [f, zero_add, Set.projIcc_left, Set.projIcc_right]
    exact hΓ.symm
  refine ⟨⟨AddCircle.liftIco 1 0 f, AddCircle.liftIco_continuous hf01 hf.continuousOn⟩, fun t => ?_⟩
  obtain ⟨⟨x, hx⟩, rfl⟩ := (AddCircle.equivIco 1 0).symm.surjective t
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, by simpa using hx.2.le⟩
  change Complex.exp (AddCircle.liftIco 1 0 f (x : AddCircle (1 : ℝ))) = h (x : AddCircle (1 : ℝ))
  rw [AddCircle.liftIco_coe_apply hx]
  simp only [f, Set.projIcc_of_mem _ hx']
  exact exp_windingLift h hh ⟨x, hx'⟩

variable {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] in
theorem continuous_diagonal_update_one {X : Type*} [TopologicalSpace X] (i₀ : n)
    {E : X → C(AddCircle (1 : ℝ), ℂ)} (hE : Continuous E) :
    Continuous fun s => diagonal (Function.update (1 : n → C(AddCircle (1 : ℝ), ℂ)) i₀ (E s)) := by
  refine continuous_matrix fun a b => ?_
  simp only [diagonal_apply, Function.update_apply, Pi.one_apply]
  split_ifs
  · exact hE
  all_goals exact continuous_const

/-- `diag(d, 1, …, 1)` with `winding d = 0` is joined to `1` inside `GL_n(C(𝕋))`. -/
theorem joinedIn_diagonal_one (i₀ : n) (d : C(AddCircle (1 : ℝ), ℂ)) (hd : ∀ t, d t ≠ 0) (hw : winding d hd = 0) :
    JoinedIn (circleGL n) (diagonal (Function.update 1 i₀ d)) 1 := by
  obtain ⟨L, hL⟩ := exists_log_of_winding_eq_zero d hd hw
  let F : C(ℝ × AddCircle (1 : ℝ), ℂ) := ⟨fun p => Complex.exp ((p.1 : ℂ) * L p.2), by fun_prop⟩
  let E : C(ℝ, C(AddCircle (1 : ℝ), ℂ)) := F.curry
  have hE : ∀ s t, E s t = Complex.exp ((s : ℂ) * L t) := fun _ _ => rfl
  have hE0 : E 0 = 1 := by ext t; simp [hE]
  have hE1 : E 1 = d := by ext t; simp [hE, hL]
  let γ : Path (1 : Matrix n n C(AddCircle (1 : ℝ), ℂ)) (diagonal (Function.update 1 i₀ d)) :=
    { toFun := fun s => diagonal (Function.update (1 : n → C(AddCircle (1 : ℝ), ℂ)) i₀ (E s))
      continuous_toFun := continuous_diagonal_update_one i₀ (E.continuous.comp continuous_subtype_val)
      source' := by
        simp only [Set.Icc.coe_zero, hE0]
        rw [← Pi.one_apply (M := fun _ : n => C(AddCircle (1 : ℝ), ℂ)) i₀, Function.update_eq_self]
        exact diagonal_one
      target' := by simp only [Set.Icc.coe_one, hE1] }
  refine JoinedIn.symm ⟨γ, fun s => ?_⟩
  change IsUnit (diagonal (Function.update 1 i₀ (E s))).det
  rw [det_diagonal_update_one, ContinuousMap.isUnit_iff_forall_ne_zero]
  intro t
  rw [hE]
  exact Complex.exp_ne_zero _

/-! ## The winding number of `det` is constant along paths in `GL_n(C(𝕋))` -/

theorem det_ne_zero_of_mem_circleGL {M : Matrix n n C(AddCircle (1 : ℝ), ℂ)} (hM : M ∈ circleGL n) (t : AddCircle (1 : ℝ)) :
    M.det t ≠ 0 :=
  ((ContinuousMap.isUnit_iff_forall_ne_zero _).1 hM) t

theorem winding_det_eq_of_joinedIn {M N : Matrix n n C(AddCircle (1 : ℝ), ℂ)} (h : JoinedIn (circleGL n) M N) :
    winding M.det (det_ne_zero_of_mem_circleGL h.source_mem) =
      winding N.det (det_ne_zero_of_mem_circleGL h.target_mem) := by
  let γ := h.somePath
  let F : unitInterval → C(AddCircle (1 : ℝ), ℂ) := fun s => (γ s).det
  have hF : Continuous F := continuous_id.matrix_det.comp γ.continuous
  have hne : ∀ s t, F s t ≠ 0 := fun s => det_ne_zero_of_mem_circleGL (h.somePath_mem s)
  calc winding M.det _ = winding (F 0) (hne 0) := winding_congr (by simp [F, γ]) _ _
    _ = winding (F 1) (hne 1) := winding_eq_of_path F hF hne
    _ = winding N.det _ := winding_congr (by simp [F, γ]) _ _

/-- `GL_n(C(𝕋))` minus the winding number: an invertible matrix whose determinant has winding
number zero is joined to `1` inside `GL_n(C(𝕋))`. -/
theorem joinedIn_one_of_winding_eq_zero (U : Matrix n n C(AddCircle (1 : ℝ), ℂ)) (hU : U ∈ circleGL n)
    (hw : winding U.det (det_ne_zero_of_mem_circleGL hU) = 0) : JoinedIn (circleGL n) U 1 := by
  cases isEmpty_or_nonempty n with
  | inl _ =>
    have : U = 1 := by ext i; exact isEmptyElim i
    subst this
    exact JoinedIn.refl hU
  | inr _ =>
    let i₀ : n := Classical.arbitrary n
    obtain ⟨d, hUD⟩ := exists_joinedIn_diagonal i₀ U hU
    have hdet : (diagonal (Function.update (1 : n → C(AddCircle (1 : ℝ), ℂ)) i₀ d)).det = d :=
      det_diagonal_update_one i₀ d
    have hd : ∀ t, d t ≠ 0 := fun t => hdet ▸ det_ne_zero_of_mem_circleGL hUD.target_mem t
    have hwd : winding d hd = 0 := by
      rw [← hw, winding_det_eq_of_joinedIn hUD]
      exact winding_congr hdet.symm _ _
    exact hUD.trans (joinedIn_diagonal_one i₀ d hd hwd)

/-! ## Transfer to `A ≃⋆ₐ C(𝕋)` and the polar retraction -/

section Transfer

open OperatorKTheory

variable {A : Type u} [CStarAlgebra A] (φ : A ≃⋆ₐ[ℂ] C(AddCircle (1 : ℝ), ℂ))

/-- Pull a matrix over `C(𝕋, ℂ)` back to a `CStarMatrix` over `A`, entrywise by `φ⁻¹`. -/
def pullback : Matrix n n C(AddCircle (1 : ℝ), ℂ) →+* CStarMatrix n n A :=
  (CStarMatrix.ofMatrixRingEquiv (n := n) (A := A)).toRingHom.comp
    (φ.symm : C(AddCircle (1 : ℝ), ℂ) →+* A).mapMatrix

theorem pullback_apply (M : Matrix n n C(AddCircle (1 : ℝ), ℂ)) (i j : n) : pullback φ M i j = φ.symm (M i j) := rfl

theorem continuous_pullback : Continuous (pullback (n := n) φ) := by
  have : Continuous fun M : Matrix n n C(AddCircle (1 : ℝ), ℂ) => M.map φ.symm :=
    continuous_matrix fun i j => (map_continuous φ.symm).comp (continuous_id.matrix_elem i j)
  exact (CStarMatrix.ofMatrixL (m := n) (n := n) (A := A)).continuous.comp this

theorem pullback_circleMatrix (a : CStarMatrix n n A) :
    pullback φ (circleMatrix (φ : A →⋆ₐ[ℂ] C(AddCircle (1 : ℝ), ℂ)) a) = a := by
  ext i j
  rw [pullback_apply, circleMatrix_apply]
  exact φ.symm_apply_apply _

variable [PartialOrder A] [StarOrderedRing A]

/-- A matrix unitary over `A` whose determinant has winding number zero is homotopic to `1`
among unitaries. -/
theorem unitaryHomotopic_one_of_unitaryWinding_eq_zero (v : MatrixUnitary A n)
    (hv : unitaryWinding (φ : A →⋆ₐ[ℂ] C(AddCircle (1 : ℝ), ℂ)) v = 0) : UnitaryHomotopic v 1 := by
  set ψ : A →⋆ₐ[ℂ] C(AddCircle (1 : ℝ), ℂ) := (↑φ : A →⋆ₐ[ℂ] C(AddCircle (1 : ℝ), ℂ))
  set U := circleMatrix ψ (v : CStarMatrix n n A)
  have hU : U ∈ circleGL n := Unitary.isUnit_coe (U := ⟨_, circleDet_mem_unitary ψ v⟩)
  have hUw : winding U.det (det_ne_zero_of_mem_circleGL hU) = 0 :=
    (winding_congr rfl _ _).trans hv
  have hpath := (joinedIn_one_of_winding_eq_zero U hU hUw).map (continuous_pullback φ)
  rw [pullback_circleMatrix, map_one] at hpath
  have hpath' : JoinedIn {x : CStarMatrix n n A | IsUnit x} (v : CStarMatrix n n A) 1 := by
    refine hpath.mono ?_
    rintro _ ⟨M, hM, rfl⟩
    exact ((Matrix.isUnit_iff_isUnit_det M).2 hM).map (pullback φ)
  let _ : PartialOrder (CStarMatrix n n A) := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing (CStarMatrix n n A) := CStarAlgebra.spectralOrderedRing _
  let γ := KKTheory.oddFredholmPolarUnitaryPath hpath'.somePath hpath'.somePath_mem
  have h0 : KKTheory.oddFredholmPolarUnitary (v : CStarMatrix n n A)
      (by simpa only [Path.source, Set.mem_ofPred_eq] using hpath'.somePath_mem 0) = v :=
    Subtype.ext (KKTheory.oddFredholmPolarElement_unitary v)
  have h1 : KKTheory.oddFredholmPolarUnitary (1 : CStarMatrix n n A)
      (by simpa only [Path.target, Set.mem_ofPred_eq] using hpath'.somePath_mem 1) = 1 :=
    Subtype.ext (KKTheory.oddFredholmPolarElement_unitary 1)
  exact ⟨(γ.cast h0.symm h1.symm)⟩

/-- **The winding number of the determinant is injective on `K₁ A`** for `A ≃⋆ₐ[ℂ] C(𝕋, ℂ)`. -/
theorem windingHom_injective :
    Function.Injective (windingHom (φ : A →⋆ₐ[ℂ] C(AddCircle (1 : ℝ), ℂ))) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨m, a, rfl⟩ := OperatorKTheory.K1.exists_finRepresentative x
  rw [windingHom_of] at hx
  rw [OperatorKTheory.K1.of_homotopic (unitaryHomotopic_one_of_unitaryWinding_eq_zero φ a hx)]
  exact OperatorKTheory.K1.of_identity (Fin m)

end Transfer

end Injectivity

end BC4lean.OperatorKTheory.CircleWinding
