import BC4lean.ProjectionHomotopy
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Order.ProjIcc

/-! # Projections over the circle are equivalent to constant ones

Let `P` be a projection in `M_n(C(𝕋))`, `𝕋 = ℝ/ℤ`, and let `P₀ = P(0)`, viewed as a constant
function. There is `v ∈ M_n(C(𝕋))` with `v v* = P` and `v* v = P₀`.

Proof. Write `P(t)` for `t ∈ ℝ`; it is 1-periodic. In `B = C([0,1], M_n(ℂ))` the projections
`s ↦ (t ↦ P(s t))` form a norm-continuous path from the constant `P₀` to `t ↦ P(t)`, so
`ProjectionHomotopy.equivalent_of_path` gives `w ∈ B` with `w(t)* w(t) = P₀` and
`w(t) w(t)* = P(t)`. Both `w(0)` and `w(1)` are partial isometries with initial and final
projection `P₀`, so `U = w(1)* w(0) + (1 - P₀)` is a unitary commuting with `P₀`. Its spectrum is
finite, so `arg` is continuous on it and `γ(t) = exp(i t arg U)` is a path of unitaries from `1`
to `U`, each commuting with `P₀`. Then `V(t) = w(t) γ(t)` has `V* V = P₀`, `V V* = P(t)` and
`V(1) = w(1) U = w(0) = V(0)`, so `V` descends to the circle.

No order instance on `C(𝕋)` enters: the statement is about plain matrices.
-/

noncomputable section
open scoped Matrix ComplexOrder

namespace BC4lean.OperatorKTheory.CircleProjection

/-! ### A unitary with finite spectrum is joined to `1` inside the commutant -/

section UnitaryPath

variable {A : Type*} [CStarAlgebra A]

open selfAdjoint Unitary Complex in
/-- For a unitary with finite spectrum, `exp (i arg u) = u` (Mathlib proves this when
`‖u - 1‖ < 2`; finiteness of the spectrum makes `arg` continuous on it in general). -/
theorem expUnitary_argSelfAdjoint_of_finite {u : unitary A} (hfin : (spectrum ℂ (u : A)).Finite) :
    expUnitary (argSelfAdjoint u) = u := by
  ext
  have : ContinuousOn arg (spectrum ℂ (u : A)) := hfin.continuousOn _
  rw [expUnitary_coe, argSelfAdjoint_coe, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ),
    ← cfc_comp_smul .., ← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (u : A)]
  refine cfc_congr fun y hy ↦ ?_
  have hy₁ : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 hy
  have : I * y.arg = log y :=
    Complex.ext (by simp [log_re, spectrum.norm_eq_one_of_unitary u.2 hy]) (by simp [log_im])
  simpa [← exp_eq_exp_ℂ, this] using exp_log (by aesop)

open selfAdjoint Unitary in
/-- A unitary `u` with finite spectrum is joined to `1` by a continuous path of unitaries, each
commuting with every `b` that commutes with `u` and `u*`. -/
theorem exists_unitary_path {u : A} (hu : u ∈ unitary A) (hfin : (spectrum ℂ u).Finite)
    {b : A} (hb : Commute u b) (hb' : Commute (star u) b) :
    ∃ γ : ℝ → A, Continuous γ ∧ γ 0 = 1 ∧ γ 1 = u ∧
      ∀ t, star (γ t) * γ t = 1 ∧ γ t * star (γ t) = 1 ∧ Commute (γ t) b := by
  let u' : unitary A := ⟨u, hu⟩
  let x : selfAdjoint A := argSelfAdjoint u'
  have hx : Commute (x : A) b := by
    simp only [x, argSelfAdjoint_coe]
    exact hb.cfc hb' _
  refine ⟨fun t => (expUnitary (t • x) : A), ?_, ?_, ?_, fun t => ⟨?_, ?_, ?_⟩⟩
  · exact continuous_subtype_val.comp
      (continuous_expUnitary.comp (continuous_id.smul continuous_const))
  · simp
  · simp only [one_smul]
    exact congrArg Subtype.val (expUnitary_argSelfAdjoint_of_finite (u := u') hfin)
  · exact coe_star_mul_self _
  · exact coe_mul_star_self _
  · simp only [expUnitary_coe, selfAdjoint.val_smul]
    exact Commute.exp_left ((hx.smul_left t).smul_left _)

end UnitaryPath

/-! ### Closing the loop: algebra in a star ring -/

section Closing

variable {R : Type*} [Ring R] [StarRing R]

/-- If `W` is a partial isometry with initial and final projection `p`, then `W + (1 - p)` is a
unitary commuting with `p`. -/
theorem unitary_add_complement {p W : R} (hp : IsStarProjection p)
    (h₁ : star W * W = p) (h₂ : W * star W = p) (h₃ : p * W = W) (h₄ : W * p = W) :
    star (W + (1 - p)) * (W + (1 - p)) = 1 ∧ (W + (1 - p)) * star (W + (1 - p)) = 1 ∧
      Commute (W + (1 - p)) p ∧ Commute (star (W + (1 - p))) p := by
  have hps : star p = p := hp.isSelfAdjoint.star_eq
  have hpp : p * p = p := hp.isIdempotentElem.eq
  have h₅ : star W * p = star W := by simpa [star_mul, hps] using congrArg star h₃
  have h₆ : p * star W = star W := by simpa [star_mul, hps] using congrArg star h₄
  have hs : star (W + (1 - p)) = star W + (1 - p) := by simp [hps]
  rw [hs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [add_mul, mul_add, mul_sub, sub_mul, one_mul, mul_one, h₁, h₅, h₃, hpp]
    abel
  · simp only [add_mul, mul_add, mul_sub, sub_mul, one_mul, mul_one, h₂, h₆, h₄, hpp]
    abel
  · simp only [Commute, SemiconjBy, add_mul, mul_add, mul_sub, sub_mul, one_mul, mul_one, h₃,
      h₄, hpp]
  · simp only [Commute, SemiconjBy, add_mul, mul_add, mul_sub, sub_mul, one_mul, mul_one, h₅,
      h₆, hpp]

end Closing

/-! ### The main lemma -/

section Main

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Evaluation at a point of the circle. -/
abbrev ev (x : AddCircle (1 : ℝ)) : C(AddCircle (1 : ℝ), ℂ) →⋆ₐ[ℂ] ℂ := ContinuousMap.evalStarAlgHom ℂ ℂ x

/-- The identification `M_n(ℂ) ≃ CStarMatrix`, used to move algebra between the two. -/
abbrev toC : Matrix ι ι ℂ ≃⋆ₐ[ℂ] CStarMatrix ι ι ℂ := CStarMatrix.ofMatrixStarAlgEquiv

omit [DecidableEq ι] in
theorem isStarProjection_map_ev {P : Matrix ι ι C(AddCircle (1 : ℝ), ℂ)} (hP : P * P = P) (hPs : Pᴴ = P)
    (x : AddCircle (1 : ℝ)) : IsStarProjection (toC (P.map (ev x))) := by
  refine IsStarProjection.map ?_ toC
  refine ⟨?_, ?_⟩
  · change P.map (ev x) * P.map (ev x) = P.map (ev x)
    rw [← Matrix.map_mul, hP]
  · change (P.map (ev x))ᴴ = P.map (ev x)
    rw [← Matrix.conjTranspose_map _ (fun a => map_star (ev x) a), hPs]

theorem coe_one_eq_coe_zero : ((1 : ℝ) : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) := by
  rw [AddCircle.coe_period]; rfl

/-- **Projections over the circle are trivial.** Every projection `P ∈ M_n(C(𝕋))` is
Murray–von Neumann equivalent, inside `M_n(C(𝕋))`, to the constant projection `P(0)`. -/
theorem exists_partialIsometry_const (P : Matrix ι ι C(AddCircle (1 : ℝ), ℂ)) (hP : P * P = P) (hPs : Pᴴ = P) :
    ∃ v : Matrix ι ι C(AddCircle (1 : ℝ), ℂ), v * vᴴ = P ∧
      vᴴ * v = P.map (fun f => algebraMap ℂ C(AddCircle (1 : ℝ), ℂ) (f 0)) := by
  -- the fibres `P(t)`, `t ∈ ℝ`
  let Pt : ℝ → CStarMatrix ι ι ℂ := fun t => toC (P.map (ev (t : AddCircle (1 : ℝ))))
  have hPt_cont : Continuous Pt :=
    continuous_pi fun i => continuous_pi fun j =>
      (P i j).continuous.comp (AddCircle.continuous_mk' (1 : ℝ))
  have hPt : ∀ t, IsStarProjection (Pt t) := fun t => isStarProjection_map_ev hP hPs _
  set P0 := Pt 0 with hP0def
  have hP1 : Pt 1 = P0 := by
    simp only [hP0def, Pt, coe_one_eq_coe_zero]
  -- Step A: a partial isometry over `[0,1]` from `P₀` to `P(t)`
  let g : C(unitInterval × unitInterval, CStarMatrix ι ι ℂ) :=
    ⟨fun st => Pt ((st.1 : ℝ) * st.2), hPt_cont.comp
      ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd))⟩
  let F := g.curry
  have hF : ∀ s, IsStarProjection (F s) := fun s =>
    ⟨ContinuousMap.ext fun t => (hPt _).isIdempotentElem.eq,
      ContinuousMap.ext fun t => (hPt _).isSelfAdjoint.star_eq⟩
  let path : Path (⟨F 0, hF 0⟩ : OperatorKTheory.Projection C(unitInterval, CStarMatrix ι ι ℂ))
      ⟨F 1, hF 1⟩ :=
    { toFun := fun s => ⟨F s, hF s⟩
      continuous_toFun := F.continuous.subtype_mk _
      source' := rfl
      target' := rfl }
  obtain ⟨w, hw1, hw2⟩ := OperatorKTheory.Projection.equivalent_of_path path
  have hw1' : ∀ t, star (w t) * w t = P0 := fun t => by
    have := congrArg (fun f : C(unitInterval, CStarMatrix ι ι ℂ) => f t) hw1
    simpa [F, g] using this
  have hw2' : ∀ t : unitInterval, w t * star (w t) = Pt t := fun t => by
    have := congrArg (fun f : C(unitInterval, CStarMatrix ι ι ℂ) => f t) hw2
    simpa [F, g] using this
  -- Step B: close the loop
  have hP0 : IsStarProjection P0 := hPt 0
  let p0 : OperatorKTheory.Projection (CStarMatrix ι ι ℂ) := ⟨P0, hP0⟩
  set a := w 0 with ha
  set b := w 1 with hb
  have ha1 : star a * a = P0 := hw1' 0
  have ha2 : a * star a = P0 := by simpa using hw2' 0
  have hb1 : star b * b = P0 := hw1' 1
  have hb2 : b * star b = P0 := by simpa [hP1] using hw2' 1
  have ha3 : a * P0 = a := OperatorKTheory.Projection.right_support p0 a ha1
  have hb3 : b * P0 = b := OperatorKTheory.Projection.right_support p0 b hb1
  have ha4 : P0 * a = a := by rw [← ha2, mul_assoc, ha1, ha3]
  have hb5 : star b * P0 = star b := by
    simpa [star_mul, hP0.isSelfAdjoint.star_eq] using congrArg star (show P0 * b = b by
      rw [← hb2, mul_assoc, hb1, hb3])
  have hb6 : P0 * star b = star b := by
    simpa [star_mul, hP0.isSelfAdjoint.star_eq] using congrArg star hb3
  set W := star b * a with hW
  have hWW : star W * W = P0 := by
    rw [hW, star_mul, star_star]
    calc star a * b * (star b * a) = star a * (b * star b) * a := by noncomm_ring
      _ = P0 := by rw [hb2, mul_assoc, ha4, ha1]
  have hWW' : W * star W = P0 := by
    rw [hW, star_mul, star_star]
    calc star b * a * (star a * b) = star b * (a * star a) * b := by noncomm_ring
      _ = P0 := by rw [ha2, hb5, hb1]
  have hPW : P0 * W = W := by rw [hW, ← mul_assoc, hb6]
  have hWP : W * P0 = W := by rw [hW, mul_assoc, ha3]
  obtain ⟨hU1, hU2, hUc, hUc'⟩ := unitary_add_complement hP0 hWW hWW' hPW hWP
  set U := W + (1 - P0) with hU
  have hfin : (spectrum ℂ U).Finite := by
    have h := AlgEquiv.spectrum_eq (toC (ι := ι)).toAlgEquiv (CStarMatrix.ofMatrix.symm U)
    have h' : (toC (ι := ι)).toAlgEquiv (CStarMatrix.ofMatrix.symm U) = U := rfl
    rw [h'] at h
    rw [h]
    exact Matrix.finite_spectrum _
  obtain ⟨γ, hγc, hγ0, hγ1, hγ⟩ :=
    exists_unitary_path (Unitary.mem_iff.mpr ⟨hU1, hU2⟩) hfin hUc hUc'
  -- the closed loop of partial isometries
  let V : unitInterval → CStarMatrix ι ι ℂ := fun t => w t * γ t
  have hVc : Continuous V := w.continuous.mul (hγc.comp continuous_subtype_val)
  have hV1 : ∀ t, star (V t) * V t = P0 := fun t => by
    calc star (w t * γ t) * (w t * γ t) = star (γ t) * (star (w t) * w t) * γ t := by
          simp only [star_mul, mul_assoc]
      _ = star (γ t) * (P0 * γ t) := by rw [hw1', mul_assoc]
      _ = star (γ t) * (γ t * P0) := by rw [((hγ t).2.2).eq]
      _ = P0 := by rw [← mul_assoc, (hγ t).1, one_mul]
  have hV2 : ∀ t, V t * star (V t) = Pt t := fun t => by
    calc w t * γ t * star (w t * γ t) = w t * (γ t * star (γ t)) * star (w t) := by
          simp only [star_mul, mul_assoc]
      _ = Pt t := by rw [(hγ t).2.1, mul_one, hw2']
  have hV01 : V 0 = V 1 := by
    change w 0 * γ ((0 : unitInterval) : ℝ) = w 1 * γ ((1 : unitInterval) : ℝ)
    rw [Set.Icc.coe_zero, Set.Icc.coe_one, hγ0, hγ1, mul_one, ← ha, ← hb, hU, hW]
    rw [mul_add, mul_sub, mul_one, ← mul_assoc, hb2, ha4, hb3, sub_self, add_zero]
  -- descend to the circle
  let Vext : ℝ → CStarMatrix ι ι ℂ := Set.IccExtend zero_le_one V
  have hVext : Continuous Vext := continuous_IccExtend_iff.mpr hVc
  have hVext01 : Vext 0 = Vext (0 + 1) := by
    simp only [zero_add, Vext]
    rw [Set.IccExtend_of_mem _ _ (Set.left_mem_Icc.2 zero_le_one),
      Set.IccExtend_of_mem _ _ (Set.right_mem_Icc.2 zero_le_one)]
    exact hV01
  let v : Matrix ι ι C(AddCircle (1 : ℝ), ℂ) := fun i j =>
    ⟨AddCircle.liftIco 1 0 (fun t => Vext t i j),
      AddCircle.liftIco_continuous (congrArg (fun M : CStarMatrix ι ι ℂ => M i j) hVext01)
        ((continuous_apply j).comp ((continuous_apply i).comp hVext)).continuousOn⟩
  have key : ∀ t (ht : t ∈ Set.Ico (0 : ℝ) 1),
      toC (v.map (ev (t : AddCircle (1 : ℝ)))) = V ⟨t, Set.Ico_subset_Icc_self ht⟩ := by
    intro t ht
    ext i j
    change AddCircle.liftIco 1 0 (fun t => Vext t i j) (t : AddCircle (1 : ℝ)) = _
    rw [AddCircle.liftIco_coe_apply (by simpa using ht)]
    simp only [Vext]
    rw [Set.IccExtend_of_mem _ _ (Set.Ico_subset_Icc_self ht)]
  have hsurj : ∀ x : AddCircle (1 : ℝ), ∃ t, ∃ ht : t ∈ Set.Ico (0 : ℝ) 1, (t : AddCircle (1 : ℝ)) = x := fun x =>
    ⟨(AddCircle.equivIco 1 0 x : ℝ), by simpa using (AddCircle.equivIco 1 0 x).2,
      AddCircle.coe_equivIco⟩
  have hext : ∀ M N : Matrix ι ι C(AddCircle (1 : ℝ), ℂ),
      (∀ t (_ : t ∈ Set.Ico (0 : ℝ) 1), toC (M.map (ev (t : AddCircle (1 : ℝ)))) = toC (N.map (ev (t : AddCircle (1 : ℝ))))) →
      M = N := by
    intro M N h
    ext i j x
    obtain ⟨t, ht, rfl⟩ := hsurj x
    exact congrArg (fun K : CStarMatrix ι ι ℂ => K i j) (h t ht)
  refine ⟨v, hext _ _ fun t ht => ?_, hext _ _ fun t ht => ?_⟩
  · rw [Matrix.map_mul, Matrix.conjTranspose_map _ (fun a => map_star (ev (t : AddCircle (1 : ℝ))) a), map_mul]
    change toC (v.map (ev (t : AddCircle (1 : ℝ)))) * star (toC (v.map (ev (t : AddCircle (1 : ℝ))))) = Pt t
    rw [key t ht]
    exact hV2 _
  · rw [Matrix.map_mul, Matrix.conjTranspose_map _ (fun a => map_star (ev (t : AddCircle (1 : ℝ))) a), map_mul]
    change star (toC (v.map (ev (t : AddCircle (1 : ℝ))))) * toC (v.map (ev (t : AddCircle (1 : ℝ)))) = _
    rw [key t ht, hV1]
    ext i j
    show P i j ((0 : ℝ) : AddCircle (1 : ℝ)) = P i j 0
    rw [QuotientAddGroup.mk_zero]

end Main

end BC4lean.OperatorKTheory.CircleProjection
