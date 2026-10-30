import BC4lean.KasparovReducingCompression
import BC4lean.IntervalKasparovFibre
import BC4lean.OddIntervalKasparovFibre

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Fibres of compressed interval cycles

Let `c` be a cycle over interval-type coefficients `C(X, B)` and `P` a reducing projection.
At every point `t` the fibre projection `P_t` reduces the fibre cycle, and the fibre of the
compression `c|P` is isomorphic to the compression of the fibre `(c_t)|P_t`. The module
isomorphism is the completion of evaluation `x ↦ x_t` from the range of `P` to the range of
`P_t`; it preserves the evaluated inner product and has dense range. -/

noncomputable section
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {Γ A B X M : Type*} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

section DenseEvaluation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- Variant of `hilbertModuleFibreEquivOfEvaluation` for an evaluation with dense range: the
completed fibre is complete and the induced map is isometric, so its range is closed. -/
def hilbertModuleFibreEquivOfDenseEvaluation (t : X) (f : M →L[ℂ] E)
    (hf : ∀ x y : M, ⟪f x, f y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t))
    (hfd : DenseRange f) : HilbertModuleEquiv B (HilbertModuleFibre B M t) E := by
  let fq : PositiveModuleQuotient B (EvaluatedModuleSpace B M t) →ₗ[ℂ] E :=
    (PositiveModuleForm.nullRadical (B := B) (E := EvaluatedModuleSpace B M t)).liftQ
      (f.toLinearMap.comp (evaluatedModuleLinearEquiv (B := B) (M := M) t).toLinearMap)
      (fun x hx => by
        apply (CStarModule.inner_self (A := Bᵐᵒᵖ)).mp
        change ⟪f (evaluatedModuleToOriginal t x), f (evaluatedModuleToOriginal t x)⟫_(Bᵐᵒᵖ) = 0
        rw [hf]
        exact (PositiveModuleForm.mem_nullRadical x).mp hx)
  have fq_norm (q : PositiveModuleQuotient B (EvaluatedModuleSpace B M t)) :
      ‖fq q‖ = ‖q‖ := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    change ‖f (evaluatedModuleToOriginal t x)‖ = ‖positiveModuleQuotientMk (B := B) x‖
    rw [PositiveModuleQuotient.norm_mk,
      CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), hf]
    rfl
  let fqL : PositiveModuleQuotient B (EvaluatedModuleSpace B M t) →L[ℂ] E :=
    fq.mkContinuous 1 (fun q => by simpa only [one_mul] using (fq_norm q).le)
  let F : HilbertModuleFibre B M t →L[ℂ] E := fqL.fromCompletion
  have F_mk (x : M) : F (hilbertModuleFibreMk (B := B) t x) = f x := by
    rw [hilbertModuleFibreMk_apply, ContinuousLinearMap.fromCompletion_apply_coe]
    rfl
  have F_norm (z : HilbertModuleFibre B M t) : ‖F z‖ = ‖z‖ := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) continuous_norm
    · intro x
      rw [F_mk, hilbertModuleFibre_norm_mk,
        CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), hf]
      rfl
  have F_inj : Function.Injective F := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [← F_norm, map_sub, hxy, sub_self, norm_zero]
  have F_surj : Function.Surjective F := by
    have hclosed : IsClosed (Set.range F) :=
      (AddMonoidHomClass.isometry_of_norm F F_norm).isClosedEmbedding.isClosed_range
    have hdense : Dense (Set.range F) :=
      hfd.mono (by
        rintro _ ⟨x, rfl⟩
        exact ⟨hilbertModuleFibreMk (B := B) t x, F_mk x⟩)
    intro y
    have hy : y ∈ closure (Set.range F) := hdense y
    rwa [hclosed.closure_eq] at hy
  refine
    { linearIsometryEquiv :=
        { toLinearEquiv := LinearEquiv.ofBijective F.toLinearMap ⟨F_inj, F_surj⟩
          norm_map' := F_norm }
      inner_map := ?_ }
  intro x y
  have hinner (p : HilbertModuleFibre B M t × HilbertModuleFibre B M t) :
      ⟪F p.1, F p.2⟫_(Bᵐᵒᵖ) = ⟪p.1, p.2⟫_(Bᵐᵒᵖ) := by
    refine ((hilbertModuleFibreMk_denseRange (B := B) (M := M) t).prodMap
      (hilbertModuleFibreMk_denseRange (B := B) (M := M) t)).induction_on p ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro q
      change ⟪F (hilbertModuleFibreMk (B := B) t q.1),
        F (hilbertModuleFibreMk (B := B) t q.2)⟫_(Bᵐᵒᵖ) =
          ⟪hilbertModuleFibreMk (B := B) t q.1, hilbertModuleFibreMk (B := B) t q.2⟫_(Bᵐᵒᵖ)
      rw [F_mk, F_mk, hilbertModuleFibre_inner_mk]
      exact hf q.1 q.2
  exact hinner (x, y)

omit [CompleteSpace M] in
@[simp] theorem hilbertModuleFibreEquivOfDenseEvaluation_mk (t : X) (f : M →L[ℂ] E)
    (hf : ∀ x y : M, ⟪f x, f y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t))
    (hfd : DenseRange f) (x : M) :
    hilbertModuleFibreEquivOfDenseEvaluation t f hf hfd (hilbertModuleFibreMk (B := B) t x) =
      f x := by
  exact ContinuousLinearMap.fromCompletion_apply_coe _ _

end DenseEvaluation

/-! ## Fibre of a projection range -/

section ProjectionFibre

theorem commute_hilbertModuleFibreOperator (t : X) {S T : AdjointableMap C(X, B) M M}
    (h : Commute S T) :
    Commute (hilbertModuleFibreOperator (B := B) t S) (hilbertModuleFibreOperator t T) := by
  rw [Commute, SemiconjBy, ← hilbertModuleFibreOperator_mul, ← hilbertModuleFibreOperator_mul,
    h.eq]

theorem isStarProjection_hilbertModuleFibreOperator (t : X) {P : AdjointableMap C(X, B) M M}
    (hP : IsStarProjection P) :
    IsStarProjection (hilbertModuleFibreOperator (B := B) t P) where
  isIdempotentElem := by
    rw [IsIdempotentElem, ← hilbertModuleFibreOperator_mul, hP.isIdempotentElem.eq]
  isSelfAdjoint := by
    rw [IsSelfAdjoint, ← hilbertModuleFibreOperator_star, hP.isSelfAdjoint.star_eq]

variable {P : AdjointableMap C(X, B) M M} (hP : IsStarProjection P) (t : X)

/-- Evaluation at `t` from the range of `P` to the range of the fibre projection `P_t`. -/
def projectionFibreEvaluation :
    ProjectionModule P →L[ℂ] ProjectionModule (hilbertModuleFibreOperator (B := B) t P) :=
  ((hilbertModuleFibreMk (B := B) t).comp (projectionFixedSubmodule P).subtypeL).codRestrict _
    (fun x => by
      change hilbertModuleFibreOperator (B := B) t P (hilbertModuleFibreMk (B := B) t (x : M)) =
        hilbertModuleFibreMk (B := B) t (x : M)
      rw [hilbertModuleFibreOperator_mk, x.property])

@[simp] theorem projectionFibreEvaluation_coe (x : ProjectionModule P) :
    (projectionFibreEvaluation (B := B) t x : HilbertModuleFibre B M t) =
      hilbertModuleFibreMk (B := B) t (x : M) := rfl

theorem projectionFibreEvaluation_inner (x y : ProjectionModule P) :
    ⟪projectionFibreEvaluation (B := B) t x, projectionFibreEvaluation (B := B) t y⟫_(Bᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(C(X, B)ᵐᵒᵖ) t) :=
  hilbertModuleFibre_inner_mk t (x : M) (y : M)

include hP in
theorem projectionFibreEvaluation_denseRange :
    DenseRange (projectionFibreEvaluation (B := B) (P := P) t) := by
  have hPt := isStarProjection_hilbertModuleFibreOperator (B := B) t hP
  let g := projectionCorestrict (hilbertModuleFibreOperator (B := B) t P) hPt
  have hg : Function.Surjective g := fun z =>
    ⟨(z : HilbertModuleFibre B M t), Subtype.ext z.property⟩
  have hdense : DenseRange (fun x : M => g (hilbertModuleFibreMk (B := B) t x)) :=
    hg.denseRange.comp (hilbertModuleFibreMk_denseRange (B := B) (M := M) t) g.toCLM.continuous
  refine hdense.mono ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨projectionCorestrict P hP x, Subtype.ext ?_⟩
  change hilbertModuleFibreMk (B := B) t (P x) =
    hilbertModuleFibreOperator (B := B) t P (hilbertModuleFibreMk (B := B) t x)
  rw [hilbertModuleFibreOperator_mk]

/-- The fibre of the range of `P` is the range of the fibre projection. -/
def projectionFibreEquiv :
    HilbertModuleEquiv B (HilbertModuleFibre B (ProjectionModule P) t)
      (ProjectionModule (hilbertModuleFibreOperator (B := B) t P)) :=
  hilbertModuleFibreEquivOfDenseEvaluation t (projectionFibreEvaluation (B := B) t)
    (projectionFibreEvaluation_inner t) (projectionFibreEvaluation_denseRange hP t)

@[simp] theorem projectionFibreEquiv_mk_coe (x : ProjectionModule P) :
    (projectionFibreEquiv hP t (hilbertModuleFibreMk (B := B) t x) : HilbertModuleFibre B M t) =
      hilbertModuleFibreMk (B := B) t (x : M) := by
  rw [projectionFibreEquiv, hilbertModuleFibreEquivOfDenseEvaluation_mk,
    projectionFibreEvaluation_coe]

end ProjectionFibre

/-! ## Even cycles -/

namespace KasparovCycle

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  (c : KasparovCycle α (β.continuousSections (X := X)) M)
  {P : AdjointableMap C(X, B) M M} (hP : c.ReducingProjection P)

/-- The fibre projection of a reducing projection reduces the fibre cycle. -/
theorem ReducingProjection.fibre {c : KasparovCycle α (β.continuousSections (X := X)) M}
    (hP : c.ReducingProjection P) (t : X) : (c.fibre t).ReducingProjection (hilbertModuleFibreOperator (B := B) t P) where
  isStarProjection := isStarProjection_hilbertModuleFibreOperator t hP.isStarProjection
  commute_operator := commute_hilbertModuleFibreOperator t hP.commute_operator
  commute_representation a := commute_hilbertModuleFibreOperator t (hP.commute_representation a)
  grading z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      simp only [hilbertModuleFibreOperator_mk, fibre_grading_mk, hP.grading]
  action g z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      simp only [hilbertModuleFibreOperator_mk, fibre_action_mk, hP.action]

/-- The fibre of the compression is the compression of the fibre. -/
def compressFibreIso (t : X) :
    KasparovCycleIso ((c.compress hP).fibre t) ((c.fibre t).compress (hP.fibre t)) where
  moduleEquiv := projectionFibreEquiv hP.isStarProjection t
  grading_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := ProjectionModule P) t).induction_on z
      ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      apply Subtype.ext
      rw [fibre_grading_mk, projectionFibreEquiv_mk_coe]
      change _ = (c.fibre t).grading.grading
        (projectionFibreEquiv hP.isStarProjection t (hilbertModuleFibreMk (B := B) t x) :
          HilbertModuleFibre B M t)
      rw [projectionFibreEquiv_mk_coe, fibre_grading_mk]
      rfl
  action_intertwine g z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := ProjectionModule P) t).induction_on z
      ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      apply Subtype.ext
      rw [fibre_action_mk, projectionFibreEquiv_mk_coe]
      change _ = (c.fibre t).groupAction.action g
        (projectionFibreEquiv hP.isStarProjection t (hilbertModuleFibreMk (B := B) t x) :
          HilbertModuleFibre B M t)
      rw [projectionFibreEquiv_mk_coe, fibre_action_mk]
      rfl
  representation_intertwine a z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := ProjectionModule P) t).induction_on z
      ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      apply Subtype.ext
      rw [fibre_representation_mk, projectionFibreEquiv_mk_coe, compress_representation_coe,
        compress_representation_coe, projectionFibreEquiv_mk_coe, fibre_representation_mk]
  operator_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := ProjectionModule P) t).induction_on z
      ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      apply Subtype.ext
      rw [fibre_operator_mk, projectionFibreEquiv_mk_coe, compress_operator_coe,
        compress_operator_coe, projectionFibreEquiv_mk_coe, fibre_operator_mk]

end KasparovCycle

/-! ## Odd cycles -/

namespace OddKasparovCycle

variable {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  (c : OddKasparovCycle α (β.continuousSections (X := X)) M)
  {P : AdjointableMap C(X, B) M M} (hP : c.ReducingProjection P)

/-- The fibre projection of a reducing projection reduces the odd fibre cycle. -/
theorem ReducingProjection.fibre {c : OddKasparovCycle α (β.continuousSections (X := X)) M}
    (hP : c.ReducingProjection P) (t : X) :
    (c.fibre t).ReducingProjection (hilbertModuleFibreOperator (B := B) t P) where
  isStarProjection := isStarProjection_hilbertModuleFibreOperator t hP.isStarProjection
  commute_operator := commute_hilbertModuleFibreOperator t hP.commute_operator
  commute_representation a := commute_hilbertModuleFibreOperator t (hP.commute_representation a)
  action g z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      simp only [hilbertModuleFibreOperator_mk, fibre_action_mk, hP.action]

/-- The fibre of the odd compression is the compression of the fibre. -/
def compressFibreIso (t : X) :
    OddKasparovCycleIso ((c.compress hP).fibre t) ((c.fibre t).compress (hP.fibre t)) where
  moduleEquiv := projectionFibreEquiv hP.isStarProjection t
  action_intertwine g z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := ProjectionModule P) t).induction_on z
      ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      apply Subtype.ext
      rw [fibre_action_mk, projectionFibreEquiv_mk_coe]
      change _ = (c.fibre t).groupAction.action g
        (projectionFibreEquiv hP.isStarProjection t (hilbertModuleFibreMk (B := B) t x) :
          HilbertModuleFibre B M t)
      rw [projectionFibreEquiv_mk_coe, fibre_action_mk]
      rfl
  representation_intertwine a z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := ProjectionModule P) t).induction_on z
      ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      apply Subtype.ext
      rw [fibre_representation_mk, projectionFibreEquiv_mk_coe, compress_representation_coe,
        compress_representation_coe, projectionFibreEquiv_mk_coe, fibre_representation_mk]
  operator_intertwine z := by
    refine (hilbertModuleFibreMk_denseRange (B := B) (M := ProjectionModule P) t).induction_on z
      ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro x
      apply Subtype.ext
      rw [fibre_operator_mk, projectionFibreEquiv_mk_coe, compress_operator_coe,
        compress_operator_coe, projectionFibreEquiv_mk_coe, fibre_operator_mk]

end OddKasparovCycle

end BC4lean.KKTheory
