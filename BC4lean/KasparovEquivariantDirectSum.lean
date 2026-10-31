import BC4lean.KasparovEquivariantRepresentative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Direct sums of reduced and equivariant cycles

A diagonal projection `P ⊕ Q` reduces a direct sum `c ⊕ d` when `P` reduces `c` and `Q` reduces
`d`, and the compression of `c ⊕ d` to `P ⊕ Q` is the direct sum of the compressions
(`compressDirectSumDiagIso`). The canonical equivariant operator of a direct sum is diagonal
(`equivariantCycleDirectSumIso`). Over trivial coefficients `∑_g U_g` is `|Γ|` times the
averaging projection (`EquivariantHilbertModule.sum_actionOperator`). -/

noncomputable section
universe uΓ uA uB uE uF
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE} {F : Type uF} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

omit [CompleteSpace E] [CompleteSpace F] in
/-- Block-diagonal maps commute with finite sums. -/
theorem sumMap_finsetSum {ι : Type*} (s : Finset ι) (f : ι → AdjointableMap B E E)
    (g : ι → AdjointableMap B F F) :
    ∑ i ∈ s, sumMap (f i) (g i) = sumMap (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi, ih, sumMap_add]

omit [CompleteSpace E] [CompleteSpace F] in
theorem commute_sumMap {S U : AdjointableMap B E E} {T V : AdjointableMap B F F}
    (h₁ : Commute S U) (h₂ : Commute T V) : Commute (sumMap S T) (sumMap U V) := by
  change sumMap S T * sumMap U V = sumMap U V * sumMap S T
  rw [← sumMap_mul, ← sumMap_mul, h₁.eq, h₂.eq]

/-! ## Even cycles -/

namespace KasparovCycle

variable {c : KasparovCycle α β E} {d : KasparovCycle α β F}
  {P : AdjointableMap B E E} {Q : AdjointableMap B F F}

/-- A diagonal projection built from reducing projections reduces the direct sum. -/
theorem ReducingProjection.directSum (hP : c.ReducingProjection P)
    (hQ : d.ReducingProjection Q) : (c.directSum d).ReducingProjection (sumMap P Q) where
  isStarProjection := by
    apply isStarProjection_iff'.mpr
    constructor
    · rw [← sumMap_mul, hP.isStarProjection.isIdempotentElem.eq,
        hQ.isStarProjection.isIdempotentElem.eq]
    · rw [← sumMap_star, hP.isStarProjection.isSelfAdjoint.star_eq,
        hQ.isStarProjection.isSelfAdjoint.star_eq]
  commute_operator := by
    change Commute (sumMap P Q) (sumMap c.operator d.operator)
    exact commute_sumMap hP.commute_operator hQ.commute_operator
  commute_representation a := by
    change Commute (sumMap P Q) (sumMap (c.representation a) (d.representation a))
    exact commute_sumMap (hP.commute_representation a) (hQ.commute_representation a)
  grading x := by
    change sumMap P Q ((c.grading.sum d.grading).grading x) =
      (c.grading.sum d.grading).grading (sumMap P Q x)
    simp only [GradedHilbertModule.sum_grading_apply, sumMap_apply, sumMk_fst, sumMk_snd,
      hP.grading, hQ.grading]
  action g x := by
    change sumMap P Q ((c.groupAction.sum d.groupAction).action g x) =
      (c.groupAction.sum d.groupAction).action g (sumMap P Q x)
    simp only [EquivariantHilbertModule.sum_action_apply, sumMap_apply, sumMk_fst, sumMk_snd,
      hP.action, hQ.action]

/-- The compression of a direct sum to a diagonal projection is the direct sum of the
compressions. -/
def compressDirectSumDiagIso (hP : c.ReducingProjection P) (hQ : d.ReducingProjection Q) :
    KasparovCycleIso ((c.directSum d).compress (hP.directSum hQ))
      ((c.compress hP).directSum (d.compress hQ)) where
  moduleEquiv := projectionSumRangeEquiv P Q
  grading_intertwine x := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  action_intertwine g x := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  representation_intertwine a x := by
    apply Prod.ext <;> apply Subtype.ext
    · change ((projectionSumRangeEquiv P Q (((c.directSum d).compress
          (hP.directSum hQ)).representation a x)).fst : E) = ((((c.compress hP).directSum (d.compress hQ)).representation a
          (projectionSumRangeEquiv P Q x)).fst : E)
      simp only [projectionSumRangeEquiv_fst, compress_representation_coe,
        KasparovCycle.directSum, sumRepresentation_apply, sumMap_apply, sumMk_fst]
    · change ((projectionSumRangeEquiv P Q (((c.directSum d).compress
          (hP.directSum hQ)).representation a x)).snd : F) = ((((c.compress hP).directSum (d.compress hQ)).representation a
          (projectionSumRangeEquiv P Q x)).snd : F)
      simp only [projectionSumRangeEquiv_snd, compress_representation_coe,
        KasparovCycle.directSum, sumRepresentation_apply, sumMap_apply, sumMk_snd]
  operator_intertwine x := by
    apply Prod.ext <;> apply Subtype.ext
    · change ((projectionSumRangeEquiv P Q (((c.directSum d).compress (hP.directSum hQ)).operator
          x)).fst : E) = ((((c.compress hP).directSum (d.compress hQ)).operator
          (projectionSumRangeEquiv P Q x)).fst : E)
      simp only [projectionSumRangeEquiv_fst, compress_operator_coe, KasparovCycle.directSum,
        sumMap_apply, sumMk_fst]
    · change ((projectionSumRangeEquiv P Q (((c.directSum d).compress (hP.directSum hQ)).operator
          x)).snd : F) = ((((c.compress hP).directSum (d.compress hQ)).operator
          (projectionSumRangeEquiv P Q x)).snd : F)
      simp only [projectionSumRangeEquiv_snd, compress_operator_coe, KasparovCycle.directSum,
        sumMap_apply, sumMk_snd]

variable [Fintype Γ]

/-- The canonical equivariant operator of a direct sum is diagonal. -/
theorem equivariantOperator_directSum (c : KasparovCycle α β E) (d : KasparovCycle α β F) :
    (c.directSum d).equivariantOperator = sumMap c.equivariantOperator d.equivariantOperator := by
  have hs : (c.directSum d).symmetrizedCycle.operator =
      sumMap c.symmetrizedCycle.operator d.symmetrizedCycle.operator := by
    change sumMap c.operator d.operator + (2 : ℂ)⁻¹ • (star (sumMap c.operator d.operator) -
      sumMap c.operator d.operator) = sumMap (c.operator + (2 : ℂ)⁻¹ • (star c.operator -
        c.operator)) (d.operator + (2 : ℂ)⁻¹ • (star d.operator - d.operator))
    rw [← sumMap_star, ← sumMap_sub, ← sumMap_smul, ← sumMap_add]
  change (Fintype.card Γ : ℂ)⁻¹ • ∑ g, (c.groupAction.sum d.groupAction).conjugateOperator g
      (c.directSum d).symmetrizedCycle.operator = sumMap ((Fintype.card Γ : ℂ)⁻¹ •
        ∑ g, c.groupAction.conjugateOperator g c.symmetrizedCycle.operator)
      ((Fintype.card Γ : ℂ)⁻¹ • ∑ g, d.groupAction.conjugateOperator g d.symmetrizedCycle.operator)
  simp only [hs, EquivariantHilbertModule.sum_conjugateOperator]
  rw [sumMap_finsetSum, sumMap_smul]

/-- The canonical representative of a direct sum is the direct sum of the canonical
representatives. -/
def equivariantCycleDirectSumIso (c : KasparovCycle α β E) (d : KasparovCycle α β F) :
    KasparovCycleIso (c.directSum d).equivariantCycle
      (c.equivariantCycle.directSum d.equivariantCycle) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine x := by
    change (c.directSum d).equivariantOperator x =
      sumMap c.equivariantOperator d.equivariantOperator x
    rw [equivariantOperator_directSum]

end KasparovCycle

section EigenSum

variable [β.IsTrivial]

omit [CompleteSpace E] [CompleteSpace F] in
theorem EquivariantHilbertModule.sum_actionOperator (U : EquivariantHilbertModule β E)
    (V : EquivariantHilbertModule β F) (g : Γ) :
    (U.sum V).actionOperator g = sumMap (U.actionOperator g) (V.actionOperator g) := by
  ext x
  apply Prod.ext <;>
    simp only [EquivariantHilbertModule.actionOperator_apply,
      EquivariantHilbertModule.sum_action_apply, sumMap_apply, sumMk_fst, sumMk_snd]

end EigenSum

/-! ## Odd cycles -/

namespace OddKasparovCycle

variable {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}
  {P : AdjointableMap B E E} {Q : AdjointableMap B F F}

/-- A diagonal projection built from reducing projections reduces the direct sum. -/
theorem ReducingProjection.directSum (hP : c.ReducingProjection P)
    (hQ : d.ReducingProjection Q) : (c.directSum d).ReducingProjection (sumMap P Q) where
  isStarProjection := by
    apply isStarProjection_iff'.mpr
    constructor
    · rw [← sumMap_mul, hP.isStarProjection.isIdempotentElem.eq,
        hQ.isStarProjection.isIdempotentElem.eq]
    · rw [← sumMap_star, hP.isStarProjection.isSelfAdjoint.star_eq,
        hQ.isStarProjection.isSelfAdjoint.star_eq]
  commute_operator := by
    change Commute (sumMap P Q) (sumMap c.operator d.operator)
    exact commute_sumMap hP.commute_operator hQ.commute_operator
  commute_representation a := by
    change Commute (sumMap P Q) (sumMap (c.representation a) (d.representation a))
    exact commute_sumMap (hP.commute_representation a) (hQ.commute_representation a)
  action g x := by
    change sumMap P Q ((c.groupAction.sum d.groupAction).action g x) =
      (c.groupAction.sum d.groupAction).action g (sumMap P Q x)
    simp only [EquivariantHilbertModule.sum_action_apply, sumMap_apply, sumMk_fst, sumMk_snd,
      hP.action, hQ.action]

/-- The compression of a direct sum to a diagonal projection is the direct sum of the
compressions. -/
def compressDirectSumDiagIso (hP : c.ReducingProjection P) (hQ : d.ReducingProjection Q) :
    OddKasparovCycleIso ((c.directSum d).compress (hP.directSum hQ))
      ((c.compress hP).directSum (d.compress hQ)) where
  moduleEquiv := projectionSumRangeEquiv P Q
  action_intertwine g x := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  representation_intertwine a x := by
    apply Prod.ext <;> apply Subtype.ext
    · change ((projectionSumRangeEquiv P Q (((c.directSum d).compress
          (hP.directSum hQ)).representation a x)).fst : E) =
        ((((c.compress hP).directSum (d.compress hQ)).representation a
          (projectionSumRangeEquiv P Q x)).fst : E)
      simp only [projectionSumRangeEquiv_fst, compress_representation_coe,
        OddKasparovCycle.directSum, sumRepresentation_apply, sumMap_apply, sumMk_fst]
    · change ((projectionSumRangeEquiv P Q (((c.directSum d).compress
          (hP.directSum hQ)).representation a x)).snd : F) =
        ((((c.compress hP).directSum (d.compress hQ)).representation a
          (projectionSumRangeEquiv P Q x)).snd : F)
      simp only [projectionSumRangeEquiv_snd, compress_representation_coe,
        OddKasparovCycle.directSum, sumRepresentation_apply, sumMap_apply, sumMk_snd]
  operator_intertwine x := by
    apply Prod.ext <;> apply Subtype.ext
    · change ((projectionSumRangeEquiv P Q (((c.directSum d).compress (hP.directSum hQ)).operator
          x)).fst : E) = ((((c.compress hP).directSum (d.compress hQ)).operator
          (projectionSumRangeEquiv P Q x)).fst : E)
      simp only [projectionSumRangeEquiv_fst, compress_operator_coe, OddKasparovCycle.directSum,
        sumMap_apply, sumMk_fst]
    · change ((projectionSumRangeEquiv P Q (((c.directSum d).compress (hP.directSum hQ)).operator
          x)).snd : F) = ((((c.compress hP).directSum (d.compress hQ)).operator
          (projectionSumRangeEquiv P Q x)).snd : F)
      simp only [projectionSumRangeEquiv_snd, compress_operator_coe, OddKasparovCycle.directSum,
        sumMap_apply, sumMk_snd]

variable [Fintype Γ]

/-- The canonical equivariant operator of a direct sum is diagonal. -/
theorem equivariantOperator_directSum (c : OddKasparovCycle α β E)
    (d : OddKasparovCycle α β F) :
    (c.directSum d).equivariantOperator = sumMap c.equivariantOperator d.equivariantOperator := by
  have hs : (c.directSum d).symmetrized.operator =
      sumMap c.symmetrized.operator d.symmetrized.operator := by
    change sumMap c.operator d.operator + (2 : ℂ)⁻¹ • (star (sumMap c.operator d.operator) -
      sumMap c.operator d.operator) = sumMap (c.operator + (2 : ℂ)⁻¹ • (star c.operator -
        c.operator)) (d.operator + (2 : ℂ)⁻¹ • (star d.operator - d.operator))
    rw [← sumMap_star, ← sumMap_sub, ← sumMap_smul, ← sumMap_add]
  change (Fintype.card Γ : ℂ)⁻¹ • ∑ g, (c.groupAction.sum d.groupAction).conjugateOperator g
      (c.directSum d).symmetrized.operator = sumMap ((Fintype.card Γ : ℂ)⁻¹ •
        ∑ g, c.groupAction.conjugateOperator g c.symmetrized.operator)
      ((Fintype.card Γ : ℂ)⁻¹ • ∑ g, d.groupAction.conjugateOperator g d.symmetrized.operator)
  simp only [hs, EquivariantHilbertModule.sum_conjugateOperator]
  rw [sumMap_finsetSum, sumMap_smul]

/-- The canonical representative of a direct sum is the direct sum of the canonical
representatives. -/
def equivariantCycleDirectSumIso (c : OddKasparovCycle α β E) (d : OddKasparovCycle α β F) :
    OddKasparovCycleIso (c.directSum d).equivariantCycle
      (c.equivariantCycle.directSum d.equivariantCycle) where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine x := by
    change (c.directSum d).equivariantOperator x =
      sumMap c.equivariantOperator d.equivariantOperator x
    rw [equivariantOperator_directSum]

end OddKasparovCycle

end BC4lean.KKTheory
