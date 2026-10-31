import BC4lean.GroupIsoDescent
import BC4lean.GroupIsoKHomology
import BC4lean.BaumConnesProperty
import BC4lean.NativeEvenSourcePullback
import BC4lean.NativeOddSourcePullback
import BC4lean.AssemblyColimit
import BC4lean.AssemblyPieceHom
import BC4lean.ScalarKKNativeNaturality
import BC4lean.CutoffRestrictionNaturality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Group-isomorphism invariance of the Baum–Connes property

The relabelling square on each cocompact piece, hence for the telescope, and
`BC4lean.Assembly.baumConnesProperty_congr`: reduced Baum–Connes holds for `Γ` iff it holds for any
isomorphic `Γ'` in the same universe.
-/

noncomputable section

/-! ## Reduction of `baumConnesProperty_congr` to one relabelling square

For `e : Γ ≃* Γ'` and a proper `Γ'`-space `X`, the *relabelling square* in degree `p` asks for an
additive bijection `φ : K^Γ_p(e* X) ≃ K^{Γ'}_p(X)` with `μ_{Γ'} ∘ φ = ψ_p ∘ μ_Γ`, where `ψ_p` is the
analytic relabelling `analyticGroupEquiv e p`. Given the square for the
telescope `Model Γ'` in both degrees, the canonical assembly maps of `Γ` and `Γ'` are bijective
together: by `reducedAssemblyHom_bijective_iff_pull` canonical assembly of `Γ` may be
computed on `e* (Model Γ')`, and the square transports bijectivity across `φ` and `ψ_p`.

The square itself is `relabelSquare_of_pieces` with `pieceSquare`; the theorem is
`BC4lean.Assembly.baumConnesProperty_congr`.
-/

namespace BC4lean.KKTheory.GroupIso
universe u
open ProperActions

private theorem bijective_iff_of_equiv' {A B C D : Type*}
    (f : A → C) (g : B → D) (φ : A ≃ B) (ψ : C ≃ D) (h : ∀ x, g (φ x) = ψ (f x)) :
    Function.Bijective f ↔ Function.Bijective g := by
  have hg : g = ψ ∘ f ∘ φ.symm := by
    funext y
    simp only [Function.comp_apply, ← h, Equiv.apply_symm_apply]
  rw [hg, Equiv.comp_bijective, Equiv.bijective_comp]

variable {Γ Γ' : Type u} [Group Γ] [Group Γ'] [Countable Γ] [Countable Γ']
  [TopologicalSpace Γ] [DiscreteTopology Γ] [TopologicalSpace Γ'] [DiscreteTopology Γ']
  (e : Γ ≃* Γ')

/-- The relabelling square for a proper `Γ'`-space `X` in degree `p`. -/
def RelabelSquare (X : Type u) [TopologicalSpace X] [MulAction Γ' X]
    [ContinuousConstSMul Γ' X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] [ProperSMul Γ' X] (p : Bool) : Prop :=
  ∃ φ : TopologicalKHomology.group (Γ := Γ) (X := Pull e X) p ≃+
      TopologicalKHomology.group (Γ := Γ') (X := X) p,
    ∀ x, Assembly.assemblyHom Γ' X p (φ x) =
      analyticGroupEquiv e p (Assembly.assemblyHom Γ (Pull e X) p x)

/-- `baumConnesProperty_congr`, conditional on the relabelling square for the telescope of `Γ'`
in both degrees. -/
theorem baumConnesProperty_congr_of_square
    (h : ∀ p, letI : ProperSMul Γ' (LabeledOrbitTelescope.Model Γ') := LabeledOrbitTelescope.proper Γ'
      RelabelSquare e (LabeledOrbitTelescope.Model Γ') p) :
    Assembly.BaumConnesProperty Γ ↔ Assembly.BaumConnesProperty Γ' := by
  let _ : ProperSMul Γ' (LabeledOrbitTelescope.Model Γ') := LabeledOrbitTelescope.proper Γ'
  refine forall_congr' fun p => ?_
  rw [reducedAssemblyHom_bijective_iff_pull e p]
  obtain ⟨φ, hφ⟩ := h p
  exact bijective_iff_of_equiv' _ _ φ.toEquiv (analyticGroupEquiv e p).toEquiv hφ

end BC4lean.KKTheory.GroupIso

/-! ## The relabelling square from the pieces -/

namespace BC4lean.KKTheory.GroupIso
open scoped ZeroAtInfty ComplexOrder
open KKTheory.GroupRestriction
open KKTheory KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open ProperActions

section Square
universe u
variable {Γ Γ' : Type u} [Group Γ] [Group Γ'] [Countable Γ] [Countable Γ']
  [TopologicalSpace Γ] [DiscreteTopology Γ] [TopologicalSpace Γ'] [DiscreteTopology Γ']
  (e : Γ ≃* Γ')
  (X : Type u) [TopologicalSpace X] [MulAction Γ' X] [ContinuousConstSMul Γ' X]
  [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] [ProperSMul Γ' X]

/-- The square on pieces: for every `Γ'`-piece `S`, assembly of `Γ'` on `S` is assembly of `Γ` on
the relabelled piece followed by the analytic relabelling. -/
def PieceSquare (p : Bool) : Prop :=
  ∀ (S : CocompactPiece Γ' X) (x : TopologicalKHomology.pieceGroup p S),
    analyticGroupEquiv e p
        (Assembly.pieceAssemblyHom Γ (Pull e X) p ((pieceRelabel e X).symm S)
          (pieceEquiv e X p S x)) =
      Assembly.pieceAssemblyHom Γ' X p S x

/-- The square on pieces gives the relabelling square. -/
theorem relabelSquare_of_pieces (p : Bool) (h : PieceSquare e X p) : RelabelSquare e X p := by
  refine ⟨(groupRelabel e X p).symm, fun z => ?_⟩
  have key := colimitEquiv_comp_eq (D := TopologicalKHomology.diagram (Γ := Γ') (X := X) p)
    (E := TopologicalKHomology.diagram (Γ := Γ) (X := Pull e X) p)
    (pieceRelabel e X).symm (pieceEquiv e X p)
    (fun _ _ hij x => pieceEquiv_transition e X p hij x)
    (Assembly.assemblyHom Γ' X p)
    ((analyticGroupEquiv e p).toAddMonoidHom.comp (Assembly.assemblyHom Γ (Pull e X) p))
    (fun S x => h S x) ((groupRelabel e X p).symm z)
  have hz : colimitEquiv (D := TopologicalKHomology.diagram (Γ := Γ') (X := X) p)
      (E := TopologicalKHomology.diagram (Γ := Γ) (X := Pull e X) p)
      (pieceRelabel e X).symm (pieceEquiv e X p)
      (fun _ _ hij x => pieceEquiv_transition e X p hij x) ((groupRelabel e X p).symm z) = z :=
    (groupRelabel e X p).apply_symm_apply z
  rw [hz] at key
  exact key.symm

end Square

end BC4lean.KKTheory.GroupIso

/-! ## The cutoff class under the crossed-product isomorphism

A cutoff function `c` for `Γ'` on `Y` is a cutoff function for `Γ` on `e* Y` (`cutoffPull`): the
normalization sum over `Γ` is the sum over `Γ'` reindexed by `e`. The isomorphism
`Φ : C₀(Y) ⋊ Γ ≅ C₀(Y) ⋊ Γ'` sends a finite element `∑ a_g u_g` to `∑ a_g u_{e g}`
(`crossedProductEquiv_algebraic`), so it sends the cutoff projection of `cutoffPull c` to that of
`c`. Hence it sends the cutoff K₀ class and the cutoff KK class of `Γ` to those of `Γ'`.

The action of `Γ` on `C₀(e* Y)` is the restriction of that of `Γ'` only propositionally (`cZeroAction_pull`), so
`Φ` is also given in a form `crossedProductEquiv'` that takes the equality of actions as an
argument; it is `crossedProductEquiv` when that argument is `rfl`.
-/

namespace BC4lean.KKTheory.GroupIso
open scoped ZeroAtInfty ComplexOrder CompactlySupported
open KKTheory.GroupRestriction
open KKTheory OperatorKTheory ProperActions ProperActions.Cutoff
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open scoped KasparovDescent

section Cutoff
universe u
variable {Γ Γ' : Type u} [Group Γ] [Group Γ'] [Countable Γ] [Countable Γ'] (e : Γ ≃* Γ')
  {Y : Type u} [TopologicalSpace Y] [MulAction Γ' Y]

/-- A cutoff function for `Γ'` on `Y` is one for `Γ` on `e* Y`. -/
def cutoffPull (c : CutoffFunction Γ' Y) : CutoffFunction Γ (Pull e Y) where
  toCompactlySupportedContinuousMap := c.toCompactlySupportedContinuousMap
  nonneg x := c.nonneg x
  normalized x := by
    change (∑ᶠ g : Γ, c ((e g⁻¹) • (show Y from x)) ^ 2) = 1
    calc (∑ᶠ g : Γ, c ((e g⁻¹) • (show Y from x)) ^ 2)
        = ∑ᶠ g : Γ, c ((e.toEquiv g)⁻¹ • (show Y from x)) ^ 2 := by
          apply finsum_congr
          intro g
          exact congrArg (fun h : Γ' => c (h • (show Y from x)) ^ 2) (map_inv e g)
      _ = ∑ᶠ g' : Γ', c (g'⁻¹ • (show Y from x)) ^ 2 :=
          finsum_comp_equiv e.toEquiv (f := fun g' : Γ' => c (g'⁻¹ • (show Y from x)) ^ 2)
      _ = 1 := c.normalized x

variable [TopologicalSpace Γ] [DiscreteTopology Γ] [TopologicalSpace Γ'] [DiscreteTopology Γ']
  [ContinuousConstSMul Γ' Y] [ProperSMul Γ' Y]

omit [Countable Γ] [Countable Γ'] in
/-- Relabelling takes the algebraic cutoff projection of `cutoffPull c` to that of `c`. -/
theorem algRelabel_algebraicProjection (c : CutoffFunction Γ' Y) :
    algRelabel e (CZero.action Γ' (X := Y)) (CZero.action Γ (X := Pull e Y))
        (algebraicProjection (cutoffPull e c)) =
      algebraicProjection c := by
  apply AlgebraicCrossedProduct.ext (CZero.action Γ' (X := Y))
  intro g'
  obtain ⟨g, rfl⟩ := e.surjective g'
  refine (coeff_algRelabel e (CZero.action Γ' (X := Y)) (CZero.action Γ (X := Pull e Y))
    (algebraicProjection (cutoffPull e c)) g).trans ?_
  apply ZeroAtInftyContinuousMap.ext
  intro x
  change (((c (show Y from x) * c ((e g⁻¹) • (show Y from x)) : ℝ)) : ℂ) =
    ((c (show Y from x) * c ((e g)⁻¹ • (show Y from x)) : ℝ) : ℂ)
  rw [map_inv]

variable [LocallyCompactSpace Y]

omit [LocallyCompactSpace Y] [Countable Γ] [Countable Γ'] in
/-- The cutoff projection of `Γ` maps to that of `Γ'`. -/
theorem reducedCutoffProjection_pull (c : CutoffFunction Γ' Y) :
    crossedProductEquiv' e (CZero.action Γ' (X := Y)) (CZero.action Γ (X := Pull e Y))
        (cZeroAction_pull e Y).symm (reducedCutoffProjection (cutoffPull e c)) =
      reducedCutoffProjection c :=
  (crossedProductEquiv'_algebraic e (CZero.action Γ' (X := Y)) (CZero.action Γ (X := Pull e Y))
    (cZeroAction_pull e Y).symm (algebraicProjection (cutoffPull e c))).trans
    (congrArg (algebraicToReducedCrossed (CZero.action Γ' (X := Y)))
      (algRelabel_algebraicProjection e c))

private theorem projectionK0_congr {D : Type*} [NonUnitalCStarAlgebra D]
    {p q : D} {hp : IsStarProjection p} {hq : IsStarProjection q} (h : p = q) :
    nonunitalProjectionK0 p hp = nonunitalProjectionK0 q hq := by
  cases h
  rfl

/-- A star homomorphism sending one projection to another sends its K₀ class to the other's. -/
theorem projectionK0_map_eq {D D' : Type*} [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra D']
    (φ : D →⋆ₙₐ[ℂ] D') {p : D} {q : D'} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : φ p = q) : operatorK0Map φ (nonunitalProjectionK0 p hp) = nonunitalProjectionK0 q hq :=
  (nonunitalProjectionK0_map φ p hp).trans (projectionK0_congr h)

omit [Countable Γ] [Countable Γ'] in
/-- The cutoff K₀ class of `Γ` maps to that of `Γ'`. -/
theorem cutoffK0_pull (c : CutoffFunction Γ' Y) (cΓ : CutoffFunction Γ (Pull e Y)) :
    operatorK0Map (crossedProductEquiv' e (CZero.action Γ' (X := Y))
        (CZero.action Γ (X := Pull e Y)) (cZeroAction_pull e Y).symm).toNonUnitalStarAlgHom
        (cutoffK0 cΓ) = cutoffK0 c := by
  rw [cutoffK0_independent cΓ (cutoffPull e c)]
  exact projectionK0_map_eq _ (reducedCutoffProjection_isStarProjection (cutoffPull e c))
    (reducedCutoffProjection_isStarProjection c) (reducedCutoffProjection_pull e c)

variable [SecondCountableTopology Y] [T2Space Y]

local instance cZero_separable : TopologicalSpace.SeparableSpace C₀(Y, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

/-- The cutoff KK class: `Φ_*` of the cutoff class of `Γ` on `e* Y` is the cutoff class of `Γ'` on
`Y`. Pattern: upstream `cutoffKKClass_properPullback`. -/
theorem cutoffKKClass_pull (c : CutoffFunction Γ' Y) (cΓ : CutoffFunction Γ (Pull e Y)) :
    coefficientPushforward.{0, 0, u, u, u} false
      (crossedProductEquiv' e (CZero.action Γ' (X := Y)) (CZero.action Γ (X := Pull e Y))
        (cZeroAction_pull e Y).symm).toNonUnitalStarAlgHom
      (crossedProductEquiv'_trivial e (CZero.action Γ' (X := Y)) (CZero.action Γ (X := Pull e Y))
        (cZeroAction_pull e Y).symm) (Assembly.cutoffKKClass Γ (Pull e Y) cΓ) =
      Assembly.cutoffKKClass Γ' Y c := by
  apply (scalarKKOperatorK0AddEquiv.{u, u}).injective
  let φ := (crossedProductEquiv' e (CZero.action Γ' (X := Y)) (CZero.action Γ (X := Pull e Y))
    (cZeroAction_pull e Y).symm).toNonUnitalStarAlgHom
  have hn := Assembly.scalarKKOperatorK0_native_coefficient_natural.{u, u, u}
    (B := ReducedCrossedProduct (CZero.action Γ (X := Pull e Y)))
    (C := ReducedCrossedProduct (CZero.action Γ' (X := Y)))
    φ (Assembly.cutoffKKClass Γ (Pull e Y) cΓ)
  have hP : scalarKKOperatorK0AddEquiv.{u, u} (Assembly.cutoffKKClass Γ (Pull e Y) cΓ) =
      cutoffK0 cΓ :=
    (scalarKKOperatorK0AddEquiv.{u, u}).apply_symm_apply (cutoffK0 cΓ)
  have hY : scalarKKOperatorK0AddEquiv.{u, u} (Assembly.cutoffKKClass Γ' Y c) = cutoffK0 c :=
    (scalarKKOperatorK0AddEquiv.{u, u}).apply_symm_apply (cutoffK0 c)
  rw [hn, hP, hY]
  exact cutoffK0_pull e c cΓ

end Cutoff

end BC4lean.KKTheory.GroupIso

/-! ## The relabelling square, and `baumConnesProperty_congr`

For a `Γ'`-coefficient algebra `A` with action `α`, a class `κ ∈ KK(ℂ, A ⋊ (α∘e) Γ)` and
`x ∈ KK^{Γ'}_p(A, ℂ)`:

  R_Γ'([Φ_A]_* κ ⊗ j_Γ'(x)) = R_Γ'(κ ⊗ Φ_A^* j_Γ'(x))      (product balancing, upstream)
                           = R_Γ'(κ ⊗ (Φ_ℂ)_* j_Γ(res x))  (descent)
                           = R_Γ'((Φ_ℂ)_* (κ ⊗ j_Γ(res x)))  (product associativity, upstream)
                           = ψ(R_Γ(κ ⊗ j_Γ(res x)))         (scalar square)

(`square_core_even/odd`). `square_general_even/odd` replace `α∘e` by any equal action, by `subst`; with
`κ` the cutoff class of `Γ` and `[Φ_A]_* κ` the cutoff class of `Γ'` (`cutoffKKClass_pull`) this is the square on
each cocompact piece (`pieceSquare`), hence the relabelling square (`relabelSquare_of_pieces`) and the theorem.
-/

namespace BC4lean.KKTheory.GroupIso
open scoped ZeroAtInfty ComplexOrder
open KKTheory.GroupRestriction
open KKTheory OperatorKTheory ProperActions
open KKTheory.KasparovDescent
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open scoped KasparovDescent

section Core
universe u
variable {Γ Γ' : Type u} [Group Γ] [Group Γ'] [Countable Γ] [Countable Γ'] (e : Γ ≃* Γ')
  {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace.SeparableSpace A] (α : CStarAlgebraAction Γ' A)

/-- The square in even degree, before replacing `α∘e` by an equal action. -/
theorem square_core_even
    (κ : KKParityGroup.{0, 0, u, u} false (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ) (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
      (ReducedCrossedProduct (actionComap e.toMonoidHom α))))
    (x : KKParityGroup.{u, u, 0, u} false α (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)) :
    Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' false
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false false
          (coefficientPushforward.{0, 0, u, u, u} false (crossedProductEquiv e α).toNonUnitalStarAlgHom
            (crossedProductEquiv_trivial e α) κ)
          (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ) α false x)) =
      analyticGroupEquiv e false (Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ false
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false false κ
          (classHom (actionComap e.toMonoidHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)) (actionComap e.toMonoidHom α) false
            (parityComap e.toMonoidHom false x)))) := by
  have s1 := coefficientPushforward_product_eq_sourcePullback.{0, 0, u, u, u, u} false false
    (crossedProductEquiv e α).toNonUnitalStarAlgHom (crossedProductEquiv_trivial e α) κ
    (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ) α false x)
  have s2 := evenDescent_parity.{u, u, 0, u} e α (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ) x
  have s3 := coefficientPushforward_product.{0, 0, u, u, u, u} false false (crossedProductHom e (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ))
    (crossedProductHom_trivial e (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)) κ
    (classHom (actionComap e.toMonoidHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)) (actionComap e.toMonoidHom α) false
      (parityComap e.toMonoidHom false x))
  have s4 := analytic_natural_even e
    (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false false κ
      (classHom (actionComap e.toMonoidHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)) (actionComap e.toMonoidHom α) false
        (parityComap e.toMonoidHom false x)))
  exact (congrArg (Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' false) s1).trans
    ((congrArg (fun t => Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' false
      (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false false κ t)) s2.symm).trans
    ((congrArg (Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' false) s3.symm).trans s4))

/-- The square in odd degree, before replacing `α∘e` by an equal action. -/
theorem square_core_odd
    (κ : KKParityGroup.{0, 0, u, u} false (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ) (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
      (ReducedCrossedProduct (actionComap e.toMonoidHom α))))
    (x : KKParityGroup.{u, u, 0, u} true α (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)) :
    Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' true
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false true
          (coefficientPushforward.{0, 0, u, u, u} false (crossedProductEquiv e α).toNonUnitalStarAlgHom
            (crossedProductEquiv_trivial e α) κ)
          (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ) α true x)) =
      analyticGroupEquiv e true (Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ true
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false true κ
          (classHom (actionComap e.toMonoidHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)) (actionComap e.toMonoidHom α) true
            (parityComap e.toMonoidHom true x)))) := by
  have s1 := coefficientPushforward_product_eq_sourcePullback.{0, 0, u, u, u, u} false true
    (crossedProductEquiv e α).toNonUnitalStarAlgHom (crossedProductEquiv_trivial e α) κ
    (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ) α true x)
  have s2 := oddDescent_parity.{u, u, 0, u} e α (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ) x
  have s3 := coefficientPushforward_product.{0, 0, u, u, u, u} false true (crossedProductHom e (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ))
    (crossedProductHom_trivial e (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)) κ
    (classHom (actionComap e.toMonoidHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)) (actionComap e.toMonoidHom α) true
      (parityComap e.toMonoidHom true x))
  have s4 := analytic_natural_odd e
    (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false true κ
      (classHom (actionComap e.toMonoidHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)) (actionComap e.toMonoidHom α) true
        (parityComap e.toMonoidHom true x)))
  exact (congrArg (Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' true) s1).trans
    ((congrArg (fun t => Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' true
      (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false true κ t)) s2.symm).trans
    ((congrArg (Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' true) s3.symm).trans s4))

/-- The square for any action `αΓ` equal to `α∘e` and any `κ` whose image under `Φ_A` is `κ'`. -/
theorem square_general_even (αΓ : CStarAlgebraAction Γ A)
    (hα : actionComap e.toMonoidHom α = αΓ)
    (κ : KKParityGroup.{0, 0, u, u} false (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct αΓ)))
    (κ' : KKParityGroup.{0, 0, u, u} false (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α)))
    (hκ : coefficientPushforward.{0, 0, u, u, u} false
      (crossedProductEquiv' e α αΓ hα).toNonUnitalStarAlgHom (crossedProductEquiv'_trivial e α αΓ hα)
      κ = κ')
    (x : KKParityGroup.{u, u, 0, u} false α (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)) :
    Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' false
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false false κ' (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ) α false x)) =
      analyticGroupEquiv e false (Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ false
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false false κ
          (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) αΓ false (parityRelabel e false hα (actionComap_trivial e.toMonoidHom) x)))) := by
  subst hα
  subst hκ
  exact square_core_even e α κ x

/-- The square for any action `αΓ` equal to `α∘e` and any `κ` whose image under `Φ_A` is `κ'`. -/
theorem square_general_odd (αΓ : CStarAlgebraAction Γ A)
    (hα : actionComap e.toMonoidHom α = αΓ)
    (κ : KKParityGroup.{0, 0, u, u} false (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct αΓ)))
    (κ' : KKParityGroup.{0, 0, u, u} false (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct α)))
    (hκ : coefficientPushforward.{0, 0, u, u, u} false
      (crossedProductEquiv' e α αΓ hα).toNonUnitalStarAlgHom (crossedProductEquiv'_trivial e α αΓ hα)
      κ = κ')
    (x : KKParityGroup.{u, u, 0, u} true α (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)) :
    Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' true
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false true κ' (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ) α true x)) =
      analyticGroupEquiv e true (Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ true
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false true κ
          (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) αΓ true (parityRelabel e true hα (actionComap_trivial e.toMonoidHom) x)))) := by
  subst hα
  subst hκ
  exact square_core_odd e α κ x

end Core

section Pieces
universe u
variable {Γ Γ' : Type u} [Group Γ] [Group Γ'] [Countable Γ] [Countable Γ']
  [TopologicalSpace Γ] [DiscreteTopology Γ] [TopologicalSpace Γ'] [DiscreteTopology Γ']
  (e : Γ ≃* Γ')
  (X : Type u) [TopologicalSpace X] [MulAction Γ' X] [ContinuousConstSMul Γ' X]
  [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] [ProperSMul Γ' X]

local instance sq_piece_locallyCompact' (S : CocompactPiece Γ' X) :
    LocallyCompactSpace S.toInvariantSubset := S.locallyCompact

local instance sq_piece_locallyCompact (S : CocompactPiece Γ (Pull e X)) :
    LocallyCompactSpace S.toInvariantSubset := S.locallyCompact

local instance sq_piece_separable' (S : CocompactPiece Γ' X) :
    TopologicalSpace.SeparableSpace C₀(S.toInvariantSubset, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

/-- The `Γ`-space of a relabelled piece is `e*` of the `Γ'`-piece, definitionally (needed to use
the cutoff lemmas, which are stated for `Pull e Y`). -/
example (S : CocompactPiece Γ' X) :
    (CZero.action Γ (X := ((pieceRelabel e X).symm S).toInvariantSubset) :
      CStarAlgebraAction Γ C₀(S.toInvariantSubset, ℂ)) =
      CZero.action Γ (X := Pull e S.toInvariantSubset) := rfl

omit [Countable Γ'] in
theorem pieceAssemblyHom_relabel_even (S : CocompactPiece Γ' X)
    (x : TopologicalKHomology.pieceGroup false S) :
    Assembly.pieceAssemblyHom Γ (Pull e X) false ((pieceRelabel e X).symm S)
        (pieceEquiv e X false S x) =
      Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ false
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false false
          (Assembly.cutoffKKClass Γ ((pieceRelabel e X).symm S).toInvariantSubset
            (Assembly.pieceCutoff Γ (Pull e X) ((pieceRelabel e X).symm S)))
          (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
            (CZero.action Γ (X := ((pieceRelabel e X).symm S).toInvariantSubset)) false
            (pieceEquiv e X false S x))) :=
  rfl

theorem pieceAssemblyHom_even (S : CocompactPiece Γ' X)
    (x : TopologicalKHomology.pieceGroup false S) :
    Assembly.pieceAssemblyHom Γ' X false S x =
      Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' false
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false false
          (Assembly.cutoffKKClass Γ' S.toInvariantSubset (Assembly.pieceCutoff Γ' X S))
          (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)
            (CZero.action Γ' (X := S.toInvariantSubset)) false x)) :=
  rfl

/-- The square on a piece, with the assembly maps unfolded (even degree). -/
theorem pieceSquare_even_core (S : CocompactPiece Γ' X)
    (x : TopologicalKHomology.pieceGroup false S) :
    analyticGroupEquiv e false
        (Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ false
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false false
          (Assembly.cutoffKKClass Γ ((pieceRelabel e X).symm S).toInvariantSubset
            (Assembly.pieceCutoff Γ (Pull e X) ((pieceRelabel e X).symm S)))
          (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
            (CZero.action Γ (X := ((pieceRelabel e X).symm S).toInvariantSubset)) false
            (parityRelabel e false (pieceAction_pull e X S) (actionComap_trivial e.toMonoidHom) x)))) =
      Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' false
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false false
          (Assembly.cutoffKKClass Γ' S.toInvariantSubset (Assembly.pieceCutoff Γ' X S))
          (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)
            (CZero.action Γ' (X := S.toInvariantSubset)) false x)) :=
  (@square_general_even _ _ _ _ _ _ e C₀(S.toInvariantSubset, ℂ) _
      (CZero.instPartialOrder (X := S.toInvariantSubset))
      (CZero.instStarOrderedRing (X := S.toInvariantSubset)) _
      (CZero.action Γ' (X := S.toInvariantSubset))
      (CZero.action Γ (X := ((pieceRelabel e X).symm S).toInvariantSubset) :
        CStarAlgebraAction Γ C₀(S.toInvariantSubset, ℂ))
      (pieceAction_pull e X S)
      (Assembly.cutoffKKClass Γ ((pieceRelabel e X).symm S).toInvariantSubset
        (Assembly.pieceCutoff Γ (Pull e X) ((pieceRelabel e X).symm S)) :
        KKParityGroup.{0, 0, u, u} false (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
          (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct
            (CZero.action Γ (X := ((pieceRelabel e X).symm S).toInvariantSubset) :
              CStarAlgebraAction Γ C₀(S.toInvariantSubset, ℂ)))))
      (Assembly.cutoffKKClass Γ' S.toInvariantSubset (Assembly.pieceCutoff Γ' X S))
      (cutoffKKClass_pull e (Y := S.toInvariantSubset) (Assembly.pieceCutoff Γ' X S)
        (Assembly.pieceCutoff Γ (Pull e X) ((pieceRelabel e X).symm S))) x).symm

omit [Countable Γ'] in
theorem pieceAssemblyHom_relabel_odd (S : CocompactPiece Γ' X)
    (x : TopologicalKHomology.pieceGroup true S) :
    Assembly.pieceAssemblyHom Γ (Pull e X) true ((pieceRelabel e X).symm S)
        (pieceEquiv e X true S x) =
      Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ true
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false true
          (Assembly.cutoffKKClass Γ ((pieceRelabel e X).symm S).toInvariantSubset
            (Assembly.pieceCutoff Γ (Pull e X) ((pieceRelabel e X).symm S)))
          (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
            (CZero.action Γ (X := ((pieceRelabel e X).symm S).toInvariantSubset)) true
            (pieceEquiv e X true S x))) :=
  rfl

theorem pieceAssemblyHom_odd (S : CocompactPiece Γ' X)
    (x : TopologicalKHomology.pieceGroup true S) :
    Assembly.pieceAssemblyHom Γ' X true S x =
      Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' true
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false true
          (Assembly.cutoffKKClass Γ' S.toInvariantSubset (Assembly.pieceCutoff Γ' X S))
          (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)
            (CZero.action Γ' (X := S.toInvariantSubset)) true x)) :=
  rfl

/-- The square on a piece, with the assembly maps unfolded (odd degree). -/
theorem pieceSquare_odd_core (S : CocompactPiece Γ' X)
    (x : TopologicalKHomology.pieceGroup true S) :
    analyticGroupEquiv e true
        (Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ true
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false true
          (Assembly.cutoffKKClass Γ ((pieceRelabel e X).symm S).toInvariantSubset
            (Assembly.pieceCutoff Γ (Pull e X) ((pieceRelabel e X).symm S)))
          (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
            (CZero.action Γ (X := ((pieceRelabel e X).symm S).toInvariantSubset)) true
            (parityRelabel e true (pieceAction_pull e X S) (actionComap_trivial e.toMonoidHom) x)))) =
      Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' true
        (GroupUniverseCommonParityProduct.product.{0, 0, u, u, u} false true
          (Assembly.cutoffKKClass Γ' S.toInvariantSubset (Assembly.pieceCutoff Γ' X S))
          (classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)
            (CZero.action Γ' (X := S.toInvariantSubset)) true x)) :=
  (@square_general_odd _ _ _ _ _ _ e C₀(S.toInvariantSubset, ℂ) _
      (CZero.instPartialOrder (X := S.toInvariantSubset))
      (CZero.instStarOrderedRing (X := S.toInvariantSubset)) _
      (CZero.action Γ' (X := S.toInvariantSubset))
      (CZero.action Γ (X := ((pieceRelabel e X).symm S).toInvariantSubset) :
        CStarAlgebraAction Γ C₀(S.toInvariantSubset, ℂ))
      (pieceAction_pull e X S)
      (Assembly.cutoffKKClass Γ ((pieceRelabel e X).symm S).toInvariantSubset
        (Assembly.pieceCutoff Γ (Pull e X) ((pieceRelabel e X).symm S)) :
        KKParityGroup.{0, 0, u, u} false (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
          (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct
            (CZero.action Γ (X := ((pieceRelabel e X).symm S).toInvariantSubset) :
              CStarAlgebraAction Γ C₀(S.toInvariantSubset, ℂ)))))
      (Assembly.cutoffKKClass Γ' S.toInvariantSubset (Assembly.pieceCutoff Γ' X S))
      (cutoffKKClass_pull e (Y := S.toInvariantSubset) (Assembly.pieceCutoff Γ' X S)
        (Assembly.pieceCutoff Γ (Pull e X) ((pieceRelabel e X).symm S))) x).symm

/-- The square on a piece in even degree. The assembly maps and `pieceEquiv` are
unfolded by rewriting first, so that the kernel never compares folded and unfolded forms. -/
theorem pieceSquare_even (S : CocompactPiece Γ' X) (x : TopologicalKHomology.pieceGroup false S) :
    analyticGroupEquiv e false
        (Assembly.pieceAssemblyHom Γ (Pull e X) false ((pieceRelabel e X).symm S)
          (pieceEquiv e X false S x)) =
      Assembly.pieceAssemblyHom Γ' X false S x := by
  rw [pieceAssemblyHom_relabel_even, pieceAssemblyHom_even, pieceEquiv_apply]
  exact pieceSquare_even_core e X S x

/-- The square on a piece in odd degree. The assembly maps and `pieceEquiv` are
unfolded by rewriting first, so that the kernel never compares folded and unfolded forms. -/
theorem pieceSquare_odd (S : CocompactPiece Γ' X) (x : TopologicalKHomology.pieceGroup true S) :
    analyticGroupEquiv e true
        (Assembly.pieceAssemblyHom Γ (Pull e X) true ((pieceRelabel e X).symm S)
          (pieceEquiv e X true S x)) =
      Assembly.pieceAssemblyHom Γ' X true S x := by
  rw [pieceAssemblyHom_relabel_odd, pieceAssemblyHom_odd, pieceEquiv_apply]
  exact pieceSquare_odd_core e X S x

/-- The square on every cocompact piece. -/
theorem pieceSquare (p : Bool) : PieceSquare e X p := by
  cases p
  · exact pieceSquare_even e X
  · exact pieceSquare_odd e X

end Pieces

end BC4lean.KKTheory.GroupIso

namespace BC4lean.Assembly
open KKTheory.GroupIso ProperActions

section Main
universe u
variable {Γ Γ' : Type u} [Group Γ] [Group Γ'] [Countable Γ] [Countable Γ']
  [TopologicalSpace Γ] [DiscreteTopology Γ] [TopologicalSpace Γ'] [DiscreteTopology Γ']

/-- **Group-isomorphism invariance.** Reduced Baum–Connes (upstream's `BaumConnesProperty`,
unchanged) holds for `Γ` iff it holds for any isomorphic `Γ'` in the same universe. -/
theorem baumConnesProperty_congr (e : Γ ≃* Γ') :
    BaumConnesProperty Γ ↔ BaumConnesProperty Γ' :=
  baumConnesProperty_congr_of_square e fun p =>
    letI : ProperSMul Γ' (LabeledOrbitTelescope.Model Γ') := LabeledOrbitTelescope.proper Γ'
    relabelSquare_of_pieces e (LabeledOrbitTelescope.Model Γ') p
      (pieceSquare e (LabeledOrbitTelescope.Model Γ') p)

end Main

end BC4lean.Assembly
