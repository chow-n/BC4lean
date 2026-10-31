import BC4lean.FinitePointCharacterAssembly
import BC4lean.OrderTwoPointKKScalar
import BC4lean.FiniteReducedGroupCStar
import BC4lean.BaumConnesProperty
import BC4lean.UnitAssemblyEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The assembly map for a group of order two

For `Nat.card Γ = 2` the reduced assembly map is identified, in both parities, with an explicit
additive equivalence, so `Γ` has the coefficient-free reduced Baum–Connes property
(`baumConnesProperty_of_card_two`). The proof follows `UnitAssemblyEquivalence`:

* the canonical colimit is the point model (`reducedAssemblyHom_finitePoint`);
* `KK^Γ_p(C₀(pt), ℂ) ≅ KK_p(ℂ, ℂ)²` by the `±1` eigen parts of the generator
  (`orderTwoPointKKSplit`), with inverse `(a, b) ↦ infl a + χ ⊗ infl b`, `χ` the sign character;
* on a class of the form `χ ⊗ infl a`, cutoff product and descent give the coefficient extension
  of `a` along `z ↦ z • P_χ`, and the scalar index theorem then gives `(P_χ)_* [a]` in
  `K_p(C*_r Γ)` (`spaceAssembly_even_class`, `spaceAssembly_odd_class`, which hold for every finite
  group and live in `FinitePointCharacterAssembly`);
* under `ℂ × ℂ ≅ C*_r Γ` the projections `P_1` and `P_sign` are the two coordinate idempotents
  (`crossedHom_comp_characterHom_one`, `crossedHom_comp_characterHom_sign`), so the composite is
  `KK_p(ℂ, ℂ)² ≅ K_p(ℂ)² ≅ K_p(ℂ × ℂ) ≅ K_p(C*_r Γ)` (`orderTwoAnalyticEquiv`).
-/

noncomputable section

namespace BC4lean.Chapter8Examples.OrderTwoAssembly
open ProperActions KKTheory OperatorKTheory OrderTwo FinitePointAssembly
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open KKTheory.FinitePointCompressedDescent KKTheory.FinitePointCharacterTensor KKTheory.FinitePointCutoff
open scoped ZeroAtInfty ComplexOrder KasparovDescent

variable {Γ : Type} [Group Γ] [Countable Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]

section Algebra

variable (h2 : Nat.card Γ = 2)

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- For `Γ = {1, g}`, the image of `P_χ` in `C*_r(Γ)` is `(1 + χ(g) λ_g) / 2`. -/
theorem crossedHom_characterProjection (χ : Γ →* unitary ℂ) :
    crossedHom Γ (characterProjection Γ χ) =
      (2⁻¹ : ℂ) • (1 : ReducedGroupCStar Γ) + ((2⁻¹ : ℂ) * (χ (orderTwoGenerator h2) : ℂ)) •
        ⟨regularOperator (orderTwoGenerator h2), regularOperator_mem_reducedAlgebra _⟩ := by
  have hcard : (Fintype.card Γ : ℂ) = 2 := by
    rw [Fintype.card_eq_nat_card, h2]; norm_num
  have hone : (⟨regularOperator (1 : Γ), regularOperator_mem_reducedAlgebra 1⟩ :
      ReducedGroupCStar Γ) = 1 := Subtype.ext regularOperator_one
  rw [characterProjection, map_sum, Fintype.sum_eq_add 1 (orderTwoGenerator h2)
    (orderTwoGenerator_ne_one h2).symm (fun x hx => by
      rcases eq_one_or_eq_orderTwoGenerator h2 x with h | h
      · exact absurd h hx.1
      · exact absurd h hx.2)]
  rw [map_smul, map_smul, crossedHom_regular, crossedHom_regular, hone, hcard, map_one,
    OneMemClass.coe_one, mul_one]

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- The trivial-character projection is the first idempotent of `ℂ × ℂ ≅ C*_r(Γ)`. -/
theorem crossedHom_comp_characterHom_one :
    (crossedHom Γ).comp (characterHom Γ 1) =
      (orderTwoReducedEquiv h2).toNonUnitalStarAlgHom.comp (NonUnitalStarAlgHom.inl ℂ ℂ ℂ) := by
  apply scalarHom_ext
  change crossedHom Γ ((1 : ℂ) • characterProjection Γ 1) = orderTwoReducedEquiv h2 (1, 0)
  rw [one_smul, crossedHom_characterProjection h2,
    orderTwoReducedEquiv_apply h2 (orderTwoGenerator_ne_one h2)]
  simp only [MonoidHom.one_apply, OneMemClass.coe_one]
  norm_num

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- The sign-character projection is the second idempotent of `ℂ × ℂ ≅ C*_r(Γ)`. -/
theorem crossedHom_comp_characterHom_sign :
    (crossedHom Γ).comp (characterHom Γ (orderTwoUnitarySign h2)) =
      (orderTwoReducedEquiv h2).toNonUnitalStarAlgHom.comp (NonUnitalStarAlgHom.inr ℂ ℂ ℂ) := by
  apply scalarHom_ext
  change crossedHom Γ ((1 : ℂ) • characterProjection Γ (orderTwoUnitarySign h2)) =
    orderTwoReducedEquiv h2 (0, 1)
  rw [one_smul, crossedHom_characterProjection h2,
    orderTwoReducedEquiv_apply h2 (orderTwoGenerator_ne_one h2), orderTwoUnitarySign_generator h2]
  norm_num

end Algebra

section Glue

local instance pointCZero_separable' : TopologicalSpace.SeparableSpace C₀(FiniteGroupPoint.{0}, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

variable (h2 : Nat.card Γ = 2)

omit [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
variable (Γ) in
/-- Even analytic side for `|Γ| = 2`: `KK₀(ℂ,ℂ)² ≅ K₀(ℂ)² ≅ K₀(ℂ × ℂ) ≅ K₀(C*_r Γ)`. -/
def orderTwoK0Equiv :
    KasparovHomotopyClass.{0,0,0,0} unitScalarAction unitScalarAction ×
      KasparovHomotopyClass.{0,0,0,0} unitScalarAction unitScalarAction ≃+ ReducedK0 Γ :=
  letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  (scalarKKOperatorK0AddEquiv.{0,0}.prodCongr scalarKKOperatorK0AddEquiv.{0,0}).trans
    ((operatorK0ProductEquiv ℂ ℂ).symm.trans ((operatorK0MapEquiv (orderTwoReducedEquiv h2)).trans
      (operatorK0UnitalEquiv (ReducedGroupCStar Γ))))

omit [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
variable (Γ) in
/-- Odd analytic side for `|Γ| = 2`: `KK₁(ℂ,ℂ)² ≅ K₁(ℂ)² ≅ K₁(ℂ × ℂ) ≅ K₁(C*_r Γ)`. -/
def orderTwoK1Equiv :
    OddKK.{0,0,0,0} unitScalarAction unitScalarAction ×
      OddKK.{0,0,0,0} unitScalarAction unitScalarAction ≃+ ReducedK1 Γ :=
  letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  (oddKKOperatorK1AllModuleUniversesAddEquiv.{0,0}.prodCongr
    oddKKOperatorK1AllModuleUniversesAddEquiv.{0,0}).trans
    ((operatorK1ProductEquiv ℂ ℂ).symm.trans ((operatorK1MapEquiv (orderTwoReducedEquiv h2)).trans
      (operatorK1UnitalEquiv (ReducedGroupCStar Γ))))

omit [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
variable (Γ) in
/-- The analytic side for `|Γ| = 2` in either parity. -/
def orderTwoAnalyticEquiv (p : Bool) :
    KKParityGroup.{0,0,0,0} p unitScalarAction unitScalarAction ×
      KKParityGroup.{0,0,0,0} p unitScalarAction unitScalarAction ≃+
      Assembly.analyticGroup Γ p :=
  match p with
  | false => orderTwoK0Equiv Γ h2
  | true => orderTwoK1Equiv Γ h2

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- `orderTwoK0Equiv` as the sum of the two character pushforwards. -/
theorem orderTwoK0Equiv_apply (a b : KasparovHomotopyClass.{0,0,0,0} unitScalarAction unitScalarAction) :
    orderTwoK0Equiv Γ h2 (a, b) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK0UnitalEquiv (ReducedGroupCStar Γ)
          (operatorK0Map ((crossedHom Γ).comp (characterHom Γ 1)) (scalarKKOperatorK0AddEquiv a)) +
        operatorK0UnitalEquiv (ReducedGroupCStar Γ)
          (operatorK0Map ((crossedHom Γ).comp (characterHom Γ (orderTwoUnitarySign h2)))
            (scalarKKOperatorK0AddEquiv b)) := by
  rw [crossedHom_comp_characterHom_one h2, crossedHom_comp_characterHom_sign h2, operatorK0Map_comp,
    operatorK0Map_comp, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← map_add, ← map_add,
    ← operatorK0ProductEquiv_symm_apply]
  rfl

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- `orderTwoK1Equiv` as the sum of the two character pushforwards. -/
theorem orderTwoK1Equiv_apply (a b : OddKK.{0,0,0,0} unitScalarAction unitScalarAction) :
    orderTwoK1Equiv Γ h2 (a, b) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK1UnitalEquiv (ReducedGroupCStar Γ)
          (operatorK1Map ((crossedHom Γ).comp (characterHom Γ 1))
            (oddKKOperatorK1AllModuleUniversesAddEquiv a)) +
        operatorK1UnitalEquiv (ReducedGroupCStar Γ)
          (operatorK1Map ((crossedHom Γ).comp (characterHom Γ (orderTwoUnitarySign h2)))
            (oddKKOperatorK1AllModuleUniversesAddEquiv b)) := by
  rw [crossedHom_comp_characterHom_one h2, crossedHom_comp_characterHom_sign h2, operatorK1Map_comp,
    operatorK1Map_comp, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← map_add, ← map_add,
    ← operatorK1ProductEquiv_symm_apply]
  rfl

/-- On the point, the assembly map is the eigen split `orderTwoPointKKSplit` followed by
`orderTwoAnalyticEquiv`, in both parities and for every cutoff. -/
theorem spaceAssemblyHom_orderTwo (c0 : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0}) (p : Bool)
    (x : TopologicalKHomology.spaceGroup p Γ FiniteGroupPoint.{0}) :
    Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} p c0 x =
      orderTwoAnalyticEquiv Γ h2 p (orderTwoPointKKSplit.{0,0} FiniteGroupPoint.{0} h2 default p x) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (orderTwoPointKKSplit.{0,0} FiniteGroupPoint.{0} h2 default p).symm.surjective x
  rw [AddEquiv.apply_symm_apply]
  cases p
  · have ha := spaceAssembly_even_class c0 1 a
    rw [twist_one_even] at ha
    exact ((map_add (Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} false c0) _ _).trans
      (congrArg₂ (· + ·) ha (spaceAssembly_even_class c0 (orderTwoUnitarySign h2) b))).trans
      (orderTwoK0Equiv_apply h2 a b).symm
  · have ha := spaceAssembly_odd_class c0 1 a
    rw [twist_one_odd] at ha
    exact ((map_add (Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} true c0) _ _).trans
      (congrArg₂ (· + ·) ha (spaceAssembly_odd_class c0 (orderTwoUnitarySign h2) b))).trans
      (orderTwoK1Equiv_apply h2 a b).symm

end Glue

end BC4lean.Chapter8Examples.OrderTwoAssembly

namespace BC4lean.Chapter8Examples
open OrderTwoAssembly KKTheory OrderTwo

/-- The reduced assembly map of a group of order two, as an explicit additive equivalence. -/
def orderTwoAssemblyAddEquiv (Γ : Type) [Group Γ] [Countable Γ] [TopologicalSpace Γ]
    [DiscreteTopology Γ] (h2 : Nat.card Γ = 2) (p : Bool) :
    TopologicalKHomology.topologicalGroup p Γ ≃+ Assembly.analyticGroup Γ p :=
  haveI : Finite Γ := finite_of_card_eq_two h2
  (finiteTopologicalPointSpaceEquiv Γ p).trans
    ((orderTwoPointKKSplit.{0,0} FiniteGroupPoint.{0} h2 default p).trans (orderTwoAnalyticEquiv Γ h2 p))

/-- Identification with Chapter 7's canonical assembly map. -/
theorem reducedAssemblyHom_orderTwo_eq (Γ : Type) [Group Γ] [Countable Γ] [TopologicalSpace Γ]
    [DiscreteTopology Γ] (h2 : Nat.card Γ = 2) (p : Bool)
    (x : TopologicalKHomology.topologicalGroup p Γ) :
    Assembly.reducedAssemblyHom Γ p x = orderTwoAssemblyAddEquiv Γ h2 p x := by
  have : Finite Γ := finite_of_card_eq_two h2
  let : Fintype Γ := Fintype.ofFinite Γ
  rw [reducedAssemblyHom_finitePoint]
  exact spaceAssemblyHom_orderTwo (Γ := Γ) h2 (finitePointCutoff Γ) p _

/-- The coefficient-free reduced Baum–Connes property for every countable discrete group of
order two. -/
theorem baumConnesProperty_of_card_two (Γ : Type) [Group Γ] [Countable Γ] [TopologicalSpace Γ]
    [DiscreteTopology Γ] (h2 : Nat.card Γ = 2) : Assembly.BaumConnesProperty Γ := by
  intro p
  have h : (Assembly.reducedAssemblyHom Γ p :
      TopologicalKHomology.topologicalGroup p Γ → Assembly.analyticGroup Γ p) =
      orderTwoAssemblyAddEquiv Γ h2 p := funext (reducedAssemblyHom_orderTwo_eq Γ h2 p)
  rw [h]
  exact (orderTwoAssemblyAddEquiv Γ h2 p).bijective

/-- The cyclic group of order two, with the discrete topology. -/
theorem baumConnesProperty_zmod_two :
    letI : TopologicalSpace (Multiplicative (ZMod 2)) := ⊥
    haveI : DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩
    Assembly.BaumConnesProperty (Multiplicative (ZMod 2)) :=
  letI : TopologicalSpace (Multiplicative (ZMod 2)) := ⊥
  haveI : DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩
  baumConnesProperty_of_card_two _ (by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])

end BC4lean.Chapter8Examples
