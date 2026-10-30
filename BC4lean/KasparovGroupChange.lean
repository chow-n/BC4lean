import BC4lean.KasparovHomotopyGroup
import BC4lean.OddKasparovHomotopyGroup
import BC4lean.IntervalKasparovFibre
import BC4lean.OddIntervalKasparovFibre

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Change of group for equivariant Kasparov cycles

Let `φ : H →* Γ` be a group homomorphism, and let `α'`, `β'` be `H`-actions on `A`, `B` with
`α' h = α (φ h)` and `β' h = β (φ h)` pointwise. A `Γ`-equivariant cycle becomes an
`H`-equivariant cycle by letting `h` act on the module through `φ h`; the module, grading,
representation and operator are unchanged (`KasparovCycle.comap`). The compatibility of the
actions is a hypothesis rather than a definition, so restriction to the trivial group
(`H = Unit`, `α' = β' = trivial`) and inflation from it (`Γ = Unit`) need no casts.

The construction respects cycle isomorphisms and full interval homotopies, because taking
fibres of an interval cycle commutes with it. Hence it descends to an additive map of KK groups
(`KasparovHomotopyClass.comap`, `OddKK.comap`).

For a unitary character `χ : Γ →* unitary ℂ`, twisting the module action to `g ↦ χ(g) U_g` is
treated the same way (`KasparovCycle.twist`, `KasparovHomotopyClass.twist`, `OddKK.twist`). For a
group of order two and the sign character this turns the trivial action into the sign action.

`KKGroupRestriction` restricts along a group homomorphism as well; there the restricted
coefficient actions are defined (`GroupRestriction.actionComap`). Here the compatibility of the
actions is a hypothesis, which avoids casts when the trivial group is on one side, and the file
adds the twist by a character. -/

noncomputable section
universe uΓ uH uA uB uE uF
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {Γ : Type uΓ} {H : Type uH} {A : Type uA} {B : Type uB} {E : Type uE} {F : Type uF}
  [Group Γ] [Group H]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  (φ : H →* Γ)


/-! ## Coefficient and module actions -/

variable [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]


namespace EquivariantHilbertModule

variable {β : CStarAlgebraAction Γ B} {β' : CStarAlgebraAction H B}
  (hβ : ∀ h b, β'.automorphism h b = β.automorphism (φ h) b)

/-- The module action pulled back along `φ`. -/
def comap (U : EquivariantHilbertModule β E) : EquivariantHilbertModule β' E where
  action := U.action.comp φ
  inner_action h x y := by
    rw [MonoidHom.comp_apply, U.inner_action]
    simp only [opStarAlgEquiv_apply, hβ]

@[simp] theorem comap_action (U : EquivariantHilbertModule β E) (h : H) :
    (U.comap φ hβ).action h = U.action (φ h) := rfl

theorem comap_conjugateMap (U : EquivariantHilbertModule β E) (V : EquivariantHilbertModule β F)
    (h : H) (T : AdjointableMap B E F) :
    (U.comap φ hβ).conjugateMap (V.comap φ hβ) h T = U.conjugateMap V (φ h) T := by
  ext x
  simp only [conjugateMap_apply, comap_action, map_inv]

theorem comap_conjugateOperator (U : EquivariantHilbertModule β E) (h : H)
    (T : AdjointableMap B E E) :
    (U.comap φ hβ).conjugateOperator h T = U.conjugateOperator (φ h) T :=
  comap_conjugateMap φ hβ U U h T

end EquivariantHilbertModule

/-! ## Cycles and isomorphisms -/

variable [StarOrderedRing B] [CompleteSpace E] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {α' : CStarAlgebraAction H A} {β' : CStarAlgebraAction H B}
  (hα : ∀ h a, α'.automorphism h a = α.automorphism (φ h) a)
  (hβ : ∀ h b, β'.automorphism h b = β.automorphism (φ h) b)

namespace CStarAlgebraAction

/-- Pointwise compatibility of the coefficient actions passes to continuous sections. -/
theorem continuousSections_comap_apply {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {β : CStarAlgebraAction Γ B} {β' : CStarAlgebraAction H B}
    (hβ : ∀ h b, β'.automorphism h b = β.automorphism (φ h) b) (h : H) (b : C(X, B)) :
    (β'.continuousSections (X := X)).automorphism h b =
      (β.continuousSections (X := X)).automorphism (φ h) b := by
  ext t
  exact hβ h (b t)

end CStarAlgebraAction

namespace KasparovCycle

/-- An even `Γ`-cycle read as an `H`-cycle through `φ`. -/
def comap (c : KasparovCycle α β E) : KasparovCycle α' β' E where
  countablyGenerated := c.countablyGenerated
  grading := c.grading
  groupAction := c.groupAction.comap φ hβ
  grading_preserved h x := c.grading_preserved (φ h) x
  representation := c.representation
  representation_even := c.representation_even
  representation_equivariant h a := by
    rw [EquivariantHilbertModule.comap_conjugateOperator, c.representation_equivariant, hα]
  operator := c.operator
  operator_odd := c.operator_odd
  selfadjoint_mod_compact := c.selfadjoint_mod_compact
  square_mod_compact := c.square_mod_compact
  commutator_compact := c.commutator_compact
  equivariance_mod_compact h a := by
    rw [EquivariantHilbertModule.comap_conjugateOperator]
    exact c.equivariance_mod_compact (φ h) a

@[simp] theorem comap_operator (c : KasparovCycle α β E) : (c.comap φ hα hβ).operator = c.operator :=
  rfl

@[simp] theorem comap_representation (c : KasparovCycle α β E) :
    (c.comap φ hα hβ).representation = c.representation := rfl

@[simp] theorem comap_groupAction_action (c : KasparovCycle α β E) (h : H) :
    (c.comap φ hα hβ).groupAction.action h = c.groupAction.action (φ h) := rfl

/-- Pulling back commutes with direct sums. -/
def comapDirectSumIso (c : KasparovCycle α β E) (d : KasparovCycle α β F) :
    KasparovCycleIso ((c.directSum d).comap φ hα hβ) ((c.comap φ hα hβ).directSum (d.comap φ hα hβ))
    where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

section Compose

variable {K : Type*} [Group K] (ψ : K →* H)
  {α'' : CStarAlgebraAction K A} {β'' : CStarAlgebraAction K B}
  (hα' : ∀ k a, α''.automorphism k a = α'.automorphism (ψ k) a)
  (hβ' : ∀ k b, β''.automorphism k b = β'.automorphism (ψ k) b)

/-- Pulling back twice is pulling back along the composite. -/
def comapComapIso (c : KasparovCycle α β E) :
    KasparovCycleIso ((c.comap φ hα hβ).comap ψ hα' hβ')
      (c.comap (φ.comp ψ) (fun k a => (hα' k a).trans (hα (ψ k) a))
        (fun k b => (hβ' k b).trans (hβ (ψ k) b))) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end Compose

/-- Pulling back along an endomorphism that fixes every element changes nothing. -/
def comapSelfIso (c : KasparovCycle α β E) (ψ : Γ →* Γ) (hψ : ∀ g, ψ g = g)
    (hα₀ : ∀ g a, α.automorphism g a = α.automorphism (ψ g) a)
    (hβ₀ : ∀ g b, β.automorphism g b = β.automorphism (ψ g) b) :
    KasparovCycleIso (c.comap ψ hα₀ hβ₀) c where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine g x := by
    change c.groupAction.action (ψ g) x = c.groupAction.action g x
    rw [hψ]
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end KasparovCycle

namespace KasparovCycleIso

variable {c : KasparovCycle α β E} {d : KasparovCycle α β F}

/-- A cycle isomorphism is an isomorphism of the pulled-back cycles. -/
def comap (u : KasparovCycleIso c d) : KasparovCycleIso (c.comap φ hα hβ) (d.comap φ hα hβ) where
  moduleEquiv := u.moduleEquiv
  grading_intertwine := u.grading_intertwine
  action_intertwine h x := u.action_intertwine (φ h) x
  representation_intertwine := u.representation_intertwine
  operator_intertwine := u.operator_intertwine

end KasparovCycleIso

/-! ## Fibres, full homotopies and classes -/

section Fibre

variable {X M : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

namespace KasparovCycle

/-- The fibre of a pulled-back interval cycle is the pulled-back fibre. -/
def fibreComapIso (c : KasparovCycle α (β.continuousSections (X := X)) M) (t : X) :
    KasparovCycleIso
      ((c.comap φ hα (CStarAlgebraAction.continuousSections_comap_apply φ hβ)).fibre t)
      ((c.fibre t).comap φ hα hβ) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end KasparovCycle

end Fibre

namespace BundledKasparovCycle

/-- A bundled even cycle pulled back along `φ`. -/
def comap (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    BundledKasparovCycle.{uH, uA, uB, uE} α' β' :=
  of (c.cycle.comap φ hα hβ)

end BundledKasparovCycle

namespace FullKasparovHomotopy

/-- A full interval homotopy pulled back along `φ`. -/
def comap {c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β} (H : FullKasparovHomotopy c d) :
    FullKasparovHomotopy (c.comap φ hα hβ) (d.comap φ hα hβ) where
  intervalCycle := BundledKasparovCycle.of (H.intervalCycle.cycle.comap φ hα
    (CStarAlgebraAction.continuousSections_comap_apply φ hβ))
  sourceIso := (H.intervalCycle.cycle.fibreComapIso φ hα hβ 0).trans (H.sourceIso.comap φ hα hβ)
  targetIso := (H.intervalCycle.cycle.fibreComapIso φ hα hβ 1).trans (H.targetIso.comap φ hα hβ)

end FullKasparovHomotopy

namespace KasparovHomotopyClass

/-- Pulling back along `φ` on even KK classes. -/
def comapFun :
    KasparovHomotopyClass.{uΓ, uA, uB, uE} α β → KasparovHomotopyClass.{uH, uA, uB, uE} α' β' :=
  Quotient.lift (fun c => mk (c.comap φ hα hβ))
    (fun c d h => by
      change BundledKasparovCycle.Homotopic c d at h
      induction h with
      | rel a b h =>
          change a.Isomorphic b ∨ Nonempty (FullKasparovHomotopy a b) at h
          rcases h with h | h
          · obtain ⟨u⟩ := h
            exact mk_eq_of_iso (u.comap φ hα hβ)
          · obtain ⟨h⟩ := h
            exact mk_eq_of_full (h.comap φ hα hβ)
      | refl => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b k _ _ hab hbk => exact hab.trans hbk)

/-- Pulling back along `φ` is additive on even KK classes. -/
def comap :
    KasparovHomotopyClass.{uΓ, uA, uB, uE} α β →+ KasparovHomotopyClass.{uH, uA, uB, uE} α' β' :=
  AddMonoidHom.mk' (comapFun φ hα hβ) (fun x y => by
    induction x using Quotient.inductionOn with
    | h c =>
      induction y using Quotient.inductionOn with
      | h d =>
        change mk ((c.directSum d).comap φ hα hβ) = mk ((c.comap φ hα hβ).directSum (d.comap φ hα hβ))
        exact mk_eq_of_iso (c.cycle.comapDirectSumIso φ hα hβ d.cycle))

@[simp] theorem comap_mk (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    comap φ hα hβ (mk c) = mk (c.comap φ hα hβ) := rfl

end KasparovHomotopyClass

/-! ## Odd cycles -/

namespace OddKasparovCycle

/-- An odd `Γ`-cycle read as an `H`-cycle through `φ`. -/
def comap (c : OddKasparovCycle α β E) : OddKasparovCycle α' β' E where
  countablyGenerated := c.countablyGenerated
  groupAction := c.groupAction.comap φ hβ
  representation := c.representation
  representation_equivariant h a := by
    rw [EquivariantHilbertModule.comap_conjugateOperator, c.representation_equivariant, hα]
  operator := c.operator
  selfadjoint_mod_compact := c.selfadjoint_mod_compact
  square_mod_compact := c.square_mod_compact
  commutator_compact := c.commutator_compact
  equivariance_mod_compact h a := by
    rw [EquivariantHilbertModule.comap_conjugateOperator]
    exact c.equivariance_mod_compact (φ h) a

@[simp] theorem comap_operator (c : OddKasparovCycle α β E) :
    (c.comap φ hα hβ).operator = c.operator := rfl

@[simp] theorem comap_representation (c : OddKasparovCycle α β E) :
    (c.comap φ hα hβ).representation = c.representation := rfl

@[simp] theorem comap_groupAction_action (c : OddKasparovCycle α β E) (h : H) :
    (c.comap φ hα hβ).groupAction.action h = c.groupAction.action (φ h) := rfl

/-- Pulling back commutes with direct sums. -/
def comapDirectSumIso (c : OddKasparovCycle α β E) (d : OddKasparovCycle α β F) :
    OddKasparovCycleIso ((c.directSum d).comap φ hα hβ)
      ((c.comap φ hα hβ).directSum (d.comap φ hα hβ)) where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

section Compose

variable {K : Type*} [Group K] (ψ : K →* H)
  {α'' : CStarAlgebraAction K A} {β'' : CStarAlgebraAction K B}
  (hα' : ∀ k a, α''.automorphism k a = α'.automorphism (ψ k) a)
  (hβ' : ∀ k b, β''.automorphism k b = β'.automorphism (ψ k) b)

/-- Pulling back twice is pulling back along the composite. -/
def comapComapIso (c : OddKasparovCycle α β E) :
    OddKasparovCycleIso ((c.comap φ hα hβ).comap ψ hα' hβ')
      (c.comap (φ.comp ψ) (fun k a => (hα' k a).trans (hα (ψ k) a))
        (fun k b => (hβ' k b).trans (hβ (ψ k) b))) where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end Compose

/-- Pulling back along an endomorphism that fixes every element changes nothing. -/
def comapSelfIso (c : OddKasparovCycle α β E) (ψ : Γ →* Γ) (hψ : ∀ g, ψ g = g)
    (hα₀ : ∀ g a, α.automorphism g a = α.automorphism (ψ g) a)
    (hβ₀ : ∀ g b, β.automorphism g b = β.automorphism (ψ g) b) :
    OddKasparovCycleIso (c.comap ψ hα₀ hβ₀) c where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine g x := by
    change c.groupAction.action (ψ g) x = c.groupAction.action g x
    rw [hψ]
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end OddKasparovCycle

namespace OddKasparovCycleIso

variable {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}

/-- An odd cycle isomorphism is an isomorphism of the pulled-back cycles. -/
def comap (u : OddKasparovCycleIso c d) :
    OddKasparovCycleIso (c.comap φ hα hβ) (d.comap φ hα hβ) where
  moduleEquiv := u.moduleEquiv
  action_intertwine h x := u.action_intertwine (φ h) x
  representation_intertwine := u.representation_intertwine
  operator_intertwine := u.operator_intertwine

end OddKasparovCycleIso

section OddFibre

variable {X M : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

/-- The fibre of a pulled-back odd interval cycle is the pulled-back fibre. -/
def OddKasparovCycle.fibreComapIso (c : OddKasparovCycle α (β.continuousSections (X := X)) M)
    (t : X) :
    OddKasparovCycleIso
      ((c.comap φ hα (CStarAlgebraAction.continuousSections_comap_apply φ hβ)).fibre t)
      ((c.fibre t).comap φ hα hβ) where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end OddFibre

namespace BundledOddKasparovCycle

/-- A bundled odd cycle pulled back along `φ`. -/
def comap (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    BundledOddKasparovCycle.{uH, uA, uB, uE} α' β' :=
  of (c.cycle.comap φ hα hβ)

end BundledOddKasparovCycle

namespace FullOddKasparovHomotopy

/-- An odd full interval homotopy pulled back along `φ`. -/
def comap {c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β}
    (H : FullOddKasparovHomotopy c d) :
    FullOddKasparovHomotopy (c.comap φ hα hβ) (d.comap φ hα hβ) where
  intervalCycle := BundledOddKasparovCycle.of (H.intervalCycle.cycle.comap φ hα
    (CStarAlgebraAction.continuousSections_comap_apply φ hβ))
  sourceIso := (H.intervalCycle.cycle.fibreComapIso φ hα hβ 0).trans (H.sourceIso.comap φ hα hβ)
  targetIso := (H.intervalCycle.cycle.fibreComapIso φ hα hβ 1).trans (H.targetIso.comap φ hα hβ)

end FullOddKasparovHomotopy

namespace OddKK

variable [TopologicalSpace.SeparableSpace B]

/-- Pulling back along `φ` on odd KK classes. -/
def comapFun : OddKK.{uΓ, uA, uB, uE} α β → OddKK.{uH, uA, uB, uE} α' β' :=
  Quotient.lift (fun c => mk (c.comap φ hα hβ))
    (fun _ _ h => by
      obtain ⟨h⟩ := h
      exact Quotient.sound ⟨h.comap φ hα hβ⟩)

/-- Pulling back along `φ` is additive on odd KK classes. -/
def comap : OddKK.{uΓ, uA, uB, uE} α β →+ OddKK.{uH, uA, uB, uE} α' β' :=
  AddMonoidHom.mk' (comapFun φ hα hβ) (fun x y => by
    induction x using Quotient.inductionOn with
    | h c =>
      induction y using Quotient.inductionOn with
      | h d =>
        change mk ((c.directSum d).comap φ hα hβ) =
          mk ((c.comap φ hα hβ).directSum (d.comap φ hα hβ))
        exact mk_eq_of_iso (c.cycle.comapDirectSumIso φ hα hβ d.cycle))

@[simp] theorem comap_mk (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    comap φ hα hβ (mk c) = mk (c.comap φ hα hβ) := rfl

end OddKK

/-! ## Twisting the module action by a unitary character

For `χ : Γ →* unitary ℂ`, replacing `U_g` by `χ(g) U_g` gives another compatible action with the
same coefficient action: scalars of modulus one preserve the inner product. Conjugation of
operators is unchanged, because `χ(g) χ(g⁻¹) = 1`. Hence every cycle condition is unchanged. -/

section Twist

variable (χ : Γ →* unitary ℂ)

omit [PartialOrder B] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] [SMul Bᵐᵒᵖ E] in
/-- Multiplication by a complex number of modulus one, as a linear isometry. -/
def unitarySMulEquiv (z : unitary ℂ) : E ≃ₗᵢ[ℂ] E where
  toFun x := (z : ℂ) • x
  invFun x := ((star z : unitary ℂ) : ℂ) • x
  map_add' := smul_add _
  map_smul' c x := smul_comm _ c x
  left_inv x := by
    change ((star z : unitary ℂ) : ℂ) • (z : ℂ) • x = x
    rw [smul_smul, Unitary.coe_star, Unitary.coe_star_mul_self, one_smul]
  right_inv x := by
    change (z : ℂ) • ((star z : unitary ℂ) : ℂ) • x = x
    rw [smul_smul, Unitary.coe_star, Unitary.mul_star_self_of_mem z.2, one_smul]
  norm_map' x := by
    change ‖(z : ℂ) • x‖ = ‖x‖
    rw [norm_smul, CStarRing.norm_coe_unitary, one_mul]

omit [PartialOrder B] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] [SMul Bᵐᵒᵖ E] in
@[simp] theorem unitarySMulEquiv_apply (z : unitary ℂ) (x : E) :
    unitarySMulEquiv z x = (z : ℂ) • x := rfl

namespace EquivariantHilbertModule

omit [StarOrderedRing B] [CompleteSpace E] [CompleteSpace F]

/-- The module action twisted by `χ`: `g` acts by `χ(g) U_g`. -/
def twist (U : EquivariantHilbertModule β E) : EquivariantHilbertModule β E where
  action :=
    { toFun g := (U.action g).trans (unitarySMulEquiv (χ g))
      map_one' := by
        ext x
        simp
      map_mul' g h := by
        ext x
        simp only [LinearIsometryEquiv.coe_trans, Function.comp_apply, unitarySMulEquiv_apply,
          map_mul, LinearIsometryEquiv.coe_mul, LinearIsometryEquiv.map_smul,
          smul_smul, Submonoid.coe_mul, mul_comm] }
  inner_action g x y := by
    change ⟪((χ g : unitary ℂ) : ℂ) • U.action g x, ((χ g : unitary ℂ) : ℂ) • U.action g y⟫_(Bᵐᵒᵖ) = _
    rw [CStarModule.inner_smul_left_complex, CStarModule.inner_smul_right_complex, smul_smul,
      Unitary.star_mul_self_of_mem (χ g).2, one_smul, U.inner_action]

@[simp] theorem twist_action_apply (U : EquivariantHilbertModule β E) (g : Γ) (x : E) :
    (U.twist χ).action g x = ((χ g : unitary ℂ) : ℂ) • U.action g x := rfl

theorem twist_conjugateMap (U : EquivariantHilbertModule β E) (V : EquivariantHilbertModule β F)
    (g : Γ) (T : AdjointableMap B E F) :
    (U.twist χ).conjugateMap (V.twist χ) g T = U.conjugateMap V g T := by
  ext x
  simp only [conjugateMap_apply, twist_action_apply]
  change ((χ g : unitary ℂ) : ℂ) • V.action g (T.toCLM (((χ g⁻¹ : unitary ℂ) : ℂ) •
    U.action g⁻¹ x)) = V.action g (T.toCLM (U.action g⁻¹ x))
  rw [T.toCLM.map_smul, LinearIsometryEquiv.map_smul, smul_smul, ← Submonoid.coe_mul, ← map_mul,
    mul_inv_cancel, map_one, OneMemClass.coe_one, one_smul]

theorem twist_conjugateOperator (U : EquivariantHilbertModule β E) (g : Γ)
    (T : AdjointableMap B E E) :
    (U.twist χ).conjugateOperator g T = U.conjugateOperator g T :=
  twist_conjugateMap χ U U g T

end EquivariantHilbertModule

namespace KasparovCycle

/-- An even cycle with its module action twisted by `χ`. -/
def twist (c : KasparovCycle α β E) : KasparovCycle α β E where
  countablyGenerated := c.countablyGenerated
  grading := c.grading
  groupAction := c.groupAction.twist χ
  grading_preserved g x := by
    change ((χ g : unitary ℂ) : ℂ) • c.groupAction.action g (c.grading.grading x) =
      c.grading.grading (((χ g : unitary ℂ) : ℂ) • c.groupAction.action g x)
    rw [c.grading_preserved, LinearIsometryEquiv.map_smul]
  representation := c.representation
  representation_even := c.representation_even
  representation_equivariant g a := by
    rw [EquivariantHilbertModule.twist_conjugateOperator, c.representation_equivariant]
  operator := c.operator
  operator_odd := c.operator_odd
  selfadjoint_mod_compact := c.selfadjoint_mod_compact
  square_mod_compact := c.square_mod_compact
  commutator_compact := c.commutator_compact
  equivariance_mod_compact g a := by
    rw [EquivariantHilbertModule.twist_conjugateOperator]
    exact c.equivariance_mod_compact g a

@[simp] theorem twist_groupAction_action (c : KasparovCycle α β E) (g : Γ) (x : E) :
    (c.twist χ).groupAction.action g x = ((χ g : unitary ℂ) : ℂ) • c.groupAction.action g x :=
  rfl

/-- Twisting commutes with direct sums. -/
def twistDirectSumIso (c : KasparovCycle α β E) (d : KasparovCycle α β F) :
    KasparovCycleIso ((c.directSum d).twist χ) ((c.twist χ).directSum (d.twist χ)) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

/-- Twisting then pulling back is pulling back then twisting by `χ ∘ φ`. -/
def comapTwistIso (c : KasparovCycle α β E) :
    KasparovCycleIso ((c.twist χ).comap φ hα hβ) ((c.comap φ hα hβ).twist (χ.comp φ)) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

/-- Twisting by the trivial character changes nothing. -/
def twistTrivialIso (c : KasparovCycle α β E) (hχ : ∀ g, χ g = 1) :
    KasparovCycleIso (c.twist χ) c where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine g x := by
    change ((χ g : unitary ℂ) : ℂ) • c.groupAction.action g x = c.groupAction.action g x
    rw [hχ, OneMemClass.coe_one, one_smul]
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end KasparovCycle

namespace KasparovCycleIso

variable {c : KasparovCycle α β E} {d : KasparovCycle α β F}

/-- A cycle isomorphism is an isomorphism of the twisted cycles. -/
def twist (u : KasparovCycleIso c d) : KasparovCycleIso (c.twist χ) (d.twist χ) where
  moduleEquiv := u.moduleEquiv
  grading_intertwine := u.grading_intertwine
  action_intertwine g x := by
    change u.moduleEquiv (((χ g : unitary ℂ) : ℂ) • c.groupAction.action g x) =
      ((χ g : unitary ℂ) : ℂ) • d.groupAction.action g (u.moduleEquiv x)
    rw [HilbertModuleEquiv.map_smul, u.action_intertwine]
  representation_intertwine := u.representation_intertwine
  operator_intertwine := u.operator_intertwine

end KasparovCycleIso

section TwistFibre

variable {X M : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

omit [CompleteSpace M] in
theorem EquivariantHilbertModule.fibre_twist_action
    (U : EquivariantHilbertModule (β.continuousSections (X := X)) M) (t : X) (g : Γ)
    (z : HilbertModuleFibre B M t) :
    ((U.twist χ).fibre t).action g z = ((χ g : unitary ℂ) : ℂ) • (U.fibre t).action g z := by
  refine (hilbertModuleFibreMk_denseRange (B := B) (M := M) t).induction_on z ?_ ?_
  · exact isClosed_eq (((U.twist χ).fibre t).action g).continuous
      ((continuous_const_smul _).comp ((U.fibre t).action g).continuous)
  · intro x
    rw [EquivariantHilbertModule.fibre_action_mk, EquivariantHilbertModule.fibre_action_mk,
      EquivariantHilbertModule.twist_action_apply, map_smul]

/-- The fibre of a twisted interval cycle is the twisted fibre. -/
def KasparovCycle.fibreTwistIso (c : KasparovCycle α (β.continuousSections (X := X)) M)
    (t : X) : KasparovCycleIso ((c.twist χ).fibre t) ((c.fibre t).twist χ) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine g z := c.groupAction.fibre_twist_action χ t g z
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end TwistFibre

namespace BundledKasparovCycle

/-- A bundled even cycle with its action twisted by `χ`. -/
def twist (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    BundledKasparovCycle.{uΓ, uA, uB, uE} α β :=
  of (c.cycle.twist χ)

end BundledKasparovCycle

namespace FullKasparovHomotopy

/-- A full interval homotopy with its action twisted by `χ`. -/
def twist {c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β} (H : FullKasparovHomotopy c d) :
    FullKasparovHomotopy (c.twist χ) (d.twist χ) where
  intervalCycle := BundledKasparovCycle.of (H.intervalCycle.cycle.twist χ)
  sourceIso := (H.intervalCycle.cycle.fibreTwistIso χ 0).trans (H.sourceIso.twist χ)
  targetIso := (H.intervalCycle.cycle.fibreTwistIso χ 1).trans (H.targetIso.twist χ)

end FullKasparovHomotopy

namespace KasparovHomotopyClass

/-- Twisting by `χ` on even KK classes. -/
def twistFun :
    KasparovHomotopyClass.{uΓ, uA, uB, uE} α β → KasparovHomotopyClass.{uΓ, uA, uB, uE} α β :=
  Quotient.lift (fun c => mk (c.twist χ))
    (fun c d h => by
      change BundledKasparovCycle.Homotopic c d at h
      induction h with
      | rel a b h =>
          change a.Isomorphic b ∨ Nonempty (FullKasparovHomotopy a b) at h
          rcases h with h | h
          · obtain ⟨u⟩ := h
            exact mk_eq_of_iso (u.twist χ)
          · obtain ⟨h⟩ := h
            exact mk_eq_of_full (h.twist χ)
      | refl => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b k _ _ hab hbk => exact hab.trans hbk)

/-- Twisting by `χ` is additive on even KK classes. -/
def twist :
    KasparovHomotopyClass.{uΓ, uA, uB, uE} α β →+ KasparovHomotopyClass.{uΓ, uA, uB, uE} α β :=
  AddMonoidHom.mk' (twistFun χ) (fun x y => by
    induction x using Quotient.inductionOn with
    | h c =>
      induction y using Quotient.inductionOn with
      | h d =>
        change mk ((c.directSum d).twist χ) = mk ((c.twist χ).directSum (d.twist χ))
        exact mk_eq_of_iso (c.cycle.twistDirectSumIso χ d.cycle))

@[simp] theorem twist_mk (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    twist χ (mk c) = mk (c.twist χ) := rfl

end KasparovHomotopyClass

namespace OddKasparovCycle

/-- An odd cycle with its module action twisted by `χ`. -/
def twist (c : OddKasparovCycle α β E) : OddKasparovCycle α β E where
  countablyGenerated := c.countablyGenerated
  groupAction := c.groupAction.twist χ
  representation := c.representation
  representation_equivariant g a := by
    rw [EquivariantHilbertModule.twist_conjugateOperator, c.representation_equivariant]
  operator := c.operator
  selfadjoint_mod_compact := c.selfadjoint_mod_compact
  square_mod_compact := c.square_mod_compact
  commutator_compact := c.commutator_compact
  equivariance_mod_compact g a := by
    rw [EquivariantHilbertModule.twist_conjugateOperator]
    exact c.equivariance_mod_compact g a

@[simp] theorem twist_groupAction_action (c : OddKasparovCycle α β E) (g : Γ) (x : E) :
    (c.twist χ).groupAction.action g x = ((χ g : unitary ℂ) : ℂ) • c.groupAction.action g x :=
  rfl

/-- Twisting commutes with direct sums. -/
def twistDirectSumIso (c : OddKasparovCycle α β E) (d : OddKasparovCycle α β F) :
    OddKasparovCycleIso ((c.directSum d).twist χ) ((c.twist χ).directSum (d.twist χ)) where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

/-- Twisting then pulling back is pulling back then twisting by `χ ∘ φ`. -/
def comapTwistIso (c : OddKasparovCycle α β E) :
    OddKasparovCycleIso ((c.twist χ).comap φ hα hβ) ((c.comap φ hα hβ).twist (χ.comp φ)) where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

/-- Twisting by the trivial character changes nothing. -/
def twistTrivialIso (c : OddKasparovCycle α β E) (hχ : ∀ g, χ g = 1) :
    OddKasparovCycleIso (c.twist χ) c where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine g x := by
    change ((χ g : unitary ℂ) : ℂ) • c.groupAction.action g x = c.groupAction.action g x
    rw [hχ, OneMemClass.coe_one, one_smul]
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end OddKasparovCycle

namespace OddKasparovCycleIso

variable {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}

/-- An odd cycle isomorphism is an isomorphism of the twisted cycles. -/
def twist (u : OddKasparovCycleIso c d) : OddKasparovCycleIso (c.twist χ) (d.twist χ) where
  moduleEquiv := u.moduleEquiv
  action_intertwine g x := by
    change u.moduleEquiv (((χ g : unitary ℂ) : ℂ) • c.groupAction.action g x) =
      ((χ g : unitary ℂ) : ℂ) • d.groupAction.action g (u.moduleEquiv x)
    rw [HilbertModuleEquiv.map_smul, u.action_intertwine]
  representation_intertwine := u.representation_intertwine
  operator_intertwine := u.operator_intertwine

end OddKasparovCycleIso

section OddTwistFibre

variable {X M : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

/-- The fibre of a twisted odd interval cycle is the twisted fibre. -/
def OddKasparovCycle.fibreTwistIso (c : OddKasparovCycle α (β.continuousSections (X := X)) M)
    (t : X) : OddKasparovCycleIso ((c.twist χ).fibre t) ((c.fibre t).twist χ) where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine g z := c.groupAction.fibre_twist_action χ t g z
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end OddTwistFibre

namespace BundledOddKasparovCycle

/-- A bundled odd cycle with its action twisted by `χ`. -/
def twist (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β :=
  of (c.cycle.twist χ)

end BundledOddKasparovCycle

namespace FullOddKasparovHomotopy

/-- An odd full interval homotopy with its action twisted by `χ`. -/
def twist {c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β}
    (H : FullOddKasparovHomotopy c d) : FullOddKasparovHomotopy (c.twist χ) (d.twist χ) where
  intervalCycle := BundledOddKasparovCycle.of (H.intervalCycle.cycle.twist χ)
  sourceIso := (H.intervalCycle.cycle.fibreTwistIso χ 0).trans (H.sourceIso.twist χ)
  targetIso := (H.intervalCycle.cycle.fibreTwistIso χ 1).trans (H.targetIso.twist χ)

end FullOddKasparovHomotopy

namespace OddKK

variable [TopologicalSpace.SeparableSpace B]

/-- Twisting by `χ` on odd KK classes. -/
def twistFun : OddKK.{uΓ, uA, uB, uE} α β → OddKK.{uΓ, uA, uB, uE} α β :=
  Quotient.lift (fun c => mk (c.twist χ))
    (fun _ _ h => by
      obtain ⟨h⟩ := h
      exact Quotient.sound ⟨h.twist χ⟩)

/-- Twisting by `χ` is additive on odd KK classes. -/
def twist : OddKK.{uΓ, uA, uB, uE} α β →+ OddKK.{uΓ, uA, uB, uE} α β :=
  AddMonoidHom.mk' (twistFun χ) (fun x y => by
    induction x using Quotient.inductionOn with
    | h c =>
      induction y using Quotient.inductionOn with
      | h d =>
        change mk ((c.directSum d).twist χ) = mk ((c.twist χ).directSum (d.twist χ))
        exact mk_eq_of_iso (c.cycle.twistDirectSumIso χ d.cycle))

@[simp] theorem twist_mk (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    twist χ (mk c) = mk (c.twist χ) := rfl

end OddKK

end Twist

end BC4lean.KKTheory
