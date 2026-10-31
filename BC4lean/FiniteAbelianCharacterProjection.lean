import BC4lean.KasparovEquivariantDirectSum
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Character parts of a Kasparov cycle over a finite group

Let `Γ` be a finite group acting trivially on `A` and on `B`, and let `χ : Γ →* unitary ℂ` be a
character. On the module of a cycle every group element acts by an adjointable unitary `U_g`, and

  `P_χ = |Γ|⁻¹ ∑_g conj χ(g) U_g`

is a star projection with `U_h P_χ = P_χ U_h = χ(h) P_χ`; its range is the `χ`-isotypic part of the
module. It commutes with every operator fixed by conjugation by the group, with the
representation of `A` (on which `Γ` acts trivially), with the grading and with the group action.
For `|Γ| = 2` and `χ = 1` or the sign character, `P_χ` is the eigenprojection `(1 ± U_g)/2` of
`OrderTwoPointKK`.

The `χ`-part of a cycle is the compression of its canonical equivariant representative
(`KasparovCycle.equivariantCycle`) to `P_χ`. Since compressions of the equivariant representative
respect cycle isomorphisms, full homotopies and direct sums (`KasparovEquivariantRepresentative`,
`KasparovEquivariantDirectSum`), so do `χ`-parts, so `c ↦ [c.charPart χ]` descends to an additive map `charClassHom χ` on even and odd
KK groups.

For a finite abelian group, the characters are indexed by `CharacterDual Γ = AddChar (Additive Γ) ℂ`
(Mathlib's Pontryagin dual, of cardinality `|Γ|`), and `∑_ψ P_ψ = 1` by orthogonality. -/

noncomputable section
universe uΓ uA uB uE uF
namespace BC4lean.KKTheory

open scoped InnerProductSpace

/-! ## Unitary characters -/

section UnitaryCharacter

variable {Γ : Type uΓ} [Group Γ] (χ : Γ →* unitary ℂ)

theorem unitaryChar_star_mul_self (g : Γ) :
    star ((χ g : unitary ℂ) : ℂ) * ((χ g : unitary ℂ) : ℂ) = 1 :=
  Unitary.star_mul_self_of_mem (χ g).2

theorem unitaryChar_mul_star_self (g : Γ) :
    ((χ g : unitary ℂ) : ℂ) * star ((χ g : unitary ℂ) : ℂ) = 1 :=
  Unitary.mul_star_self_of_mem (χ g).2

theorem unitaryChar_mul (g h : Γ) :
    ((χ (g * h) : unitary ℂ) : ℂ) = ((χ g : unitary ℂ) : ℂ) * ((χ h : unitary ℂ) : ℂ) := by
  rw [map_mul]
  rfl

theorem unitaryChar_star (g : Γ) : star ((χ g : unitary ℂ) : ℂ) = ((χ g⁻¹ : unitary ℂ) : ℂ) := by
  rw [map_inv, ← Unitary.coe_star, Unitary.star_eq_inv]

end UnitaryCharacter

end BC4lean.KKTheory

namespace BC4lean

/-! ## The characters of a finite abelian group -/

section Dual

variable (Γ : Type uΓ) [CommGroup Γ] [Fintype Γ]

/-- The characters of a finite abelian group `Γ`: additive characters of `Additive Γ`. -/
abbrev CharacterDual := AddChar (Additive Γ) ℂ

variable {Γ}

namespace CharacterDual

theorem norm_apply (ψ : CharacterDual Γ) (g : Γ) : ‖ψ (Additive.ofMul g)‖ = 1 :=
  AddChar.norm_apply ψ _

theorem apply_ne_zero (ψ : CharacterDual Γ) (g : Γ) : ψ (Additive.ofMul g) ≠ 0 := by
  intro h
  have := norm_apply ψ g
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- A character as a homomorphism to the unit circle. -/
def toUnitary (ψ : CharacterDual Γ) : Γ →* unitary ℂ where
  toFun g := ⟨ψ (Additive.ofMul g), Unitary.mem_iff.mpr
    ⟨by rw [RCLike.star_def, ← AddChar.inv_apply_eq_conj, inv_mul_cancel₀ (apply_ne_zero ψ g)],
     by rw [RCLike.star_def, ← AddChar.inv_apply_eq_conj, mul_inv_cancel₀ (apply_ne_zero ψ g)]⟩⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [AddChar.map_add_eq_mul])

@[simp] theorem toUnitary_apply (ψ : CharacterDual Γ) (g : Γ) :
    ((toUnitary ψ g : unitary ℂ) : ℂ) = ψ (Additive.ofMul g) := rfl

/-- There are `|Γ|` characters. -/
theorem card_eq : Fintype.card (CharacterDual Γ) = Fintype.card Γ := by
  rw [AddChar.card_eq]
  exact Fintype.card_congr Additive.ofMul.symm

/-- Orthogonality of characters: `|Γ|⁻¹ ∑_g conj χ(g) ψ(g) = [χ = ψ]`. -/
theorem orthogonality (χ ψ : CharacterDual Γ) :
    (Fintype.card Γ : ℂ)⁻¹ * ∑ g : Γ, star ((toUnitary χ g : unitary ℂ) : ℂ) *
      ((toUnitary ψ g : unitary ℂ) : ℂ) = if χ = ψ then 1 else 0 := by
  have h := AddChar.wInner_cWeight_eq_boole χ ψ
  rw [RCLike.wInner_cWeight_eq_expect, Fintype.expect_eq_sum_div_card] at h
  simp only [RCLike.inner_apply] at h
  rw [← h, div_eq_inv_mul, Fintype.card_congr Additive.ofMul.symm]
  congr 1
  exact Fintype.sum_equiv Additive.ofMul _ _ fun g => by
    simp only [toUnitary_apply, RCLike.star_def]
    ring

/-- The dual orthogonality: `∑_ψ ψ(g) = |Γ| [g = 1]`. -/
theorem sum_apply [DecidableEq Γ] (g : Γ) :
    ∑ ψ : CharacterDual Γ, ((toUnitary ψ g : unitary ℂ) : ℂ) =
      if g = 1 then (Fintype.card Γ : ℂ) else 0 := by
  simp only [toUnitary_apply]
  rw [AddChar.sum_apply_eq_ite, Fintype.card_congr Additive.ofMul.symm]
  exact if_congr (by simp) rfl rfl

end CharacterDual

end Dual

end BC4lean

namespace BC4lean.KKTheory

open scoped InnerProductSpace

theorem adjointableMap_finsetSum_apply {B : Type uB} {E : Type uE} [NonUnitalCStarAlgebra B]
    [PartialOrder B] [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    {ι : Type*} (s : Finset ι) (f : ι → AdjointableMap B E E) (x : E) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, AdjointableMap.coe_add_apply, ih]

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE} {F : Type uF} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-! ## The character projection on an equivariant module -/

namespace EquivariantHilbertModule

section Projection

omit [StarOrderedRing B] [CompleteSpace E]

variable [Fintype Γ] [β.IsTrivial] (V : EquivariantHilbertModule β E) (χ : Γ →* unitary ℂ)

/-- The character projection `P_χ = |Γ|⁻¹ ∑_g conj χ(g) U_g`. -/
def charProjection : AdjointableMap B E E :=
  (Fintype.card Γ : ℂ)⁻¹ • ∑ g, star ((χ g : unitary ℂ) : ℂ) • V.actionOperator g

/-- `U_h P_χ = χ(h) P_χ`. -/
theorem actionOperator_mul_charProjection (h : Γ) :
    V.actionOperator h * V.charProjection χ = ((χ h : unitary ℂ) : ℂ) • V.charProjection χ := by
  rw [charProjection, mul_smul_comm, Finset.mul_sum,
    smul_comm ((χ h : unitary ℂ) : ℂ) ((Fintype.card Γ : ℂ)⁻¹)]
  congr 1
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  rw [Equiv.coe_mulLeft, actionOperator_mul, mul_smul_comm, smul_smul, unitaryChar_mul, star_mul',
    ← mul_assoc, unitaryChar_mul_star_self, one_mul]

/-- `P_χ U_h = χ(h) P_χ`. -/
theorem charProjection_mul_actionOperator (h : Γ) :
    V.charProjection χ * V.actionOperator h = ((χ h : unitary ℂ) : ℂ) • V.charProjection χ := by
  rw [charProjection, smul_mul_assoc, Finset.sum_mul,
    smul_comm ((χ h : unitary ℂ) : ℂ) ((Fintype.card Γ : ℂ)⁻¹)]
  congr 1
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => ?_
  rw [Equiv.coe_mulRight, actionOperator_mul, smul_mul_assoc, smul_smul, unitaryChar_mul,
    star_mul', mul_comm (star ((χ g : unitary ℂ) : ℂ)), ← mul_assoc, unitaryChar_mul_star_self,
    one_mul]

theorem charProjection_isStarProjection : IsStarProjection (V.charProjection χ) := by
  have hn : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine isStarProjection_iff'.mpr ⟨?_, ?_⟩
  · change ((Fintype.card Γ : ℂ)⁻¹ • ∑ g, star ((χ g : unitary ℂ) : ℂ) • V.actionOperator g) *
      V.charProjection χ = V.charProjection χ
    rw [smul_mul_assoc, Finset.sum_mul]
    simp_rw [smul_mul_assoc, actionOperator_mul_charProjection, smul_smul,
      unitaryChar_star_mul_self, one_smul]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hn, one_smul]
  · rw [charProjection, star_smul, star_sum, star_inv₀, star_natCast]
    congr 1
    refine Fintype.sum_equiv (Equiv.inv Γ) _ _ fun g => ?_
    rw [star_smul, star_star, star_actionOperator, Equiv.inv_apply, unitaryChar_star, inv_inv]

/-- The character projection commutes with every operator fixed by all conjugations. -/
theorem commute_charProjection {T : AdjointableMap B E E}
    (hT : ∀ g, V.conjugateOperator g T = T) : Commute (V.charProjection χ) T :=
  (Commute.sum_left _ _ _ fun g _ => (V.commute_actionOperator (hT g)).smul_left _).smul_left _

/-- The character projection commutes with the group action. -/
theorem charProjection_action (h : Γ) (x : E) :
    V.charProjection χ (V.action h x) = V.action h (V.charProjection χ x) := by
  have h1 := congrArg (fun T : AdjointableMap B E E => T x)
    ((V.charProjection_mul_actionOperator χ h).trans (V.actionOperator_mul_charProjection χ h).symm)
  simpa only [AdjointableMap.mul_apply, actionOperator_apply] using h1

/-- The character projection commutes with a grading preserved by the action. -/
theorem charProjection_grading
    {γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E}
    (hγ : V.PreservesGrading γ) (x : E) :
    V.charProjection χ (γ.grading x) = γ.grading (V.charProjection χ x) := by
  rw [charProjection, AdjointableMap.coe_smul_apply, AdjointableMap.coe_smul_apply,
    adjointableMap_finsetSum_apply, adjointableMap_finsetSum_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [AdjointableMap.coe_smul_apply, AdjointableMap.coe_smul_apply, actionOperator_apply,
    actionOperator_apply, hγ g x, map_smul]

/-- On the range of `P_χ` every `h` acts by the scalar `χ(h)`. -/
theorem action_of_charProjection_fixed {x : E} (hx : V.charProjection χ x = x) (h : Γ) :
    V.action h x = ((χ h : unitary ℂ) : ℂ) • x := by
  have h1 := congrArg (fun T : AdjointableMap B E E => T x)
    (V.actionOperator_mul_charProjection χ h)
  simp only [AdjointableMap.mul_apply, AdjointableMap.coe_smul_apply, actionOperator_apply,
    hx] at h1
  exact h1

/-- If every `h` acts by the scalar `ψ(h)`, then `P_χ` is the scalar `|Γ|⁻¹ ∑_g conj χ(g) ψ(g)`. -/
theorem charProjection_of_action {ψ : Γ →* unitary ℂ}
    (hV : ∀ h x, V.action h x = ((ψ h : unitary ℂ) : ℂ) • x) :
    V.charProjection χ = ((Fintype.card Γ : ℂ)⁻¹ *
      ∑ g, star ((χ g : unitary ℂ) : ℂ) * ((ψ g : unitary ℂ) : ℂ)) • 1 := by
  have hU : ∀ g, V.actionOperator g = ((ψ g : unitary ℂ) : ℂ) • 1 := fun g => by
    ext x
    rw [actionOperator_apply, AdjointableMap.coe_smul_apply, AdjointableMap.one_apply, hV]
  rw [charProjection, mul_smul, Finset.sum_smul]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hU, smul_smul]

end Projection

section Sum

omit [CompleteSpace E] [CompleteSpace F]

variable [Fintype Γ] [β.IsTrivial] (χ : Γ →* unitary ℂ)

/-- The character projection of a direct-sum action is diagonal. -/
theorem sum_charProjection (U : EquivariantHilbertModule β E) (V : EquivariantHilbertModule β F) :
    (U.sum V).charProjection χ = sumMap (U.charProjection χ) (V.charProjection χ) := by
  simp only [charProjection, sum_actionOperator, ← sumMap_smul, sumMap_finsetSum]

end Sum

section Fibre

variable {X M : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]
  [Fintype Γ] [β.IsTrivial] (χ : Γ →* unitary ℂ)

/-- The fibre of a character projection is the character projection on the fibre. -/
theorem fibre_charProjection (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)
    (t : X) : hilbertModuleFibreOperator (B := B) t (U.charProjection χ) =
      (U.fibre t).charProjection χ := by
  have hsum : ∀ f : Γ → AdjointableMap C(X, B) M M, hilbertModuleFibreOperator (B := B) t
      (∑ g, f g) = ∑ g, hilbertModuleFibreOperator (B := B) t (f g) := fun f => by
    change hilbertModuleFibreOperatorHom (B := B) (M := M) t _ = _
    rw [map_sum]
    rfl
  simp only [charProjection, hilbertModuleFibreOperator_smul, hsum, U.fibre_actionOperator]

end Fibre

section DualSum

omit [StarOrderedRing B] [CompleteSpace E]

variable {Λ : Type uΓ} [CommGroup Λ] [Fintype Λ] {β' : CStarAlgebraAction Λ B} [β'.IsTrivial]

/-- For a finite abelian group the character projections add up to `1`. -/
theorem sum_charProjection_dual (V : EquivariantHilbertModule β' E) :
    ∑ ψ : CharacterDual Λ, V.charProjection (CharacterDual.toUnitary ψ) = 1 := by
  classical
  have hn : (Fintype.card Λ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have key : ∀ g : Λ, ∑ ψ : CharacterDual Λ,
      star ((CharacterDual.toUnitary ψ g : unitary ℂ) : ℂ) =
        if g = 1 then (Fintype.card Λ : ℂ) else 0 := fun g => by
    rw [← star_sum, CharacterDual.sum_apply]
    split_ifs <;> simp
  have hswap : ∑ ψ : CharacterDual Λ, V.charProjection (CharacterDual.toUnitary ψ) =
      (Fintype.card Λ : ℂ)⁻¹ • ∑ g, (∑ ψ : CharacterDual Λ,
        star ((CharacterDual.toUnitary ψ g : unitary ℂ) : ℂ)) • V.actionOperator g := by
    simp only [charProjection, ← Finset.smul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
  rw [hswap]
  simp only [key, ite_smul, zero_smul, Fintype.sum_ite_eq', actionOperator_one]
  rw [smul_smul, inv_mul_cancel₀ hn, one_smul]

end DualSum

end EquivariantHilbertModule

/-! ## Isomorphisms intertwine the character projections -/

namespace KasparovCycleIso

variable {c : KasparovCycle α β E} {d : KasparovCycle α β F}

theorem transport_actionOperator [β.IsTrivial] (u : KasparovCycleIso c d) (g : Γ) :
    u.moduleEquiv.transport (c.groupAction.actionOperator g) = d.groupAction.actionOperator g := by
  ext y
  rw [HilbertModuleEquiv.transport_apply, EquivariantHilbertModule.actionOperator_apply,
    EquivariantHilbertModule.actionOperator_apply, u.action_intertwine,
    HilbertModuleEquiv.apply_symm_apply]

theorem transport_charProjection [Fintype Γ] [β.IsTrivial] (u : KasparovCycleIso c d)
    (χ : Γ →* unitary ℂ) : u.moduleEquiv.transport (c.groupAction.charProjection χ) =
      d.groupAction.charProjection χ := by
  have h : ∀ T, u.moduleEquiv.transport T = u.moduleEquiv.transportStarAlgEquiv T := fun _ => rfl
  rw [EquivariantHilbertModule.charProjection, EquivariantHilbertModule.charProjection, h,
    map_smul, map_sum]
  simp only [← h, HilbertModuleEquiv.transport_smul, transport_actionOperator]

/-- An isomorphism intertwines the character projections. -/
theorem charProjection_intertwine [Fintype Γ] [β.IsTrivial] (u : KasparovCycleIso c d)
    (χ : Γ →* unitary ℂ) (x : E) : u.moduleEquiv (c.groupAction.charProjection χ x) =
      d.groupAction.charProjection χ (u.moduleEquiv x) := by
  rw [← transport_charProjection u χ, HilbertModuleEquiv.transport_apply,
    HilbertModuleEquiv.symm_apply_apply]

end KasparovCycleIso

namespace OddKasparovCycleIso

variable {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}

theorem transport_actionOperator [β.IsTrivial] (u : OddKasparovCycleIso c d) (g : Γ) :
    u.moduleEquiv.transport (c.groupAction.actionOperator g) = d.groupAction.actionOperator g := by
  ext y
  rw [HilbertModuleEquiv.transport_apply, EquivariantHilbertModule.actionOperator_apply,
    EquivariantHilbertModule.actionOperator_apply, u.action_intertwine,
    HilbertModuleEquiv.apply_symm_apply]

theorem transport_charProjection [Fintype Γ] [β.IsTrivial] (u : OddKasparovCycleIso c d)
    (χ : Γ →* unitary ℂ) : u.moduleEquiv.transport (c.groupAction.charProjection χ) =
      d.groupAction.charProjection χ := by
  have h : ∀ T, u.moduleEquiv.transport T = u.moduleEquiv.transportStarAlgEquiv T := fun _ => rfl
  rw [EquivariantHilbertModule.charProjection, EquivariantHilbertModule.charProjection, h,
    map_smul, map_sum]
  simp only [← h, HilbertModuleEquiv.transport_smul, transport_actionOperator]

/-- An isomorphism of odd cycles intertwines the character projections. -/
theorem charProjection_intertwine [Fintype Γ] [β.IsTrivial] (u : OddKasparovCycleIso c d)
    (χ : Γ →* unitary ℂ) (x : E) : u.moduleEquiv (c.groupAction.charProjection χ x) =
      d.groupAction.charProjection χ (u.moduleEquiv x) := by
  rw [← transport_charProjection u χ, HilbertModuleEquiv.transport_apply,
    HilbertModuleEquiv.symm_apply_apply]

end OddKasparovCycleIso

/-! ## Even character parts -/

section Even

variable [Fintype Γ] [α.IsTrivial] [β.IsTrivial] (χ : Γ →* unitary ℂ)

namespace KasparovCycle

/-- If the operator commutes with the whole group action, `P_χ` reduces the cycle. -/
theorem reducingProjection_charProjection (c : KasparovCycle α β E)
    (hF : ∀ g, c.groupAction.conjugateOperator g c.operator = c.operator) :
    c.ReducingProjection (c.groupAction.charProjection χ) where
  isStarProjection := c.groupAction.charProjection_isStarProjection χ
  commute_operator := c.groupAction.commute_charProjection χ hF
  commute_representation a := c.groupAction.commute_charProjection χ fun g => by
    rw [c.representation_equivariant, CStarAlgebraAction.IsTrivial.apply_eq]
  grading x := c.groupAction.charProjection_grading χ c.grading_preserved x
  action h x := c.groupAction.charProjection_action χ h x

theorem reducingProjection_equivariantCycle_char (c : KasparovCycle α β E) :
    c.equivariantCycle.ReducingProjection (c.groupAction.charProjection χ) :=
  c.equivariantCycle.reducingProjection_charProjection χ c.conjugateOperator_equivariantOperator

/-- The `χ`-part: the compression of the canonical representative to `P_χ`. -/
def charPart (c : KasparovCycle α β E) :
    KasparovCycle α β (ProjectionModule (c.groupAction.charProjection χ)) :=
  c.equivariantCycle.compress (c.reducingProjection_equivariantCycle_char χ)

/-- On the `χ`-part every `h` acts by `χ(h)`. -/
theorem charPart_action (c : KasparovCycle α β E)
    (y : ProjectionModule (c.groupAction.charProjection χ)) (h : Γ) :
    (c.charPart χ).groupAction.action h y = ((χ h : unitary ℂ) : ℂ) • y :=
  Subtype.ext (c.groupAction.action_of_charProjection_fixed χ y.property h)

end KasparovCycle

namespace KasparovCycleIso

variable {c : KasparovCycle α β E} {d : KasparovCycle α β F}

/-- An isomorphism of cycles restricts to an isomorphism of `χ`-parts. -/
def charPart (u : KasparovCycleIso c d) : KasparovCycleIso (c.charPart χ) (d.charPart χ) :=
  u.equivariantCycle.compress _ _ (u.charProjection_intertwine χ)

end KasparovCycleIso

section Fibre

variable {X M : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

/-- The fibre of a `χ`-part is the `χ`-part of the fibre. -/
def KasparovCycle.fibreCharPartIso (c : KasparovCycle α (β.continuousSections (X := X)) M)
    (t : X) : KasparovCycleIso ((c.charPart χ).fibre t) ((c.fibre t).charPart χ) :=
  (c.equivariantCycle.compressFibreIso (c.reducingProjection_equivariantCycle_char χ) t).trans
    ((c.fibreEquivariantCycleIso t).compress _ _ fun x => by
      change hilbertModuleFibreOperator (B := B) t (c.groupAction.charProjection χ) x =
        (c.fibre t).groupAction.charProjection χ x
      rw [c.groupAction.fibre_charProjection χ t]
      rfl)

end Fibre

namespace FullKasparovHomotopy

/-- The `χ`-part of the interval cycle of a full homotopy is a full homotopy between the
`χ`-parts of its endpoints. -/
def charPart {c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : FullKasparovHomotopy c d) :
    FullKasparovHomotopy (BundledKasparovCycle.of (c.cycle.charPart χ))
      (BundledKasparovCycle.of (d.cycle.charPart χ)) where
  intervalCycle := BundledKasparovCycle.of (h.intervalCycle.cycle.charPart χ)
  sourceIso := (h.intervalCycle.cycle.fibreCharPartIso χ 0).trans (h.sourceIso.charPart χ)
  targetIso := (h.intervalCycle.cycle.fibreCharPartIso χ 1).trans (h.targetIso.charPart χ)

end FullKasparovHomotopy

/-- The `χ`-part of a direct sum is the direct sum of the `χ`-parts. -/
def KasparovCycle.charPartDirectSumIso (c : KasparovCycle α β E) (d : KasparovCycle α β F) :
    KasparovCycleIso ((c.directSum d).charPart χ) ((c.charPart χ).directSum (d.charPart χ)) :=
  ((c.equivariantCycleDirectSumIso d).compress
    ((c.directSum d).reducingProjection_equivariantCycle_char χ)
    ((c.reducingProjection_equivariantCycle_char χ).directSum
      (d.reducingProjection_equivariantCycle_char χ))
    (fun x => by
      change (c.groupAction.sum d.groupAction).charProjection χ x = _
      rw [EquivariantHilbertModule.sum_charProjection]
      rfl)).trans
    (KasparovCycle.compressDirectSumDiagIso _ _)

namespace KasparovHomotopyClass

/-- The class of the `χ`-part; well defined because `χ`-parts respect cycle isomorphisms and
full homotopies. -/
def charClass :
    KasparovHomotopyClass.{uΓ, uA, uB, uE} α β → KasparovHomotopyClass.{uΓ, uA, uB, uE} α β :=
  Quotient.lift (fun c => mk (BundledKasparovCycle.of (c.cycle.charPart χ)))
    (fun c d h => by
      change BundledKasparovCycle.Homotopic c d at h
      induction h with
      | rel a b h =>
          change a.Isomorphic b ∨ Nonempty (FullKasparovHomotopy a b) at h
          rcases h with h | h
          · obtain ⟨u⟩ := h
            exact mk_eq_of_iso (u.charPart χ)
          · obtain ⟨h⟩ := h
            exact mk_eq_of_full (h.charPart χ)
      | refl => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b k _ _ hab hbk => exact hab.trans hbk)

@[simp] theorem charClass_mk (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    charClass χ (mk c) = mk (BundledKasparovCycle.of (c.cycle.charPart χ)) :=
  rfl

theorem charClass_add (x y : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) :
    charClass χ (x + y) = charClass χ x + charClass χ y := by
  induction x using Quotient.inductionOn with
  | h c =>
    induction y using Quotient.inductionOn with
    | h d =>
      exact mk_eq_of_iso (c.cycle.charPartDirectSumIso χ d.cycle)

/-- The `χ`-class as an additive map. -/
def charClassHom :
    KasparovHomotopyClass.{uΓ, uA, uB, uE} α β →+ KasparovHomotopyClass.{uΓ, uA, uB, uE} α β :=
  AddMonoidHom.mk' (charClass χ) (charClass_add χ)

@[simp] theorem charClassHom_apply (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) :
    charClassHom χ x = charClass χ x := rfl

end KasparovHomotopyClass

end Even

/-! ## Odd character parts -/

section Odd

variable [Fintype Γ] [α.IsTrivial] [β.IsTrivial] (χ : Γ →* unitary ℂ)

namespace OddKasparovCycle

/-- If the operator commutes with the whole group action, `P_χ` reduces the odd cycle. -/
theorem reducingProjection_charProjection (c : OddKasparovCycle α β E)
    (hF : ∀ g, c.groupAction.conjugateOperator g c.operator = c.operator) :
    c.ReducingProjection (c.groupAction.charProjection χ) where
  isStarProjection := c.groupAction.charProjection_isStarProjection χ
  commute_operator := c.groupAction.commute_charProjection χ hF
  commute_representation a := c.groupAction.commute_charProjection χ fun g => by
    rw [c.representation_equivariant, CStarAlgebraAction.IsTrivial.apply_eq]
  action h x := c.groupAction.charProjection_action χ h x

theorem reducingProjection_equivariantCycle_char (c : OddKasparovCycle α β E) :
    c.equivariantCycle.ReducingProjection (c.groupAction.charProjection χ) :=
  c.equivariantCycle.reducingProjection_charProjection χ c.conjugateOperator_equivariantOperator

/-- The `χ`-part of an odd cycle. -/
def charPart (c : OddKasparovCycle α β E) :
    OddKasparovCycle α β (ProjectionModule (c.groupAction.charProjection χ)) :=
  c.equivariantCycle.compress (c.reducingProjection_equivariantCycle_char χ)

/-- On the `χ`-part every `h` acts by `χ(h)`. -/
theorem charPart_action (c : OddKasparovCycle α β E)
    (y : ProjectionModule (c.groupAction.charProjection χ)) (h : Γ) :
    (c.charPart χ).groupAction.action h y = ((χ h : unitary ℂ) : ℂ) • y :=
  Subtype.ext (c.groupAction.action_of_charProjection_fixed χ y.property h)

end OddKasparovCycle

namespace OddKasparovCycleIso

variable {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}

/-- An isomorphism of odd cycles restricts to an isomorphism of `χ`-parts. -/
def charPart (u : OddKasparovCycleIso c d) :
    OddKasparovCycleIso (c.charPart χ) (d.charPart χ) :=
  u.equivariantCycle.compress _ _ (u.charProjection_intertwine χ)

end OddKasparovCycleIso

section Fibre

variable {X M : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

/-- The fibre of an odd `χ`-part is the `χ`-part of the fibre. -/
def OddKasparovCycle.fibreCharPartIso (c : OddKasparovCycle α (β.continuousSections (X := X)) M)
    (t : X) : OddKasparovCycleIso ((c.charPart χ).fibre t) ((c.fibre t).charPart χ) :=
  (c.equivariantCycle.compressFibreIso (c.reducingProjection_equivariantCycle_char χ) t).trans
    ((c.fibreEquivariantCycleIso t).compress _ _ fun x => by
      change hilbertModuleFibreOperator (B := B) t (c.groupAction.charProjection χ) x =
        (c.fibre t).groupAction.charProjection χ x
      rw [c.groupAction.fibre_charProjection χ t]
      rfl)

end Fibre

/-- The `χ`-part of an odd direct sum is the direct sum of the `χ`-parts. -/
def OddKasparovCycle.charPartDirectSumIso (c : OddKasparovCycle α β E)
    (d : OddKasparovCycle α β F) :
    OddKasparovCycleIso ((c.directSum d).charPart χ) ((c.charPart χ).directSum (d.charPart χ)) :=
  ((c.equivariantCycleDirectSumIso d).compress
    ((c.directSum d).reducingProjection_equivariantCycle_char χ)
    ((c.reducingProjection_equivariantCycle_char χ).directSum
      (d.reducingProjection_equivariantCycle_char χ))
    (fun x => by
      change (c.groupAction.sum d.groupAction).charProjection χ x = _
      rw [EquivariantHilbertModule.sum_charProjection]
      rfl)).trans
    (OddKasparovCycle.compressDirectSumDiagIso _ _)

variable [TopologicalSpace.SeparableSpace B]

namespace FullOddKasparovHomotopy

/-- The `χ`-part of an odd full homotopy. -/
def charPart {c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : FullOddKasparovHomotopy c d) :
    FullOddKasparovHomotopy (BundledOddKasparovCycle.of (c.cycle.charPart χ))
      (BundledOddKasparovCycle.of (d.cycle.charPart χ)) where
  intervalCycle := BundledOddKasparovCycle.of (h.intervalCycle.cycle.charPart χ)
  sourceIso := (h.intervalCycle.cycle.fibreCharPartIso χ 0).trans (h.sourceIso.charPart χ)
  targetIso := (h.intervalCycle.cycle.fibreCharPartIso χ 1).trans (h.targetIso.charPart χ)

end FullOddKasparovHomotopy

namespace OddKK

/-- The class of the `χ`-part of an odd cycle. -/
def charClass : OddKK.{uΓ, uA, uB, uE} α β → OddKK.{uΓ, uA, uB, uE} α β :=
  Quotient.lift (fun c => mk (BundledOddKasparovCycle.of (c.cycle.charPart χ)))
    (fun _ _ h => by
      obtain ⟨h⟩ := h
      exact Quotient.sound ⟨h.charPart χ⟩)

@[simp] theorem charClass_mk (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    charClass χ (mk c) = mk (BundledOddKasparovCycle.of (c.cycle.charPart χ)) :=
  rfl

theorem charClass_add (x y : OddKK.{uΓ, uA, uB, uE} α β) :
    charClass χ (x + y) = charClass χ x + charClass χ y := by
  induction x using Quotient.inductionOn with
  | h c =>
    induction y using Quotient.inductionOn with
    | h d =>
      exact mk_eq_of_iso (c.cycle.charPartDirectSumIso χ d.cycle)

/-- The `χ`-class of odd classes as an additive map. -/
def charClassHom : OddKK.{uΓ, uA, uB, uE} α β →+ OddKK.{uΓ, uA, uB, uE} α β :=
  AddMonoidHom.mk' (charClass χ) (charClass_add χ)

@[simp] theorem charClassHom_apply (x : OddKK.{uΓ, uA, uB, uE} α β) :
    charClassHom χ x = charClass χ x := rfl

end OddKK

end Odd

end BC4lean.KKTheory
