import BC4lean.FiniteAbelianCharacterProjection
import BC4lean.KasparovTrivialInflation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # KK of a finite abelian group with trivial actions splits over the characters

Let `Γ` be a finite abelian group acting trivially on `A` and on `B`, and let
`Γ̂ = CharacterDual Γ` be its character group. For `χ ∈ Γ̂`, `e_χ = charClassHom χ` is the
`χ`-class map of `FiniteAbelianCharacterProjection`. Then:

* every class is the sum of its character classes, `∑_χ e_χ x = x` (`sum_charClass`). The proof
  is an induction over a finite set `S ⊆ Γ̂`: if `P_ψ = 0` on a cycle for every `ψ ∉ S`, its class
  is `∑_{χ ∈ S} e_χ` of it. For `S = ∅` the projections `P_ψ` add up to `1` and all vanish, so the
  module is zero. For `S = insert χ₀ S'`, the class is `e_χ₀ [c] + [c']` with `c'` the compression
  of the canonical representative to `1 - P_χ₀`, which is `S'`-supported; and `e_χ [c'] = e_χ [c]`
  for `χ ≠ χ₀` because `e_χ` vanishes on the `χ₀`-part, where `Γ` acts through `χ₀`;
* `x ↦ (χ ↦ res (e_χ x))` is an additive equivalence `KK^Γ ≃+ (Γ̂ → KK)`, with inverse
  `u ↦ ∑_χ χ ⊗ infl (u χ)` (`KasparovHomotopyClass.charSplit`, `OddKK.charSplit`,
  `finiteAbelianKKParitySplit`), and, for the point, `KK^Γ_p(C₀(pt), ℂ) ≃+ (Γ̂ → KK_p(ℂ, ℂ))`
  (`finiteAbelianPointKKSplit`).

For `|Γ| = 2` this is the eigen split `orderTwoSplit`: the two characters are `1` and the sign. -/

noncomputable section
universe uΓ uA uB uE u
namespace BC4lean.KKTheory

open scoped InnerProductSpace
open CharacterDual

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE} [CommGroup Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-! ## Module-level facts -/

namespace EquivariantHilbertModule

omit [StarOrderedRing B] [CompleteSpace E]

variable [Fintype Γ] [β.IsTrivial] (V : EquivariantHilbertModule β E)

/-- The character projection of a restricted action is the restriction. -/
theorem restrict_charProjection_coe (P : AdjointableMap B E E)
    (hU : ∀ g x, P (V.action g x) = V.action g (P x)) (χ : Γ →* unitary ℂ)
    (y : ProjectionModule P) :
    ((V.restrict P hU).charProjection χ y : E) = V.charProjection χ (y : E) := by
  simp only [charProjection, AdjointableMap.coe_smul_apply, adjointableMap_finsetSum_apply,
    Submodule.coe_smul, Submodule.coe_sum, actionOperator_apply, restrict_coe]

/-- If `Γ` acts through the character `ψ`, then `P_χ = 0` for `χ ≠ ψ`. -/
theorem charProjection_eq_zero_of_action {χ ψ : CharacterDual Γ} (hne : χ ≠ ψ)
    (hV : ∀ h x, V.action h x = ((toUnitary ψ h : unitary ℂ) : ℂ) • x) :
    V.charProjection (toUnitary χ) = 0 := by
  rw [V.charProjection_of_action _ hV, CharacterDual.orthogonality, if_neg hne, zero_smul]

end EquivariantHilbertModule

/-! ## Even classes -/

section Even

variable [Fintype Γ] [α.IsTrivial] [β.IsTrivial]

omit [Fintype Γ] [α.IsTrivial] [β.IsTrivial] in
/-- A cycle on the zero module is degenerate. -/
theorem KasparovCycle.isDegenerate_of_subsingleton (c : KasparovCycle α β E) (hE : Subsingleton E) :
    c.IsDegenerate := by
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ _ => ?_⟩ <;>
    exact AdjointableMap.ext fun _ => Subsingleton.elim _ _

namespace KasparovHomotopyClass

theorem charClass_mk_eq_zero (χ : Γ →* unitary ℂ)
    (c : KasparovCycle α β E) (h0 : c.groupAction.charProjection χ = 0) :
    charClass χ (mk.{uΓ, uA, uB, uE} (BundledKasparovCycle.of c)) = 0 := by
  have := projectionModule_subsingleton_of_eq_zero h0
  exact mk_eq_zero_of_degenerate _ (KasparovCycle.isDegenerate_of_subsingleton _ this)

/-- If `P_ψ` vanishes on a cycle for every `ψ ∉ S`, its class is the sum of its `χ`-classes over
`χ ∈ S`. -/
theorem mk_eq_sum_charClass_of_support (S : Finset (CharacterDual Γ)) :
    ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
      [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] (c : KasparovCycle α β E),
      (∀ ψ ∉ S, c.groupAction.charProjection (toUnitary ψ) = 0) →
        mk.{uΓ, uA, uB, uE} (BundledKasparovCycle.of c) =
          ∑ χ ∈ S, charClass (toUnitary χ) (mk (BundledKasparovCycle.of c)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro E _ _ _ _ _ c hc
    have h1 : (1 : AdjointableMap B E E) = 0 := by
      rw [← c.groupAction.sum_charProjection_dual]
      exact Finset.sum_eq_zero fun ψ _ => hc ψ (by simp)
    have : Subsingleton E := ⟨fun x y => by
      have h0 : ∀ z : E, z = 0 := fun z => by
        simpa using congrArg (fun T : AdjointableMap B E E => T z) h1
      rw [h0 x, h0 y]⟩
    rw [Finset.sum_empty]
    exact mk_eq_zero_of_degenerate _ (KasparovCycle.isDegenerate_of_subsingleton _ this)
  | insert χ₀ S hχ₀ ih =>
    intro E _ _ _ _ _ c hc
    have hP := c.reducingProjection_equivariantCycle_char (toUnitary χ₀)
    have hsplit : mk.{uΓ, uA, uB, uE} (BundledKasparovCycle.of c) =
        charClass (toUnitary χ₀) (mk (BundledKasparovCycle.of c)) +
          mk (BundledKasparovCycle.of (c.equivariantCycle.compress hP.one_sub)) :=
      c.mk_equivariantCycle.trans (c.equivariantCycle.mk_eq_add_compress hP)
    have hc' : ∀ ψ ∉ S, (c.equivariantCycle.compress hP.one_sub).groupAction.charProjection
        (toUnitary ψ) = 0 := fun ψ hψ => by
      refine AdjointableMap.ext fun y => ?_
      rw [AdjointableMap.coe_zero_apply]
      apply Subtype.ext
      have hcoe : ((c.equivariantCycle.compress hP.one_sub).groupAction.charProjection
          (toUnitary ψ) y : E) = c.groupAction.charProjection (toUnitary ψ) (y : E) :=
        EquivariantHilbertModule.restrict_charProjection_coe _ _ _ _ y
      rw [hcoe, ZeroMemClass.coe_zero]
      by_cases hψ₀ : ψ = χ₀
      · rw [hψ₀]
        have hy : (1 - c.groupAction.charProjection (toUnitary χ₀)) (y : E) = (y : E) :=
          y.property
        have hid : c.groupAction.charProjection (toUnitary χ₀) *
            c.groupAction.charProjection (toUnitary χ₀) =
              c.groupAction.charProjection (toUnitary χ₀) :=
          (c.groupAction.charProjection_isStarProjection _).isIdempotentElem.eq
        rw [← hy, AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, map_sub,
          ← AdjointableMap.mul_apply, hid, sub_self]
      · rw [hc ψ (by simp [hψ₀, hψ])]
        rfl
    have ih' := ih (c.equivariantCycle.compress hP.one_sub) hc'
    have hpart : ∀ χ ∈ S, charClass (toUnitary χ)
        (mk (BundledKasparovCycle.of (c.equivariantCycle.compress hP.one_sub))) =
          charClass (toUnitary χ) (mk (BundledKasparovCycle.of c)) := fun χ hχ => by
      have hne : χ ≠ χ₀ := fun h => hχ₀ (h ▸ hχ)
      have h0 : charClass (toUnitary χ)
          (charClass (toUnitary χ₀) (mk.{uΓ, uA, uB, uE} (BundledKasparovCycle.of c))) = 0 :=
        charClass_mk_eq_zero _ (c.charPart (toUnitary χ₀))
          (EquivariantHilbertModule.charProjection_eq_zero_of_action _ hne
            fun h y => c.charPart_action _ y h)
      rw [hsplit, charClass_add, h0, zero_add]
    rw [Finset.sum_insert hχ₀, ← Finset.sum_congr rfl hpart, ← ih']
    exact hsplit

/-- Every class is the sum of its character classes. -/
theorem sum_charClass (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) :
    ∑ χ : CharacterDual Γ, charClass (toUnitary χ) x = x := by
  induction x using Quotient.inductionOn with
  | h c =>
    exact (mk_eq_sum_charClass_of_support Finset.univ c.cycle
      fun ψ hψ => absurd (Finset.mem_univ ψ) hψ).symm

end KasparovHomotopyClass

end Even

section EvenSplit

variable [Fintype Γ] [α.IsTrivial] [β.IsTrivial]

namespace KasparovHomotopyClass

/-- A class on which `Γ` acts through `ψ` has no `χ`-class for `χ ≠ ψ`. -/
theorem charClass_twist_inflHom_of_ne {χ ψ : CharacterDual Γ} (hne : χ ≠ ψ)
    (b : UnitKK.{uA, uB, uE} A B) :
    charClass (toUnitary χ) (twist (toUnitary ψ) (inflHom (α := α) (β := β) b)) = 0 := by
  induction b using Quotient.inductionOn with
  | h c =>
    refine charClass_mk_eq_zero (toUnitary χ) _ ?_
    refine EquivariantHilbertModule.charProjection_eq_zero_of_action _ hne fun h x => ?_
    change ((toUnitary ψ h : unitary ℂ) : ℂ) •
      c.cycle.groupAction.action ((1 : Γ →* Unit) h) x = _
    exact congrArg (((toUnitary ψ h : unitary ℂ) : ℂ) • ·) (c.cycle.groupAction.one_apply x)

/-- A class on which `Γ` acts through `ψ` is its own `ψ`-class. -/
theorem charClass_twist_inflHom_self (ψ : CharacterDual Γ) (b : UnitKK.{uA, uB, uE} A B) :
    charClass (toUnitary ψ) (twist (toUnitary ψ) (inflHom (α := α) (β := β) b)) =
      twist (toUnitary ψ) (inflHom b) := by
  have h := sum_charClass (twist (toUnitary ψ) (inflHom (α := α) (β := β) b))
  rwa [Finset.sum_eq_single ψ (fun χ _ hχ => charClass_twist_inflHom_of_ne hχ b)
    (fun h => absurd (Finset.mem_univ ψ) h)] at h

/-- The `χ`-class, restricted to the trivial group, inflated and twisted by `χ`, gives the
`χ`-class back. -/
theorem twist_inflHom_resHom_charClass (χ : CharacterDual Γ)
    (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) :
    twist (toUnitary χ) (inflHom (resHom (charClass (toUnitary χ) x))) =
      charClass (toUnitary χ) x := by
  induction x using Quotient.inductionOn with
  | h c =>
    exact mk_eq_of_iso ((c.cycle.charPart (toUnitary χ)).inflResIso (toUnitary χ)
      fun h y => c.cycle.charPart_action _ y h)

/-- For a finite abelian group with trivial actions, even KK splits over the characters: the
`χ`-parts, read over the trivial group. -/
def charSplit :
    KasparovHomotopyClass.{uΓ, uA, uB, uE} α β ≃+ (CharacterDual Γ → UnitKK.{uA, uB, uE} A B)
    where
  toFun x χ := resHom (charClass (toUnitary χ) x)
  invFun u := ∑ χ, twist (toUnitary χ) (inflHom (u χ))
  left_inv x := by
    change ∑ χ, twist (toUnitary χ) (inflHom (resHom (charClass (toUnitary χ) x))) = x
    simp only [twist_inflHom_resHom_charClass]
    exact sum_charClass x
  right_inv u := by
    funext χ
    change resHom (charClass (toUnitary χ) (∑ ψ, twist (toUnitary ψ) (inflHom (u ψ)))) = u χ
    rw [← charClassHom_apply, map_sum]
    simp only [charClassHom_apply]
    rw [Finset.sum_eq_single χ (fun ψ _ hψ => charClass_twist_inflHom_of_ne (Ne.symm hψ) _)
      (fun h => absurd (Finset.mem_univ χ) h), charClass_twist_inflHom_self,
      resHom_twist_inflHom]
  map_add' x y := by
    funext χ
    simp only [charClass_add, map_add, Pi.add_apply]

end KasparovHomotopyClass

end EvenSplit

/-! ## Odd classes -/

section Odd

variable [Fintype Γ] [α.IsTrivial] [β.IsTrivial]

omit [Fintype Γ] [α.IsTrivial] [β.IsTrivial] in
/-- An odd cycle on the zero module is degenerate. -/
theorem OddKasparovCycle.isDegenerate_of_subsingleton (c : OddKasparovCycle α β E)
    (hE : Subsingleton E) : c.IsDegenerate := by
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ _ => ?_⟩ <;>
    exact AdjointableMap.ext fun _ => Subsingleton.elim _ _

variable [TopologicalSpace.SeparableSpace B]

namespace OddKK

theorem charClass_mk_eq_zero (χ : Γ →* unitary ℂ) (c : OddKasparovCycle α β E)
    (h0 : c.groupAction.charProjection χ = 0) :
    charClass χ (mk.{uΓ, uA, uB, uE} (BundledOddKasparovCycle.of c)) = 0 := by
  have := projectionModule_subsingleton_of_eq_zero h0
  exact mk_eq_zero_of_degenerate _ (OddKasparovCycle.isDegenerate_of_subsingleton _ this)

/-- Odd analogue of `KasparovHomotopyClass.mk_eq_sum_charClass_of_support`. -/
theorem mk_eq_sum_charClass_of_support (S : Finset (CharacterDual Γ)) :
    ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
      [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] (c : OddKasparovCycle α β E),
      (∀ ψ ∉ S, c.groupAction.charProjection (toUnitary ψ) = 0) →
        mk.{uΓ, uA, uB, uE} (BundledOddKasparovCycle.of c) =
          ∑ χ ∈ S, charClass (toUnitary χ) (mk (BundledOddKasparovCycle.of c)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro E _ _ _ _ _ c hc
    have h1 : (1 : AdjointableMap B E E) = 0 := by
      rw [← c.groupAction.sum_charProjection_dual]
      exact Finset.sum_eq_zero fun ψ _ => hc ψ (by simp)
    have : Subsingleton E := ⟨fun x y => by
      have h0 : ∀ z : E, z = 0 := fun z => by
        simpa using congrArg (fun T : AdjointableMap B E E => T z) h1
      rw [h0 x, h0 y]⟩
    rw [Finset.sum_empty]
    exact mk_eq_zero_of_degenerate _ (OddKasparovCycle.isDegenerate_of_subsingleton _ this)
  | insert χ₀ S hχ₀ ih =>
    intro E _ _ _ _ _ c hc
    have hP := c.reducingProjection_equivariantCycle_char (toUnitary χ₀)
    have hsplit : mk.{uΓ, uA, uB, uE} (BundledOddKasparovCycle.of c) =
        charClass (toUnitary χ₀) (mk (BundledOddKasparovCycle.of c)) +
          mk (BundledOddKasparovCycle.of (c.equivariantCycle.compress hP.one_sub)) :=
      c.mk_equivariantCycle.trans (c.equivariantCycle.mk_eq_add_compress hP)
    have hc' : ∀ ψ ∉ S, (c.equivariantCycle.compress hP.one_sub).groupAction.charProjection
        (toUnitary ψ) = 0 := fun ψ hψ => by
      refine AdjointableMap.ext fun y => ?_
      rw [AdjointableMap.coe_zero_apply]
      apply Subtype.ext
      have hcoe : ((c.equivariantCycle.compress hP.one_sub).groupAction.charProjection
          (toUnitary ψ) y : E) = c.groupAction.charProjection (toUnitary ψ) (y : E) :=
        EquivariantHilbertModule.restrict_charProjection_coe _ _ _ _ y
      rw [hcoe, ZeroMemClass.coe_zero]
      by_cases hψ₀ : ψ = χ₀
      · rw [hψ₀]
        have hy : (1 - c.groupAction.charProjection (toUnitary χ₀)) (y : E) = (y : E) :=
          y.property
        have hid : c.groupAction.charProjection (toUnitary χ₀) *
            c.groupAction.charProjection (toUnitary χ₀) =
              c.groupAction.charProjection (toUnitary χ₀) :=
          (c.groupAction.charProjection_isStarProjection _).isIdempotentElem.eq
        rw [← hy, AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, map_sub,
          ← AdjointableMap.mul_apply, hid, sub_self]
      · rw [hc ψ (by simp [hψ₀, hψ])]
        rfl
    have ih' := ih (c.equivariantCycle.compress hP.one_sub) hc'
    have hpart : ∀ χ ∈ S, charClass (toUnitary χ)
        (mk (BundledOddKasparovCycle.of (c.equivariantCycle.compress hP.one_sub))) =
          charClass (toUnitary χ) (mk (BundledOddKasparovCycle.of c)) := fun χ hχ => by
      have hne : χ ≠ χ₀ := fun h => hχ₀ (h ▸ hχ)
      have h0 : charClass (toUnitary χ)
          (charClass (toUnitary χ₀) (mk.{uΓ, uA, uB, uE} (BundledOddKasparovCycle.of c))) = 0 :=
        charClass_mk_eq_zero _ (c.charPart (toUnitary χ₀))
          (EquivariantHilbertModule.charProjection_eq_zero_of_action _ hne
            fun h y => c.charPart_action _ y h)
      rw [hsplit, charClass_add, h0, zero_add]
    rw [Finset.sum_insert hχ₀, ← Finset.sum_congr rfl hpart, ← ih']
    exact hsplit

/-- Every odd class is the sum of its character classes. -/
theorem sum_charClass (x : OddKK.{uΓ, uA, uB, uE} α β) :
    ∑ χ : CharacterDual Γ, charClass (toUnitary χ) x = x := by
  induction x using Quotient.inductionOn with
  | h c =>
    exact (mk_eq_sum_charClass_of_support Finset.univ c.cycle
      fun ψ hψ => absurd (Finset.mem_univ ψ) hψ).symm

theorem charClass_twist_inflHom_of_ne {χ ψ : CharacterDual Γ} (hne : χ ≠ ψ)
    (b : UnitKK.{uA, uB, uE} A B) :
    charClass (toUnitary χ) (twist (toUnitary ψ) (inflHom (α := α) (β := β) b)) = 0 := by
  induction b using Quotient.inductionOn with
  | h c =>
    refine charClass_mk_eq_zero (toUnitary χ) _ ?_
    refine EquivariantHilbertModule.charProjection_eq_zero_of_action _ hne fun h x => ?_
    change ((toUnitary ψ h : unitary ℂ) : ℂ) •
      c.cycle.groupAction.action ((1 : Γ →* Unit) h) x = _
    exact congrArg (((toUnitary ψ h : unitary ℂ) : ℂ) • ·) (c.cycle.groupAction.one_apply x)

theorem charClass_twist_inflHom_self (ψ : CharacterDual Γ) (b : UnitKK.{uA, uB, uE} A B) :
    charClass (toUnitary ψ) (twist (toUnitary ψ) (inflHom (α := α) (β := β) b)) =
      twist (toUnitary ψ) (inflHom b) := by
  have h := sum_charClass (twist (toUnitary ψ) (inflHom (α := α) (β := β) b))
  rwa [Finset.sum_eq_single ψ (fun χ _ hχ => charClass_twist_inflHom_of_ne hχ b)
    (fun h => absurd (Finset.mem_univ ψ) h)] at h

theorem twist_inflHom_resHom_charClass (χ : CharacterDual Γ) (x : OddKK.{uΓ, uA, uB, uE} α β) :
    twist (toUnitary χ) (inflHom (resHom (charClass (toUnitary χ) x))) =
      charClass (toUnitary χ) x := by
  induction x using Quotient.inductionOn with
  | h c =>
    exact mk_eq_of_iso ((c.cycle.charPart (toUnitary χ)).inflResIso (toUnitary χ)
      fun h y => c.cycle.charPart_action _ y h)

/-- For a finite abelian group with trivial actions, odd KK splits over the characters. -/
def charSplit : OddKK.{uΓ, uA, uB, uE} α β ≃+ (CharacterDual Γ → UnitKK.{uA, uB, uE} A B) where
  toFun x χ := resHom (charClass (toUnitary χ) x)
  invFun u := ∑ χ, twist (toUnitary χ) (inflHom (u χ))
  left_inv x := by
    change ∑ χ, twist (toUnitary χ) (inflHom (resHom (charClass (toUnitary χ) x))) = x
    simp only [twist_inflHom_resHom_charClass]
    exact sum_charClass x
  right_inv u := by
    funext χ
    change resHom (charClass (toUnitary χ) (∑ ψ, twist (toUnitary ψ) (inflHom (u ψ)))) = u χ
    rw [← charClassHom_apply, map_sum]
    simp only [charClassHom_apply]
    rw [Finset.sum_eq_single χ (fun ψ _ hψ => charClass_twist_inflHom_of_ne (Ne.symm hψ) _)
      (fun h => absurd (Finset.mem_univ χ) h), charClass_twist_inflHom_self,
      resHom_twist_inflHom]
  map_add' x y := by
    funext χ
    simp only [charClass_add, map_add, Pi.add_apply]

end OddKK

end Odd

/-! ## Both parities, and the point -/

open GroupUniverseParityGroup

section Parity

variable [Fintype Γ] [α.IsTrivial] [β.IsTrivial] [TopologicalSpace.SeparableSpace B]

/-- For a finite abelian group acting trivially on `A` and `B`, `KK^Γ_p(A, B)` is a product of
copies of `KK_p(A, B)` over the trivial group, one for each character. -/
def finiteAbelianKKParitySplit (p : Bool) :
    KKParityGroup.{uΓ, uA, uB, uE} p α β ≃+
      (CharacterDual Γ → KKParityGroup.{0, uA, uB, uE} p
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit A)
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B)) :=
  match p with
  | false => KasparovHomotopyClass.charSplit
  | true => OddKK.charSplit

end Parity

section Point

open UnitPointCutoff
open scoped ZeroAtInfty ComplexOrder

variable [Fintype Γ] (X : Type) [TopologicalSpace X] [Subsingleton X] [MulAction Γ X]
  [ContinuousConstSMul Γ X]

/-- For a finite abelian group `Γ` acting on a point,
`KK^Γ_p(C₀(pt), ℂ) ≅ ∏_{χ ∈ Γ̂} KK_p(ℂ, ℂ)`: split over the characters
(`finiteAbelianKKParitySplit`), then pull back along `ℂ ≅ C₀(pt)` in each factor. -/
def finiteAbelianPointKKSplit (x : X) (p : Bool) :
    letI := cZero_separableSpace_of_subsingleton X x
    KKParityGroup.{uΓ, 0, 0, u} p (CZero.action Γ (X := X))
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) ≃+
      (CharacterDual Γ → KKParityGroup.{0, 0, 0, u} p
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) :=
  letI := cZero_separableSpace_of_subsingleton X x
  let e := sourcePullbackEquiv.{0, 0, 0, 0, u}
    (α := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))
    (β := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C₀(X, ℂ)))
    (γ := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) p
    (pointCZeroEquiv X x) (fun _ _ => by simp [CStarAlgebraAction.trivial])
  (finiteAbelianKKParitySplit p).trans (AddEquiv.piCongrRight fun _ => e)

end Point

end BC4lean.KKTheory
