import BC4lean.OrderTwoEigenSplitAdditive
import BC4lean.KasparovTrivialInflation
import BC4lean.FiniteReducedGroupCStar

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # KK for a group of order two with trivial actions splits into two copies of KK

Let `Γ = {1, g}` with `g` a central involution, let `Γ` act trivially on `A` and on `B`, and let
`χ : Γ →* unitary ℂ` be a character with `χ(g) = -1`. Write `KK^Γ` for the even (resp. odd) KK
group of `Γ`-equivariant cycles and `KK` for the group over the trivial group with trivial actions.

* `res : KK^Γ → KK` reads a cycle over the trivial group (pull back along `Unit →* Γ`);
* `infl : KK → KK^Γ` lets `Γ` act trivially on the module (pull back along `Γ →* Unit`);
* `twist : KK^Γ → KK^Γ` multiplies the module action by `χ`;
* `e₊`, `e₋` are the eigen classes (compressions of the canonical representative to the `±1`
  eigenspaces of `U_g`).

Then `x ↦ (res (e₊ x), res (e₋ x))` is an additive equivalence `KK^Γ ≃+ KK × KK`, with inverse
`(a, b) ↦ infl a + twist (infl b)` (`KasparovHomotopyClass.orderTwoSplit`,
`OddKK.orderTwoSplit`; for `Nat.card Γ = 2` and both parities, `orderTwoKKParitySplit`). The
action of `Γ` on `C₀(X)` for a one-point space `X` is trivial (`CZero.isTrivial_action`), so this
covers `KK^Γ_p(C₀(pt), ℂ)`. The proof uses `e₊ + e₋ = id`, the additivity of `e±`, and that `e_s` of
a cycle on which `g` acts by `-s` is zero (its eigenprojection is zero). -/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-! ## Cycle-level facts -/

namespace EquivariantHilbertModule

variable [β.IsTrivial] (V : EquivariantHilbertModule β E)

omit [StarOrderedRing B] [CompleteSpace E] in
/-- If `g` acts by the scalar `-s` with `s * s = 1`, the eigenprojection `P_s` vanishes. -/
theorem eigenProjection_eq_zero {g : Γ} {s : ℂ} (hs : s * s = 1)
    (hV : ∀ x, V.action g x = (-s) • x) : V.eigenProjection g s = 0 := by
  ext x
  simp only [eigenProjection, AdjointableMap.coe_smul_apply, AdjointableMap.coe_add_apply,
    AdjointableMap.one_apply, actionOperator_apply, hV, smul_smul]
  rw [show s * -s = -1 by rw [mul_neg, hs], neg_one_smul, add_neg_cancel, smul_zero]
  rfl

end EquivariantHilbertModule

section Even

variable [Fintype Γ] [β.IsTrivial] {g : Γ} (hg : CentralInvolution α g)
  {s : ℂ} (hs : s * s = 1) (hsr : star s = s)

namespace KasparovCycle

/-- On the `s`-eigen part the involution acts by `s`. -/
theorem eigenPart_action (c : KasparovCycle α β E)
    (y : ProjectionModule (c.groupAction.eigenProjection g s)) :
    (c.eigenPart hg hs hsr).groupAction.action g y = s • y :=
  Subtype.ext (c.groupAction.action_of_eigenProjection_fixed hg.mul_self hs y.property)

/-- A cycle with no `s`-eigenvectors has a degenerate `s`-eigen part. -/
theorem eigenPart_isDegenerate (c : KasparovCycle α β E)
    (hc : ∀ x, c.groupAction.action g x = (-s) • x) : (c.eigenPart hg hs hsr).IsDegenerate := by
  have := projectionModule_subsingleton_of_eq_zero (c.groupAction.eigenProjection_eq_zero hs hc)
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ _ => ?_⟩ <;>
    exact AdjointableMap.ext fun _ => Subsingleton.elim _ _

end KasparovCycle

namespace KasparovHomotopyClass

theorem eigenClass_mk_eq_zero (c : KasparovCycle α β E)
    (hc : ∀ x, c.groupAction.action g x = (-s) • x) :
    eigenClass hg hs hsr (mk (BundledKasparovCycle.of c)) = 0 :=
  mk_eq_zero_of_degenerate _ (c.eigenPart_isDegenerate hg hs hsr hc)

end KasparovHomotopyClass

end Even

/-! ## The splitting of the even group -/

section EvenSplit

variable [Fintype Γ] [α.IsTrivial] [β.IsTrivial] {g : Γ} (hg : CentralInvolution α g)
  (hΓ : ∀ h : Γ, h = 1 ∨ h = g) (χ : Γ →* unitary ℂ) (hχ : ((χ g : unitary ℂ) : ℂ) = -1)

namespace KasparovHomotopyClass

/-- `g` acts by `+1` on an inflated class, so its `-1` eigen class vanishes. -/
theorem eigenClass_neg_inflHom (a : UnitKK.{uA, uB, uE} A B) :
    eigenClass hg (s := -1) (by norm_num) (by simp) (inflHom (α := α) (β := β) a) = 0 := by
  induction a using Quotient.inductionOn with
  | h c =>
    refine eigenClass_mk_eq_zero hg _ _ _ fun x => ?_
    change c.cycle.groupAction.action ((1 : Γ →* Unit) g) x = (-(-1 : ℂ)) • x
    rw [neg_neg, one_smul, MonoidHom.one_apply, EquivariantHilbertModule.one_apply]

include hχ in
theorem eigenClass_pos_twist_inflHom (b : UnitKK.{uA, uB, uE} A B) :
    eigenClass hg (s := 1) (by norm_num) (by simp)
      (twist χ (inflHom (α := α) (β := β) b)) = 0 := by
  induction b using Quotient.inductionOn with
  | h c =>
    refine eigenClass_mk_eq_zero hg _ _ _ fun x => ?_
    change ((χ g : unitary ℂ) : ℂ) • c.cycle.groupAction.action ((1 : Γ →* Unit) g) x =
      (-1 : ℂ) • x
    rw [hχ]
    exact congrArg ((-1 : ℂ) • ·) (c.cycle.groupAction.one_apply x)

theorem eigenClass_pos_inflHom (a : UnitKK.{uA, uB, uE} A B) :
    eigenClass hg (s := 1) (by norm_num) (by simp) (inflHom (α := α) (β := β) a) =
      inflHom a := by
  have h := eigenClass_add_eigenClass hg (inflHom (α := α) (β := β) a)
  rwa [eigenClass_neg_inflHom hg, add_zero] at h

include hχ in
theorem eigenClass_neg_twist_inflHom (b : UnitKK.{uA, uB, uE} A B) :
    eigenClass hg (s := -1) (by norm_num) (by simp) (twist χ (inflHom (α := α) (β := β) b)) =
      twist χ (inflHom b) := by
  have h := eigenClass_add_eigenClass hg (twist χ (inflHom (α := α) (β := β) b))
  rwa [eigenClass_pos_twist_inflHom hg χ hχ, zero_add] at h

include hΓ in
theorem inflHom_resHom_eigenClass_pos (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) :
    inflHom (resHom (eigenClass hg (s := 1) (by norm_num) (by simp) x)) =
      eigenClass hg (s := 1) (by norm_num) (by simp) x := by
  induction x using Quotient.inductionOn with
  | h c =>
    refine mk_eq_of_iso (((KasparovCycle.twistTrivialIso 1 _ fun _ => rfl).symm).trans
      ((c.cycle.eigenPart hg (s := 1) (by norm_num) (by simp)).inflResIso 1 fun h y => ?_))
    rcases hΓ h with rfl | rfl
    · simp
    · rw [KasparovCycle.eigenPart_action, MonoidHom.one_apply, OneMemClass.coe_one]

include hΓ hχ in
theorem twist_inflHom_resHom_eigenClass_neg (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) :
    twist χ (inflHom (resHom (eigenClass hg (s := -1) (by norm_num) (by simp) x))) =
      eigenClass hg (s := -1) (by norm_num) (by simp) x := by
  induction x using Quotient.inductionOn with
  | h c =>
    refine mk_eq_of_iso
      ((c.cycle.eigenPart hg (s := -1) (by norm_num) (by simp)).inflResIso χ fun h y => ?_)
    rcases hΓ h with rfl | rfl
    · simp
    · rw [KasparovCycle.eigenPart_action, hχ]

include hΓ hχ in
/-- For `Γ = {1, g}` with trivial actions, even KK splits into two copies of KK over the trivial
group: the `+1` and `-1` eigen parts of `U_g`, read over the trivial group. -/
def orderTwoSplit :
    KasparovHomotopyClass.{uΓ, uA, uB, uE} α β ≃+ UnitKK.{uA, uB, uE} A B × UnitKK.{uA, uB, uE} A B
    where
  toFun x := (resHom (eigenClass hg (s := 1) (by norm_num) (by simp) x),
    resHom (eigenClass hg (s := -1) (by norm_num) (by simp) x))
  invFun p := inflHom p.1 + twist χ (inflHom p.2)
  left_inv x := by
    change inflHom (resHom (eigenClass hg (s := 1) (by norm_num) (by simp) x)) +
      twist χ (inflHom (resHom (eigenClass hg (s := -1) (by norm_num) (by simp) x))) = x
    rw [inflHom_resHom_eigenClass_pos hg hΓ, twist_inflHom_resHom_eigenClass_neg hg hΓ χ hχ,
      eigenClass_add_eigenClass]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · change resHom (eigenClass hg (s := 1) (by norm_num) (by simp)
        (inflHom a + twist χ (inflHom b))) = a
      rw [eigenClass_add, eigenClass_pos_inflHom hg, eigenClass_pos_twist_inflHom hg χ hχ,
        add_zero, resHom_inflHom]
    · change resHom (eigenClass hg (s := -1) (by norm_num) (by simp)
        (inflHom a + twist χ (inflHom b))) = b
      rw [eigenClass_add, eigenClass_neg_inflHom hg, eigenClass_neg_twist_inflHom hg χ hχ,
        zero_add, resHom_twist_inflHom]
  map_add' x y := by
    simp only [eigenClass_add, map_add, Prod.mk_add_mk]

end KasparovHomotopyClass

end EvenSplit

/-! ## Odd cycles -/

section Odd

variable [Fintype Γ] [β.IsTrivial] {g : Γ} (hg : CentralInvolution α g)
  {s : ℂ} (hs : s * s = 1) (hsr : star s = s)

namespace OddKasparovCycle

/-- On the `s`-eigen part the involution acts by `s`. -/
theorem eigenPart_action (c : OddKasparovCycle α β E)
    (y : ProjectionModule (c.groupAction.eigenProjection g s)) :
    (c.eigenPart hg hs hsr).groupAction.action g y = s • y :=
  Subtype.ext (c.groupAction.action_of_eigenProjection_fixed hg.mul_self hs y.property)

/-- A cycle with no `s`-eigenvectors has a degenerate `s`-eigen part. -/
theorem eigenPart_isDegenerate (c : OddKasparovCycle α β E)
    (hc : ∀ x, c.groupAction.action g x = (-s) • x) : (c.eigenPart hg hs hsr).IsDegenerate := by
  have := projectionModule_subsingleton_of_eq_zero (c.groupAction.eigenProjection_eq_zero hs hc)
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ _ => ?_⟩ <;>
    exact AdjointableMap.ext fun _ => Subsingleton.elim _ _

end OddKasparovCycle

namespace OddKK

variable [TopologicalSpace.SeparableSpace B]

theorem eigenClass_mk_eq_zero (c : OddKasparovCycle α β E)
    (hc : ∀ x, c.groupAction.action g x = (-s) • x) :
    eigenClass hg hs hsr (mk (BundledOddKasparovCycle.of c)) = 0 :=
  mk_eq_zero_of_degenerate _ (c.eigenPart_isDegenerate hg hs hsr hc)

end OddKK

end Odd

section OddSplit

variable [Fintype Γ] [α.IsTrivial] [β.IsTrivial] {g : Γ} (hg : CentralInvolution α g)
  (hΓ : ∀ h : Γ, h = 1 ∨ h = g) (χ : Γ →* unitary ℂ) (hχ : ((χ g : unitary ℂ) : ℂ) = -1)

namespace OddKK

variable [TopologicalSpace.SeparableSpace B]

/-- `g` acts by `+1` on an inflated class, so its `-1` eigen class vanishes. -/
theorem eigenClass_neg_inflHom (a : UnitKK.{uA, uB, uE} A B) :
    eigenClass hg (s := -1) (by norm_num) (by simp) (inflHom (α := α) (β := β) a) = 0 := by
  induction a using Quotient.inductionOn with
  | h c =>
    refine eigenClass_mk_eq_zero hg _ _ _ fun x => ?_
    change c.cycle.groupAction.action ((1 : Γ →* Unit) g) x = (-(-1 : ℂ)) • x
    rw [neg_neg, one_smul, MonoidHom.one_apply, EquivariantHilbertModule.one_apply]

include hχ in
theorem eigenClass_pos_twist_inflHom (b : UnitKK.{uA, uB, uE} A B) :
    eigenClass hg (s := 1) (by norm_num) (by simp)
      (twist χ (inflHom (α := α) (β := β) b)) = 0 := by
  induction b using Quotient.inductionOn with
  | h c =>
    refine eigenClass_mk_eq_zero hg _ _ _ fun x => ?_
    change ((χ g : unitary ℂ) : ℂ) • c.cycle.groupAction.action ((1 : Γ →* Unit) g) x =
      (-1 : ℂ) • x
    rw [hχ]
    exact congrArg ((-1 : ℂ) • ·) (c.cycle.groupAction.one_apply x)

theorem eigenClass_pos_inflHom (a : UnitKK.{uA, uB, uE} A B) :
    eigenClass hg (s := 1) (by norm_num) (by simp) (inflHom (α := α) (β := β) a) =
      inflHom a := by
  have h := eigenClass_add_eigenClass hg (inflHom (α := α) (β := β) a)
  rwa [eigenClass_neg_inflHom hg, add_zero] at h

include hχ in
theorem eigenClass_neg_twist_inflHom (b : UnitKK.{uA, uB, uE} A B) :
    eigenClass hg (s := -1) (by norm_num) (by simp) (twist χ (inflHom (α := α) (β := β) b)) =
      twist χ (inflHom b) := by
  have h := eigenClass_add_eigenClass hg (twist χ (inflHom (α := α) (β := β) b))
  rwa [eigenClass_pos_twist_inflHom hg χ hχ, zero_add] at h

include hΓ in
theorem inflHom_resHom_eigenClass_pos (x : OddKK.{uΓ, uA, uB, uE} α β) :
    inflHom (resHom (eigenClass hg (s := 1) (by norm_num) (by simp) x)) =
      eigenClass hg (s := 1) (by norm_num) (by simp) x := by
  induction x using Quotient.inductionOn with
  | h c =>
    refine mk_eq_of_iso (((OddKasparovCycle.twistTrivialIso 1 _ fun _ => rfl).symm).trans
      ((c.cycle.eigenPart hg (s := 1) (by norm_num) (by simp)).inflResIso 1 fun h y => ?_))
    rcases hΓ h with rfl | rfl
    · simp
    · rw [OddKasparovCycle.eigenPart_action, MonoidHom.one_apply, OneMemClass.coe_one]

include hΓ hχ in
theorem twist_inflHom_resHom_eigenClass_neg (x : OddKK.{uΓ, uA, uB, uE} α β) :
    twist χ (inflHom (resHom (eigenClass hg (s := -1) (by norm_num) (by simp) x))) =
      eigenClass hg (s := -1) (by norm_num) (by simp) x := by
  induction x using Quotient.inductionOn with
  | h c =>
    refine mk_eq_of_iso
      ((c.cycle.eigenPart hg (s := -1) (by norm_num) (by simp)).inflResIso χ fun h y => ?_)
    rcases hΓ h with rfl | rfl
    · simp
    · rw [OddKasparovCycle.eigenPart_action, hχ]

include hΓ hχ in
/-- For `Γ = {1, g}` with trivial actions, odd KK splits into two copies of KK over the trivial
group: the `+1` and `-1` eigen parts of `U_g`, read over the trivial group. -/
def orderTwoSplit :
    OddKK.{uΓ, uA, uB, uE} α β ≃+ UnitKK.{uA, uB, uE} A B × UnitKK.{uA, uB, uE} A B
    where
  toFun x := (resHom (eigenClass hg (s := 1) (by norm_num) (by simp) x),
    resHom (eigenClass hg (s := -1) (by norm_num) (by simp) x))
  invFun p := inflHom p.1 + twist χ (inflHom p.2)
  left_inv x := by
    change inflHom (resHom (eigenClass hg (s := 1) (by norm_num) (by simp) x)) +
      twist χ (inflHom (resHom (eigenClass hg (s := -1) (by norm_num) (by simp) x))) = x
    rw [inflHom_resHom_eigenClass_pos hg hΓ, twist_inflHom_resHom_eigenClass_neg hg hΓ χ hχ,
      eigenClass_add_eigenClass]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · change resHom (eigenClass hg (s := 1) (by norm_num) (by simp)
        (inflHom a + twist χ (inflHom b))) = a
      rw [eigenClass_add, eigenClass_pos_inflHom hg, eigenClass_pos_twist_inflHom hg χ hχ,
        add_zero, resHom_inflHom]
    · change resHom (eigenClass hg (s := -1) (by norm_num) (by simp)
        (inflHom a + twist χ (inflHom b))) = b
      rw [eigenClass_add, eigenClass_neg_inflHom hg, eigenClass_neg_twist_inflHom hg χ hχ,
        zero_add, resHom_twist_inflHom]
  map_add' x y := by
    simp only [eigenClass_add, map_add, Prod.mk_add_mk]

end OddKK

end OddSplit

/-! ## Groups of order two -/

section CardTwo

open GroupUniverseParityGroup BC4lean.OrderTwo

variable (h2 : Nat.card Γ = 2)

/-- The sign character of a group of order two, with values in the unit circle. -/
def orderTwoUnitarySign : Γ →* unitary ℂ :=
  (orderTwoSign h2).codRestrict (unitary ℂ) fun g => by
    by_cases hg : g = 1
    · rw [hg, orderTwoSign_one]
      exact one_mem _
    · rw [orderTwoSign_of_ne_one h2 hg]
      exact Unitary.mem_iff.mpr ⟨by simp, by simp⟩

theorem centralInvolution_orderTwoGenerator [α.IsTrivial] :
    CentralInvolution α (orderTwoGenerator h2) where
  mul_self := mul_self_eq_one_of_card_eq_two h2 _
  central h := by
    rcases eq_one_or_eq_orderTwoGenerator h2 h with rfl | rfl <;> simp
  fixes a := CStarAlgebraAction.IsTrivial.apply_eq _ a

theorem orderTwoUnitarySign_generator :
    ((orderTwoUnitarySign h2 (orderTwoGenerator h2) : unitary ℂ) : ℂ) = -1 :=
  orderTwoSign_of_ne_one h2 (orderTwoGenerator_ne_one h2)

variable [α.IsTrivial] [β.IsTrivial] [TopologicalSpace.SeparableSpace B]

/-- For a group of order two acting trivially on `A` and `B`, `KK^Γ_p(A, B)` is two copies of
`KK_p(A, B)` over the trivial group: the `+1` and `-1` eigen parts of the non-identity element. -/
def orderTwoKKParitySplit (p : Bool) :
    KKParityGroup.{uΓ, uA, uB, uE} p α β ≃+
      KKParityGroup.{0, uA, uB, uE} p (CStarAlgebraAction.trivial : CStarAlgebraAction Unit A)
          (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B) ×
        KKParityGroup.{0, uA, uB, uE} p (CStarAlgebraAction.trivial : CStarAlgebraAction Unit A)
          (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B) :=
  letI : Fintype Γ := @Fintype.ofFinite Γ (finite_of_card_eq_two h2)
  match p with
  | false => KasparovHomotopyClass.orderTwoSplit (centralInvolution_orderTwoGenerator h2)
      (eq_one_or_eq_orderTwoGenerator h2) (orderTwoUnitarySign h2)
      (orderTwoUnitarySign_generator h2)
  | true => OddKK.orderTwoSplit (centralInvolution_orderTwoGenerator h2)
      (eq_one_or_eq_orderTwoGenerator h2) (orderTwoUnitarySign h2)
      (orderTwoUnitarySign_generator h2)

end CardTwo

end BC4lean.KKTheory
