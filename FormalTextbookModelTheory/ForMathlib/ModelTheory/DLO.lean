import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Bundled
import Mathlib.ModelTheory.Order
import Mathlib.Order.CountableDenseLinearOrder

import FormalTextbookModelTheory.ForMathlib.ModelTheory.Order
import FormalTextbookModelTheory.ForMathlib.Data.Fin.VecNotation


open Cardinal
open FirstOrder Language Structure Theory Order
open Matrix (Vector_eq_VecNotation₂ comp_VecNotation₂)

namespace FirstOrder.Language

namespace Order

section

variable {M : Type w} [instStructure : Language.order.Structure M]

/--
The interpretation of the unique binary relation symbol of the language `Language.order` on a type `M` gives a natural binary relation on `M` and it is written with `≤`.
-/
instance instLE : LE M where
  le := fun x y => instStructure.RelMap leSymb ![x, y]

/--
Given a type `M` and `𝓜 : Language.order.Structure`, the `Language.order.Structure M` instance induced by the `LE M`
instance which is induced by `𝓜` is equal to `𝓜`. In other words, for a fixed type `M`, `@orderStructure M` is the
left-inverse of `@instLE M`.
-/
@[simp]
lemma orderStructure_of_LE : @orderStructure M (@instLE M instStructure) = instStructure := by
  ext1
  · funext _ r
    exfalso
    exact IsEmpty.elim (by infer_instance) r
  · funext n r x
    match n with
    | 0 | 1 | _ + 3 =>
      exfalso
      simp only [Language.order, mk₂_Relations, Sequence₂] at r
      exact IsEmpty.elim (by infer_instance) r
    | 2 =>
      rw [Vector_eq_VecNotation₂ x, (by apply Subsingleton.allEq : r = leSymb)]
      simp only [orderStructure, LE.le, Structure.relMap_apply₂]

/--
By definition, the binary relation `≤` is equal to the interpretation of the unique binary relation symbol of the
language `Language.order`.
-/
instance : @OrderedStructure Language.order M _ instLE instStructure := by
  simp only [OrderedStructure, orderLHom_order, orderStructure_of_LE]
  exact @LHom.id_isExpansionOn Language.order M instStructure

end

section

variable {M : Type w} [Language.order.Structure M]
variable {N : Type w} [Language.order.Structure N]

/--
An order embedding `φ : M ↪o N`, induces and embedding of structures with the same underlying function.
-/
def toLEmbedding (φ : M ↪o N) : M ↪[Language.order] N where
  toEmbedding := φ.toEmbedding
  map_fun' := by
    intro n f
    exfalso
    exact IsEmpty.elim (by infer_instance) f
  map_rel' := by
    intro n r x
    match n with
    | 0 | 1 | _ + 3 =>
      exfalso
      simp [Language.order, Sequence₂] at r
      exact IsEmpty.elim (by infer_instance) r
    | 2 =>
      rw [Vector_eq_VecNotation₂ x, comp_VecNotation₂ φ.toFun,
          (by apply Subsingleton.allEq : r = leSymb), relMap_leSymb, relMap_leSymb]
      exact φ.map_rel_iff

/--
An order isomorphism `φ : M ≃o N`, induces and isomorphism of structures with the same underlying function.
-/
def toLIso (φ : M ≃o N) : M ≃[Language.order] N where
  toEquiv := φ.toEquiv
  map_fun' := (toLEmbedding (φ.toOrderEmbedding)).map_fun'
  map_rel' := (toLEmbedding (φ.toOrderEmbedding)).map_rel'

end

namespace DLO --region

section

variable {M : Type w} [instStructure : Language.order.Structure M]
variable [instModel : M ⊨ Language.order.dlo]

instance instPreorder : Preorder M where
  le := (@instLE M instStructure).le
  le_refl := by
    apply Relations.realize_reflexive.mp
    apply realize_sentence_of_mem Language.order.dlo
    simp only [reflexive_mem_dlo]
  le_trans := by
    apply Relations.realize_transitive.mp
    apply realize_sentence_of_mem Language.order.dlo
    simp only [transitive_mem_dlo]

instance instPartialOrder : PartialOrder M where
  toPreorder := @instPreorder M instStructure instModel
  le_antisymm := by
    apply Relations.realize_antisymmetric.mp
    apply realize_sentence_of_mem Language.order.dlo
    simp only [antisymmetric_mem_dlo]

noncomputable instance instLinearOrder : LinearOrder M where
  toPartialOrder := @instPartialOrder M instStructure instModel
  le_total := by
    apply Relations.realize_total.mp
    apply realize_sentence_of_mem Language.order.dlo
    simp only [total_mem_dlo]
  decidableLE := by apply Classical.decRel

-- @[simp]
-- lemma toLE_of_Preorder
--     : (@instPreorder M instStructure instModel).toLE = @instLE M instStructure := rfl

-- @[simp]
-- lemma toLE_of_PartialOrder
--     : (@instPartialOrder M instStructure instModel).toLE = @instLE M instStructure := rfl

-- @[simp]
-- lemma toLE_of_LinearOrder
--     : (@instLinearOrder M instStructure instModel).toLE = @instLE M instStructure := rfl

instance : @NoBotOrder M instLinearOrder.toLE where
  exists_not_ge := by
    apply Relations.realize_noBot.mp
    apply realize_sentence_of_mem Language.order.dlo
    simp only [noBotOrder_mem_dlo]

instance : @NoMinOrder M instLinearOrder.toLT := NoBotOrder.to_noMinOrder M

instance : @NoTopOrder M instLinearOrder.toLE where
  exists_not_le := by
    apply Relations.realize_noTop.mp
    apply realize_sentence_of_mem Language.order.dlo
    simp only [noTopOrder_mem_dlo]

instance : @NoMaxOrder M instLinearOrder.toLT := NoTopOrder.to_noMaxOrder M

instance : @DenselyOrdered M instLinearOrder.toLT where
  dense := by
    apply Relations.realize_denselyOrdered.mp
    apply realize_sentence_of_mem Language.order.dlo
    simp only [denselyOrdered_mem_dlo]

end

theorem aleph0_categorical_of_dlo : aleph0.Categorical Language.order.dlo := by
  unfold Categorical
  rintro ⟨M⟩ ⟨N⟩ hM hN
  simp only at *
  apply Nonempty.map toLIso
  have : Countable M := by apply mk_le_aleph0_iff.mp; rw [hM]
  have : Countable N := by apply mk_le_aleph0_iff.mp; rw [hN]
  apply iso_of_countable_dense

end DLO --end

end Order

end FirstOrder.Language
