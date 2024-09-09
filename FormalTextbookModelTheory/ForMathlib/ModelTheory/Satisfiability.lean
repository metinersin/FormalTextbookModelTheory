import Mathlib.ModelTheory.Satisfiability
import FormalTextbookModelTheory.ForMathlib.ModelTheory.Syntax

namespace FirstOrder.Language.Theory

universe u v w
variable {L : Language.{u, v}} {T : L.Theory}
variable {α : Type w} {n : ℕ}

open BoundedFormula

scoped[FirstOrder] notation:50 A " ≡[" T "] " B =>
  FirstOrder.Language.Theory.SemanticallyEquivalent T A B

-- scoped[FirstOrder] notation:50 A " ≡ " B =>
--   FirstOrder.Language.Theory.SemanticallyEquivalent ∅ A B

namespace SemanticallyEquivalent

instance : Trans (@SemanticallyEquivalent L α n T) (@SemanticallyEquivalent L α n T)
    (@SemanticallyEquivalent L α n T)  where
  trans := SemanticallyEquivalent.trans

section congr

variable {φ φ₁ φ₂ ψ ψ₁ ψ₂ : L.BoundedFormula α n}
variable (h : φ ≡[T] ψ) (h₁ : φ₁ ≡[T] ψ₁) (h₂ : φ₂ ≡[T] ψ₂)
variable (f : L.BoundedFormula α n → L.BoundedFormula α n)
variable (g : L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n)

@[gcongr]
theorem not_congr : ∼φ ≡[T] ∼ψ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula at h ⊢
  intro M v xs
  replace h := h M v xs
  rw [BoundedFormula.realize_iff] at h ⊢
  rw [realize_not, realize_not]
  apply _root_.not_congr
  exact h

@[gcongr]
theorem inf_congr : φ₁ ⊓ φ₂ ≡[T] ψ₁ ⊓ ψ₂ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula at h₁ h₂ ⊢
  intro M v xs
  replace h₁ := h₁ M v xs
  replace h₂ := h₂ M v xs
  rw [BoundedFormula.realize_iff] at h₁ h₂ ⊢
  rw [realize_inf, realize_inf]
  exact and_congr h₁ h₂

@[gcongr]
theorem sup_congr : (φ₁ ⊔ φ₂) ≡[T] (ψ₁ ⊔ ψ₂) := by
  unfold SemanticallyEquivalent ModelsBoundedFormula at h₁ h₂ ⊢
  intro M v xs
  replace h₁ := h₁ M v xs
  replace h₂ := h₂ M v xs
  rw [BoundedFormula.realize_iff] at h₁ h₂ ⊢
  rw [realize_sup, realize_sup]
  exact or_congr h₁ h₂

@[gcongr]
theorem imp_congr : (φ₁ ⟹ φ₂) ≡[T] (ψ₁ ⟹ ψ₂) := by
  unfold SemanticallyEquivalent ModelsBoundedFormula at h₁ h₂ ⊢
  intro M v xs
  replace h₁ := h₁ M v xs
  replace h₂ := h₂ M v xs
  rw [BoundedFormula.realize_iff] at h₁ h₂ ⊢
  rw [realize_imp, realize_imp]
  exact _root_.imp_congr h₁ h₂

@[gcongr]
theorem iff_congr : (φ₁ ⇔ φ₂) ≡[T] (ψ₁ ⇔ ψ₂) := by
  unfold SemanticallyEquivalent ModelsBoundedFormula at h₁ h₂ ⊢
  intro M v xs
  replace h₁ := h₁ M v xs
  replace h₂ := h₂ M v xs
  rw [BoundedFormula.realize_iff] at h₁ h₂ ⊢
  rw [BoundedFormula.realize_iff, BoundedFormula.realize_iff]
  exact _root_.iff_congr h₁ h₂

@[gcongr]
theorem all_congr {φ ψ : L.BoundedFormula α (n + 1)} (h : φ ≡[T] ψ) : ∀' φ ≡[T] ∀' ψ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula at h ⊢
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_all, realize_all]
  apply forall_congr'
  intro a
  replace h := h M v (Fin.snoc xs a)
  rw [BoundedFormula.realize_iff] at h
  exact h

@[gcongr]
theorem ex_congr {φ ψ : L.BoundedFormula α (n + 1)} (h : φ ≡[T] ψ) : ∃' φ ≡[T] ∃' ψ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula at h ⊢
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_ex, realize_ex]
  replace h := h M v
  constructor
  · rintro ⟨a, h'⟩
    use a
    replace h := h (Fin.snoc xs a)
    rw [BoundedFormula.realize_iff] at h
    exact h.mp h'
  · rintro ⟨a, h'⟩
    use a
    replace h := h (Fin.snoc xs a)
    rw [BoundedFormula.realize_iff] at h
    exact h.mpr h'

end congr

section inf

theorem inf_bot (φ : L.BoundedFormula α n) : φ ⊓ ⊥ ≡[T] ⊥ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_inf, realize_bot, and_false]

theorem bot_inf (φ : L.BoundedFormula α n) : ⊥ ⊓ φ ≡[T] ⊥ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_inf, realize_bot, false_and]

theorem inf_top (φ : L.BoundedFormula α n) : φ ⊓ ⊤ ≡[T] φ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_inf, realize_top, and_true]

theorem top_inf (φ : L.BoundedFormula α n) : ⊤ ⊓ φ ≡[T] φ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_inf, realize_top, true_and]

theorem inf_comm (φ ψ : L.BoundedFormula α n) : (φ ⊓ ψ) ≡[T] (ψ ⊓ φ) := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_inf, realize_inf, and_comm]

theorem inf_assoc (φ ψ χ : L.BoundedFormula α n) : (φ ⊓ ψ) ⊓ χ ≡[T] φ ⊓ (ψ ⊓ χ) := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intros
  rw [BoundedFormula.realize_iff, realize_inf, realize_inf, realize_inf, realize_inf,
      and_assoc]

theorem inf_self (φ : L.BoundedFormula α n) : φ ⊓ φ ≡[T] φ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_inf, and_self]

end inf

section sup

theorem sup_bot (φ : L.BoundedFormula α n) : φ ⊔ ⊥ ≡[T] φ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_sup, realize_bot, or_false]

theorem bot_sup (φ : L.BoundedFormula α n) : ⊥ ⊔ φ ≡[T] φ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_sup, realize_bot, false_or]

theorem sup_top (φ : L.BoundedFormula α n) : φ ⊔ ⊤ ≡[T] ⊤ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_sup, realize_top, or_true]

theorem top_sup (φ : L.BoundedFormula α n) : ⊤ ⊔ φ ≡[T] ⊤ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_sup, realize_top, true_or]

theorem sup_comm (φ ψ : L.BoundedFormula α n) : (φ ⊔ ψ) ≡[T] (ψ ⊔ φ) := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_sup, realize_sup, or_comm]

theorem sup_assoc (φ ψ χ : L.BoundedFormula α n) : (φ ⊔ ψ) ⊔ χ ≡[T] φ ⊔ (ψ ⊔ χ) := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_sup, realize_sup, realize_sup, realize_sup, or_assoc]

theorem sup_self (φ : L.BoundedFormula α n) : φ ⊔ φ ≡[T] φ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_sup, or_self]

theorem inf_sup_left (φ ψ χ : L.BoundedFormula α n) : φ ⊓ (ψ ⊔ χ) ≡[T] (φ ⊓ ψ) ⊔ (φ ⊓ χ) := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_inf, realize_sup, realize_sup, realize_inf, realize_inf, and_or_left]

theorem inf_sup_right (φ ψ χ : L.BoundedFormula α n) : (φ ⊔ ψ) ⊓ χ ≡[T] (φ ⊓ χ) ⊔ (ψ ⊓ χ) := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_inf, realize_sup, realize_sup, realize_inf, realize_inf, or_and_right]

theorem sup_inf_left (φ ψ χ : L.BoundedFormula α n) : φ ⊔ (ψ ⊓ χ) ≡[T] (φ ⊔ ψ) ⊓ (φ ⊔ χ):= by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_inf, realize_sup, realize_sup, realize_inf, realize_sup, or_and_left]

theorem sup_inf_right (φ ψ χ : L.BoundedFormula α n) : (φ ⊓ ψ) ⊔ χ ≡[T] (φ ⊔ χ) ⊓ (ψ ⊔ χ)
    := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_inf, realize_sup, realize_inf, realize_sup, realize_sup, and_or_right]

theorem inf_absorption (φ ψ : L.BoundedFormula α n) : φ ⊓ (φ ⊔ ψ) ≡[T] φ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_inf, realize_sup]
  tauto

theorem sup_absorption (φ ψ : L.BoundedFormula α n) : φ ⊔ (φ ⊓ ψ) ≡[T] φ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_sup, realize_inf]
  tauto

end sup

section not

@[simp]
theorem not_top : ∼(⊤ : L.BoundedFormula α n) ≡[T] ⊥ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_not, realize_top, realize_bot, not_true]

@[simp]
theorem not_bot : ∼(⊥ : L.BoundedFormula α n) ≡[T] ⊤ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_not, realize_top, realize_bot, not_false_eq_true]

@[simp]
theorem not_not (φ : L.BoundedFormula α n) : ∼∼φ ≡[T] φ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_not, realize_not, Classical.not_not]

theorem not_inf_equiv_sup_not (φ ψ : L.BoundedFormula α n)
    : ∼(φ ⊓ ψ) ≡[T] (∼φ ⊔ ∼ψ) := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_not, realize_inf, realize_sup, realize_not, realize_not,
      Classical.not_and_iff_or_not_not]

theorem not_sup_equiv_inf_not (φ ψ : L.BoundedFormula α n)
    : ∼(φ ⊔ ψ) ≡[T] (∼φ ⊓ ∼ψ) := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_not, realize_inf, realize_sup, realize_not, realize_not]
  push_neg
  rfl

@[simp]
theorem em_right (φ : L.BoundedFormula α n) : φ ⊔ ∼φ ≡[T] ⊤ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, BoundedFormula.realize_sup, BoundedFormula.realize_not,
      BoundedFormula.realize_top, iff_true]
  apply Classical.em

@[simp]
theorem em_left (φ : L.BoundedFormula α n) : ∼φ ⊔ φ ≡[T] ⊤ := by
  calc _ ≡[T] φ ⊔ ∼φ := sup_comm _ _
       _ ≡[T] ⊤ := em_right _

theorem not_sup_eq_top (φ : L.BoundedFormula α n) : ∼φ ⊔ φ ≡[T] ⊤ := by apply em_left

theorem sup_not_eq_top (φ : L.BoundedFormula α n) : φ ⊔ ∼φ ≡[T] ⊤ := by apply em_right

theorem not_inf_eq_bot (φ : L.BoundedFormula α n) : ∼φ ⊓ φ ≡[T] ⊥ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, BoundedFormula.realize_inf, BoundedFormula.realize_not,
      BoundedFormula.realize_bot, iff_false]
  push_neg
  exact id

theorem inf_not_eq_bot (φ : L.BoundedFormula α n) : φ ⊓ ∼φ ≡[T] ⊥ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, BoundedFormula.realize_inf, BoundedFormula.realize_not,
      BoundedFormula.realize_bot, iff_false]
  push_neg
  exact id

end not

section iff

theorem iff_equiv_imp_inf_imp (φ ψ : L.BoundedFormula α n)
    : (φ ⇔ ψ) ≡[T] ((φ ⟹ ψ) ⊓ (ψ ⟹ φ)) := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, BoundedFormula.realize_inf, BoundedFormula.realize_imp,
      BoundedFormula.realize_imp, BoundedFormula.realize_iff]
  constructor
  <;> intro h
  <;> exact ⟨h.1, h.2⟩

end iff

section all

theorem all_inf_equiv_inf_all (φ ψ : L.BoundedFormula α (n + 1))
    : ∀' (φ ⊓ ψ) ≡[T] (∀' φ) ⊓ (∀' ψ) := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_all, realize_inf, realize_all, realize_all]
  constructor
  · intro h
    constructor
    <;> intro a
    <;> replace h := h a
    <;> rw [realize_inf] at h
    · exact h.1
    · exact h.2
  · rintro ⟨h₁, h₂⟩ a
    replace h₁ := h₁ a
    replace h₂ := h₂ a
    rw [realize_inf]
    exact ⟨h₁, h₂⟩

end all

section ex

theorem ex_sup_equiv_sup_ex (φ ψ : L.BoundedFormula α (n + 1))
    : ∃' (φ ⊔ ψ) ≡[T] (∃' φ) ⊔ (∃' ψ) := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_ex, realize_sup, realize_ex, realize_ex]
  constructor
  <;> intro h
  · rcases h with ⟨a, h⟩
    rw [realize_sup] at h
    rcases h with h | h
    · left; use a
    · right; use a
  · rcases h with h | h
    <;> rcases h with ⟨a, h⟩
    <;> use a
    <;> rw [realize_sup]
    · left; exact h
    · right; exact h

theorem not_all_equiv_ex_not (φ : L.BoundedFormula α (n + 1)) : ∼(∀' φ) ≡[T] ∃' ∼φ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_not, realize_all, realize_ex, not_forall]
  constructor
  <;> rintro ⟨a, h⟩
  <;> use a
  <;> rw [realize_not] at *
  <;> exact h

theorem not_ex_equiv_all_not (φ : L.BoundedFormula α (n + 1)) : ∼(∃' φ) ≡[T] ∀' ∼φ := by
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_iff, realize_not, realize_ex, realize_all, not_exists]
  constructor
  <;> intro h
  <;> intro a
  <;> replace h := h a
  <;> rw [realize_not] at *
  <;> exact h

theorem not_all_not_equiv_ex (φ : L.BoundedFormula α (n + 1)) : ∼(∀' ∼φ) ≡[T] ∃' φ := by
  calc _ ≡[T] ∃' ∼∼φ := by apply not_all_equiv_ex_not
       _ ≡[T] ∃' φ := by gcongr; apply not_not

theorem not_ex_not_equiv_all (φ : L.BoundedFormula α (n + 1)) : ∼(∃' ∼φ) ≡[T] ∀' φ := by
  calc _ ≡[T] ∀' ∼∼φ := by apply not_ex_equiv_all_not
       _ ≡[T] ∀' φ := by gcongr; apply not_not

end ex

section lInf

-- open Classical
open List

variable (φ : L.BoundedFormula α n)
variable (l l₁ l₂ : List (L.BoundedFormula α n))

-- def lInf_nil : lInf [] ≡[T] (⊤ : L.BoundedFormula α n) := by rfl

theorem lInf_cons : lInf (φ :: l) ≡[T] φ ⊓ lInf l := by
  induction l with
  | nil => rw [lInf_singleton, lInf_nil]
  | cons ψ l ih => rw [lInf_cons_cons]

def lInf_perm (l l' : List (L.BoundedFormula α n)) (p : l ~ l') :
    lInf l ≡[T] lInf l' := by
  induction p
  case nil => rfl
  case cons φ l l' p ih =>
    calc _ ≡[T] φ ⊓ lInf l := by apply lInf_cons
         _ ≡[T] φ ⊓ lInf l' := inf_congr (by rfl) ih
         _ ≡[T] lInf (φ :: l') := by apply lInf_cons
  case swap φ ψ l =>
    rw [lInf_cons_cons, lInf_cons_cons]
    calc _ ≡[T] ψ ⊓ (φ ⊓ lInf l) := inf_congr (by rfl) (by apply lInf_cons)
         _ ≡[T] (ψ ⊓ φ) ⊓ lInf l := by symm; apply inf_assoc
         _ ≡[T] (φ ⊓ ψ) ⊓ lInf l := inf_congr (inf_comm _ _) (by rfl)
         _ ≡[T] φ ⊓ (ψ ⊓ lInf l) := inf_assoc _ _ _
         _ ≡[T] φ ⊓ lInf (ψ :: l) := inf_congr (by rfl) (by symm; apply lInf_cons)
         _ ≡[T] _ := by rfl
  case trans p p' ih ih' =>
    trans
    · exact ih
    · exact ih'


end lInf

-- theorem models_top : T ⊨ᵇ (⊤ : L.BoundedFormula α n) := by
--   simp only [ModelsBoundedFormula, realize_top, implies_true]

-- theorem models_inf_iff_models_and_models (φ ψ : L.BoundedFormula α n) :
--     T ⊨ᵇ φ ⊓ ψ ↔ ((T ⊨ᵇ φ) ∧ (T ⊨ᵇ ψ)) := by
--   unfold ModelsBoundedFormula
--   simp only [realize_inf]
--   constructor <;> intro h
--   · constructor <;> intro M v xs
--     · exact (h M v xs).1
--     · exact (h M v xs).2
--   · intro M v xs
--     constructor
--     · exact h.1 M v xs
--     · exact h.2 M v xs

end SemanticallyEquivalent

end FirstOrder.Language.Theory
