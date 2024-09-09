import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm
import Mathlib.ModelTheory.Satisfiability
import Mathlib.Order.Lattice
import Mathlib.Order.BooleanAlgebra
import Mathlib.Algebra.Group.Defs
import FormalTextbookModelTheory.ForMathlib.ModelTheory.Satisfiability

namespace FirstOrder.Language.Theory

universe u v w
variable {L : Language.{u, v}}

def LindenbaumTarski (T : L.Theory) (α : Type w) (n : ℕ) :=
  Quotient $ @semanticallyEquivalentSetoid L α n T

namespace LindenbaumTarski

section

protected def mk {T : L.Theory} (φ : L.BoundedFormula α n) : T.LindenbaumTarski α n :=
  Quotient.mk'' φ

@[coe]
noncomputable def cast {T : L.Theory} (φ : T.LindenbaumTarski α n) : L.BoundedFormula α n :=
  Quotient.out' φ

@[simp]
theorem cast_mk {T : L.Theory} (φ : L.BoundedFormula α n) : cast (LindenbaumTarski.mk (T := T) φ) ≡[T] φ := by
  apply Quotient.mk_out' (s₁ := @semanticallyEquivalentSetoid L α n T)

@[simp]
theorem mk_cast {T : L.Theory} (φ : T.LindenbaumTarski α n) : LindenbaumTarski.mk φ.cast = φ := by
  apply Quotient.out_equiv_out.mp
  apply cast_mk

@[simp]
theorem quot_mk_eq_mk (T : L.Theory) (φ : L.BoundedFormula α n)
    : Quot.mk _ φ = LindenbaumTarski.mk (T := T) φ := rfl

@[simp]
theorem mk_eq_mk_iff_equiv {T : L.Theory} {φ ψ : L.BoundedFormula α n}
    : LindenbaumTarski.mk (T := T) φ = LindenbaumTarski.mk (T := T) ψ ↔ φ ≡[T] ψ :=
  Quotient.eq''

@[elab_as_elim]
theorem induction_on {T : L.Theory}
    (φ : T.LindenbaumTarski α n) {p : T.LindenbaumTarski α n → Prop}
    (H : ∀ φ, p (LindenbaumTarski.mk φ)) : p φ := by
  induction φ using Quotient.inductionOn'
  apply H

@[elab_as_elim]
theorem induction_on₂ {α' : Type w'} {n' : ℕ} {L' : Language.{u', v'}}
    {T : L.Theory} {T' : L'.Theory}
    (φ : T.LindenbaumTarski α n) (φ' : T'.LindenbaumTarski α' n')
    {p : T.LindenbaumTarski α n → T'.LindenbaumTarski α' n' → Prop}
    (H : ∀ φ φ', p (LindenbaumTarski.mk φ) (LindenbaumTarski.mk φ')) : p φ φ' := by
  induction φ using Quotient.inductionOn'
  induction φ' using Quotient.inductionOn'
  apply H

@[elab_as_elim]
theorem induction_on₃ {α' : Type w'} {n' : ℕ} {L' : Language.{u', v'}}
    {α'' : Type w''} {n'' : ℕ} {L'' : Language.{u'', v''}}
    {T : L.Theory} {T' : L'.Theory} {T'' : L''.Theory}
    (φ : T.LindenbaumTarski α n) (φ' : T'.LindenbaumTarski α' n')
    (φ'' : T''.LindenbaumTarski α'' n'')
    {p : T.LindenbaumTarski α n → T'.LindenbaumTarski α' n' → T''.LindenbaumTarski α'' n'' → Prop}
    (H : ∀ φ φ' φ'', p (LindenbaumTarski.mk φ) (LindenbaumTarski.mk φ') (LindenbaumTarski.mk φ'')) : p φ φ' φ'' := by
  induction φ using Quotient.inductionOn'
  induction φ' using Quotient.inductionOn'
  induction φ'' using Quotient.inductionOn'
  apply H

end

section

variable {α : Type w} {n : ℕ} {T : L.Theory}

section inf

def bot : T.LindenbaumTarski α n := LindenbaumTarski.mk ⊥
def top : T.LindenbaumTarski α n := LindenbaumTarski.mk ⊤

instance : Bot (T.LindenbaumTarski α n) := ⟨bot⟩
instance : Top (T.LindenbaumTarski α n) := ⟨top⟩

def inf (φ ψ : T.LindenbaumTarski α n) : T.LindenbaumTarski α n:= by
  apply Quotient.liftOn₂ φ ψ (fun φ ψ => LindenbaumTarski.mk (T := T) (φ ⊓ ψ))
  intro φ₁ ψ₁ φ₂ ψ₂ hφ hψ
  rw [mk_eq_mk_iff_equiv]
  exact SemanticallyEquivalent.inf_congr hφ hψ

instance instInf : Inf (T.LindenbaumTarski α n) := ⟨inf⟩

theorem inf_mk_eq_mk_inf {φ ψ : L.BoundedFormula α n}
    : LindenbaumTarski.mk (T := T) φ ⊓ LindenbaumTarski.mk ψ = LindenbaumTarski.mk (φ ⊓ ψ) := by
  simp only [instInf, LindenbaumTarski.inf]
  rfl

@[simp]
theorem inf_bot (φ : T.LindenbaumTarski α n) : φ ⊓ ⊥ = ⊥ := by
  induction φ using induction_on
  unfold Bot.bot instBot bot; dsimp only
  rw [inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.inf_bot

@[simp]
theorem bot_inf (φ : T.LindenbaumTarski α n) : ⊥ ⊓ φ = ⊥ := by
  induction φ using induction_on
  unfold Bot.bot instBot bot; dsimp only
  rw [inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.bot_inf

@[simp]
theorem inf_top (φ : T.LindenbaumTarski α n) : φ ⊓ ⊤ = φ := by
  induction φ using induction_on
  unfold Top.top instTop top; dsimp only
  rw [inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.inf_top

@[simp]
theorem top_inf (φ : T.LindenbaumTarski α n) : ⊤ ⊓ φ = φ := by
  induction φ using induction_on
  unfold Top.top instTop top; dsimp only
  rw [inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.top_inf

@[simp]
theorem inf_self (φ : T.LindenbaumTarski α n) : φ ⊓ φ = φ := by
  induction φ using induction_on
  rw [inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.inf_self

theorem inf_comm (φ ψ : T.LindenbaumTarski α n) : φ ⊓ ψ = ψ ⊓ φ := by
  induction φ, ψ using induction_on₂
  rw [inf_mk_eq_mk_inf, inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.inf_comm

theorem inf_assoc (φ ψ χ : T.LindenbaumTarski α n) : (φ ⊓ ψ) ⊓ χ = φ ⊓ (ψ ⊓ χ) := by
  induction φ, ψ, χ using induction_on₃
  rw [inf_mk_eq_mk_inf, inf_mk_eq_mk_inf, inf_mk_eq_mk_inf, inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.inf_assoc

instance instMonoid : Monoid (T.LindenbaumTarski α n) where
  mul := inf
  mul_assoc := inf_assoc
  one := ⊤
  one_mul := top_inf
  mul_one := inf_top

instance instCommMonoid : CommMonoid (T.LindenbaumTarski α n) where
  toMonoid := instMonoid
  mul_comm := inf_comm

instance : CommMonoidWithZero (T.LindenbaumTarski α n) where
  toCommMonoid := instCommMonoid
  zero := bot
  zero_mul := bot_inf
  mul_zero := inf_bot

end inf

section sup

def sup (φ ψ : T.LindenbaumTarski α n) : T.LindenbaumTarski α n := by
  apply Quotient.liftOn₂ φ ψ (fun φ ψ => LindenbaumTarski.mk (T := T) (φ ⊔ ψ))
  intro φ₁ ψ₁ φ₂ ψ₂ hφ hψ
  rw [mk_eq_mk_iff_equiv]
  exact SemanticallyEquivalent.sup_congr hφ hψ

instance instSup : Sup (T.LindenbaumTarski α n) := ⟨sup⟩

theorem sup_mk_eq_mk_sup {φ ψ : L.BoundedFormula α n}
    : LindenbaumTarski.mk (T := T) φ ⊔ LindenbaumTarski.mk ψ = LindenbaumTarski.mk (φ ⊔ ψ) := by
  simp only [instSup, LindenbaumTarski.sup]
  rfl

@[simp]
theorem sup_bot : (φ : T.LindenbaumTarski α n) ⊔ ⊥ = φ := by
  induction φ using induction_on
  unfold Bot.bot instBot bot; dsimp only
  rw [sup_mk_eq_mk_sup, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.sup_bot

@[simp]
theorem bot_sup : ⊥ ⊔ (φ : T.LindenbaumTarski α n) = φ := by
  induction φ using induction_on
  unfold Bot.bot instBot bot; dsimp only
  rw [sup_mk_eq_mk_sup, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.bot_sup

@[simp]
theorem sup_top : (φ : T.LindenbaumTarski α n) ⊔ ⊤ = ⊤ := by
  induction φ using induction_on
  unfold Top.top instTop top; dsimp only
  rw [sup_mk_eq_mk_sup, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.sup_top

@[simp]
theorem top_sup : ⊤ ⊔ (φ : T.LindenbaumTarski α n) = ⊤ := by
  induction φ using induction_on
  unfold Top.top instTop top; dsimp only
  rw [sup_mk_eq_mk_sup, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.top_sup

@[simp]
theorem sup_self (φ : T.LindenbaumTarski α n) : φ ⊔ φ = φ := by
  induction φ using induction_on
  rw [sup_mk_eq_mk_sup, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.sup_self

theorem sup_comm (φ ψ : T.LindenbaumTarski α n) : φ ⊔ ψ = ψ ⊔ φ := by
  induction φ, ψ using induction_on₂
  rw [sup_mk_eq_mk_sup, sup_mk_eq_mk_sup, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.sup_comm

theorem sup_assoc (φ ψ χ : T.LindenbaumTarski α n) : (φ ⊔ ψ) ⊔ χ = φ ⊔ (ψ ⊔ χ) := by
  induction φ, ψ, χ using induction_on₃
  rw [sup_mk_eq_mk_sup, sup_mk_eq_mk_sup, sup_mk_eq_mk_sup, sup_mk_eq_mk_sup, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.sup_assoc

theorem inf_sup_left (φ ψ χ : T.LindenbaumTarski α n) : φ ⊓ (ψ ⊔ χ) = (φ ⊓ ψ) ⊔ (φ ⊓ χ) := by
  induction φ, ψ, χ using induction_on₃
  rw [inf_mk_eq_mk_inf, inf_mk_eq_mk_inf, sup_mk_eq_mk_sup, sup_mk_eq_mk_sup, inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.inf_sup_left

theorem inf_sup_right (φ ψ χ : T.LindenbaumTarski α n) : (φ ⊔ ψ) ⊓ χ = (φ ⊓ χ) ⊔ (ψ ⊓ χ) := by
  induction φ, ψ, χ using induction_on₃
  rw [inf_mk_eq_mk_inf, inf_mk_eq_mk_inf, sup_mk_eq_mk_sup, sup_mk_eq_mk_sup, inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.inf_sup_right

theorem sup_inf_left (φ ψ χ : T.LindenbaumTarski α n) : φ ⊔ (ψ ⊓ χ) = (φ ⊔ ψ) ⊓ (φ ⊔ χ) := by
  induction φ, ψ, χ using induction_on₃
  rw [inf_mk_eq_mk_inf, sup_mk_eq_mk_sup, sup_mk_eq_mk_sup, sup_mk_eq_mk_sup, inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.sup_inf_left

theorem sup_inf_right (φ ψ χ : T.LindenbaumTarski α n) : (φ ⊓ ψ) ⊔ χ = (φ ⊔ χ) ⊓ (ψ ⊔ χ) := by
  induction φ, ψ, χ using induction_on₃
  rw [inf_mk_eq_mk_inf, sup_mk_eq_mk_sup, sup_mk_eq_mk_sup, sup_mk_eq_mk_sup, inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.sup_inf_right

@[simp]
theorem inf_absorption (φ ψ : T.LindenbaumTarski α n) : φ ⊓ (φ ⊔ ψ) = φ := by
  induction φ, ψ using induction_on₂
  rw [sup_mk_eq_mk_sup, inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.inf_absorption

@[simp]
theorem sup_absorption (φ ψ : T.LindenbaumTarski α n) : φ ⊔ (φ ⊓ ψ) = φ := by
  induction φ, ψ using induction_on₂
  rw [inf_mk_eq_mk_inf, sup_mk_eq_mk_sup, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.sup_absorption

end sup

section not

def not (φ : T.LindenbaumTarski α n) : T.LindenbaumTarski α n := by
  apply Quotient.liftOn φ (fun φ => LindenbaumTarski.mk (T := T) (∼φ))
  intro φ ψ h
  rw [mk_eq_mk_iff_equiv]
  exact SemanticallyEquivalent.not_congr h

scoped[FirstOrder] prefix:arg "∼" => FirstOrder.Language.Theory.LindenbaumTarski.not

theorem not_mk_eq_mk_not {φ : L.BoundedFormula α n}
    : ∼(LindenbaumTarski.mk (T := T) φ) = LindenbaumTarski.mk φ.not := by
  simp only [LindenbaumTarski.not]
  rfl

@[simp]
theorem not_top : ∼(⊤ : T.LindenbaumTarski α n) = ⊥ := by
  unfold Top.top instTop top Bot.bot instBot bot; dsimp only
  rw [not_mk_eq_mk_not, mk_eq_mk_iff_equiv]
  exact SemanticallyEquivalent.not_top

@[simp]
theorem top_not : ∼(⊥ : T.LindenbaumTarski α n) = ⊤ := by
  unfold Top.top instTop top Bot.bot instBot bot; dsimp only
  rw [not_mk_eq_mk_not, mk_eq_mk_iff_equiv]
  exact SemanticallyEquivalent.not_bot

@[simp]
theorem not_not (φ : T.LindenbaumTarski α n) : ∼∼φ = φ := by
  induction φ using induction_on
  rw [not_mk_eq_mk_not, not_mk_eq_mk_not, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.not_not

theorem not_inf_eq_sup_not (φ ψ : T.LindenbaumTarski α n)
    : ∼(φ ⊓ ψ) = ∼φ ⊔ ∼ψ := by
  induction φ, ψ using induction_on₂
  rw [not_mk_eq_mk_not, inf_mk_eq_mk_inf, not_mk_eq_mk_not, not_mk_eq_mk_not, sup_mk_eq_mk_sup, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.not_inf_equiv_sup_not

theorem not_sup_eq_inf_not (φ ψ : T.LindenbaumTarski α n)
    : ∼(φ ⊔ ψ) = ∼φ ⊓ ∼ψ := by
  induction φ, ψ using induction_on₂
  rw [not_mk_eq_mk_not, sup_mk_eq_mk_sup, not_mk_eq_mk_not, not_mk_eq_mk_not, inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.not_sup_equiv_inf_not

instance instHasCompl : HasCompl (T.LindenbaumTarski α n) where
  compl := LindenbaumTarski.not

@[simp]
theorem em_left (φ : T.LindenbaumTarski α n) : ∼φ ⊔ φ = ⊤ := by
  induction φ using induction_on
  unfold Top.top instTop top; dsimp only
  rw [not_mk_eq_mk_not, sup_mk_eq_mk_sup, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.em_left

@[simp]
theorem em_right (φ : T.LindenbaumTarski α n) : φ ⊔ ∼φ = ⊤ := by
  induction φ using induction_on
  unfold Top.top instTop top; dsimp only
  rw [not_mk_eq_mk_not, sup_mk_eq_mk_sup, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.em_right

@[simp]
theorem not_sup_eq_top (φ : T.LindenbaumTarski α n) : ∼φ ⊔ φ = ⊤ := by
  apply em_left

@[simp]
theorem sup_not_eq_top (φ : T.LindenbaumTarski α n) : φ ⊔ ∼φ = ⊤ := by
  apply em_right

@[simp]
theorem not_inf_eq_bot (φ : T.LindenbaumTarski α n) : ∼φ ⊓ φ = ⊥ := by
  induction φ using induction_on
  unfold Bot.bot instBot bot; dsimp only
  rw [not_mk_eq_mk_not, inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.not_inf_eq_bot

@[simp]
theorem inf_not_eq_bot (φ : T.LindenbaumTarski α n) : φ ⊓ ∼φ = ⊥ := by
  induction φ using induction_on
  unfold Bot.bot instBot bot; dsimp only
  rw [not_mk_eq_mk_not, inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.inf_not_eq_bot

end not

section imp

def imp (φ ψ : T.LindenbaumTarski α n) : T.LindenbaumTarski α n := by
  apply Quotient.liftOn₂ φ ψ (fun φ ψ => LindenbaumTarski.mk (T := T) (φ.imp ψ))
  intro φ₁ ψ₁ φ₂ ψ₂ hφ hψ
  rw [mk_eq_mk_iff_equiv]
  exact SemanticallyEquivalent.imp_congr hφ hψ

scoped[FirstOrder] infixr:62 " ⟹ " => FirstOrder.Language.Theory.LindenbaumTarski.imp

theorem imp_mk_eq_mk_imp {φ ψ : L.BoundedFormula α n}
    : (LindenbaumTarski.mk (T := T) φ) ⟹ (LindenbaumTarski.mk ψ) = LindenbaumTarski.mk (φ ⟹ ψ) := by
  unfold LindenbaumTarski.imp
  rfl

theorem imp_eq_not_sup (φ ψ : T.LindenbaumTarski α n) : φ ⟹ ψ = ∼φ ⊔ ψ := by
  induction φ, ψ using induction_on₂
  rw [imp_mk_eq_mk_imp, not_mk_eq_mk_not, sup_mk_eq_mk_sup, mk_eq_mk_iff_equiv]
  apply BoundedFormula.imp_semanticallyEquivalent_not_sup

end imp

section iff

def iff (φ ψ : T.LindenbaumTarski α n) : T.LindenbaumTarski α n := by
  apply Quotient.liftOn₂ φ ψ (fun φ ψ => LindenbaumTarski.mk (T := T) (φ.iff ψ))
  intro φ₁ ψ₁ φ₂ ψ₂ hφ hψ
  rw [mk_eq_mk_iff_equiv]
  exact SemanticallyEquivalent.iff_congr hφ hψ

scoped[FirstOrder] infixl:61 " ⇔ " => FirstOrder.Language.Theory.LindenbaumTarski.iff

theorem iff_mk_eq_mk_iff {φ ψ : L.BoundedFormula α n}
    : (LindenbaumTarski.mk (T := T) φ) ⇔ (LindenbaumTarski.mk ψ) = LindenbaumTarski.mk (φ ⇔ ψ) := by
  unfold LindenbaumTarski.iff
  rfl

theorem iff_eq_imp_inf_imp (φ ψ : T.LindenbaumTarski α n) : φ ⇔ ψ = (φ ⟹ ψ) ⊓ (ψ ⟹ φ) := by
  induction φ, ψ using induction_on₂
  rw [iff_mk_eq_mk_iff, imp_mk_eq_mk_imp, imp_mk_eq_mk_imp, inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.iff_equiv_imp_inf_imp

end iff

section order

def le (φ ψ : T.LindenbaumTarski α n) : Prop := T ⊨ᵇ φ.cast.imp ψ.cast

instance : LE (T.LindenbaumTarski α n) := ⟨le⟩

theorem le_iff_imp_semanticallyEquivalent_top (φ ψ : T.LindenbaumTarski α n)
    : φ ≤ ψ ↔ φ.cast.imp ψ.cast ≡[T] ⊤ := by
  unfold LE.le instLE le SemanticallyEquivalent ModelsBoundedFormula; dsimp only
  apply forall_congr'
  intro M
  apply forall_congr'
  intro v
  apply forall_congr'
  intro xs
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_iff, BoundedFormula.realize_imp, BoundedFormula.realize_top,
      iff_true]

theorem mk_le_mk_iff_models_imp {φ ψ : L.BoundedFormula α n}
    : (LindenbaumTarski.mk (T := T) φ ≤ LindenbaumTarski.mk ψ) ↔ T ⊨ᵇ (φ.imp ψ) := by
  unfold LE.le instLE le; dsimp only
  unfold ModelsBoundedFormula
  simp only [BoundedFormula.realize_imp]
  constructor <;> intro h M v xs <;> replace h := h M v xs <;> intro h'
  · rw [←SemanticallyEquivalent.realize_bd_iff (T := T) (cast_mk ψ)]
    rw [←SemanticallyEquivalent.realize_bd_iff (T := T) (cast_mk φ)] at h'
    exact h h'
  · rw [SemanticallyEquivalent.realize_bd_iff (T := T) (cast_mk ψ)]
    rw [SemanticallyEquivalent.realize_bd_iff (T := T) (cast_mk φ)] at h'
    exact h h'

@[refl]
theorem le_refl (φ : T.LindenbaumTarski α n) : φ ≤ φ := by
  induction φ using induction_on
  unfold LE.le instLE le ModelsBoundedFormula; dsimp only
  intro M v xs
  rw [BoundedFormula.realize_imp]
  exact id

theorem le_of_eq {φ ψ : T.LindenbaumTarski α n} (h : φ = ψ) : φ ≤ ψ := by
  subst h
  exact le_refl φ

theorem le_antisymm (φ ψ : T.LindenbaumTarski α n) : φ ≤ ψ → ψ ≤ φ → φ = ψ := by
  induction φ, ψ using induction_on₂
  rw [mk_le_mk_iff_models_imp, mk_le_mk_iff_models_imp, mk_eq_mk_iff_equiv]
  unfold SemanticallyEquivalent ModelsBoundedFormula
  intro h₁ h₂
  intro M v xs
  replace h₁ := h₁ M v xs
  replace h₂ := h₂ M v xs
  rw [BoundedFormula.realize_imp] at h₁ h₂
  rw [BoundedFormula.realize_iff]
  exact ⟨h₁, h₂⟩

@[trans]
theorem le_trans {φ ψ χ : T.LindenbaumTarski α n} : φ ≤ ψ → ψ ≤ χ → φ ≤ χ := by
  induction φ, ψ, χ using induction_on₃
  rw [mk_le_mk_iff_models_imp, mk_le_mk_iff_models_imp, mk_le_mk_iff_models_imp]
  unfold ModelsBoundedFormula
  intro h₁ h₂ M v xs h₃
  replace h₁ := h₁ M v xs
  replace h₂ := h₂ M v xs
  rw [BoundedFormula.realize_imp] at h₁ h₂
  exact h₂ (h₁ h₃)

instance : Trans (@le L α n T) (@le L α n T) (@le L α n T) where
  trans := le_trans

instance : PartialOrder (T.LindenbaumTarski α n) where
  le := le
  le_refl := le_refl
  le_trans φ ψ χ := le_trans
  le_antisymm := le_antisymm

theorem bot_le (φ : T.LindenbaumTarski α n) : ⊥ ≤ φ := by
  induction φ using induction_on
  unfold Bot.bot instBot bot
  dsimp only
  rw [mk_le_mk_iff_models_imp]
  unfold ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_bot]
  exact False.elim

theorem le_top (φ : T.LindenbaumTarski α n) : φ ≤ ⊤ := by
  induction φ using induction_on
  unfold Top.top instTop top
  dsimp only
  rw [mk_le_mk_iff_models_imp]
  unfold ModelsBoundedFormula
  intro M v xs
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_top, implies_true]
  exact True.intro

instance instOrderTop : OrderTop (T.LindenbaumTarski α n) where
  top := top
  le_top := LindenbaumTarski.le_top

instance instOrderBot : OrderBot (T.LindenbaumTarski α n) where
  bot := bot
  bot_le := LindenbaumTarski.bot_le

instance : BoundedOrder (T.LindenbaumTarski α n) where
  toOrderTop := instOrderTop
  toOrderBot := instOrderBot

theorem le_sup_left (φ ψ : T.LindenbaumTarski α n) : φ ≤ φ ⊔ ψ := by
  induction φ, ψ using induction_on₂
  rw [sup_mk_eq_mk_sup, mk_le_mk_iff_models_imp]
  intro M v xs
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  intro h
  left
  exact h

theorem le_sup_right (φ ψ : T.LindenbaumTarski α n) : ψ ≤ φ ⊔ ψ := by
  induction φ, ψ using induction_on₂
  rw [sup_mk_eq_mk_sup, mk_le_mk_iff_models_imp]
  intro M v xs
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  intro h
  right
  exact h

theorem sup_le (φ ψ χ : T.LindenbaumTarski α n) : φ ≤ χ → ψ ≤ χ → φ ⊔ ψ ≤ χ := by
  induction φ, ψ, χ using induction_on₃
  unfold LE.le instLE le ModelsBoundedFormula; dsimp only
  intro h₁ h₂
  intro M v xs
  replace h₁ := h₁ M v xs
  replace h₂ := h₂ M v xs
  rw [BoundedFormula.realize_imp] at h₁ h₂ ⊢
  rw [sup_mk_eq_mk_sup]
  rw [SemanticallyEquivalent.realize_bd_iff (cast_mk _),
      SemanticallyEquivalent.realize_bd_iff (cast_mk _)] at h₁ h₂ ⊢
  rw [BoundedFormula.realize_sup]
  intro h₃
  rcases h₃ with h₃ | h₃
  · exact h₁ h₃
  · exact h₂ h₃

theorem inf_le_left (φ ψ : T.LindenbaumTarski α n) : φ ⊓ ψ ≤ φ := by
  induction φ, ψ using induction_on₂
  rw [inf_mk_eq_mk_inf, mk_le_mk_iff_models_imp]
  intro M v xs
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  intro h
  exact h.1

theorem inf_le_right (φ ψ : T.LindenbaumTarski α n) : φ ⊓ ψ ≤ ψ := by
  induction φ, ψ using induction_on₂
  rw [inf_mk_eq_mk_inf, mk_le_mk_iff_models_imp]
  intro M v xs
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  intro h
  exact h.2

theorem le_inf (φ ψ χ : T.LindenbaumTarski α n) : φ ≤ ψ → φ ≤ χ → φ ≤ ψ ⊓ χ := by
  induction φ, ψ, χ using induction_on₃
  unfold LE.le instLE le ModelsBoundedFormula; dsimp only
  intro h₁ h₂
  intro M v xs
  replace h₁ := h₁ M v xs
  replace h₂ := h₂ M v xs
  rw [BoundedFormula.realize_imp, SemanticallyEquivalent.realize_bd_iff (cast_mk _),
      SemanticallyEquivalent.realize_bd_iff (cast_mk _)] at h₁ h₂
  rw [BoundedFormula.realize_imp, inf_mk_eq_mk_inf, SemanticallyEquivalent.realize_bd_iff (cast_mk _),
      SemanticallyEquivalent.realize_bd_iff (cast_mk _), BoundedFormula.realize_inf]
  intro h₃
  exact ⟨h₁ h₃, h₂ h₃⟩

instance instLattice : Lattice (T.LindenbaumTarski α n) where
  toSup := instSup
  toInf := instInf
  toPartialOrder := instPartialOrder
  le_sup_left := le_sup_left
  le_sup_right := le_sup_right
  sup_le := sup_le
  inf_le_left := inf_le_left
  inf_le_right := inf_le_right
  le_inf := le_inf

instance instDistribLattice : DistribLattice (T.LindenbaumTarski α n) where
  toLattice := instLattice
  le_sup_inf φ ψ χ := by rw [←sup_inf_left]

instance instBooleanAlgebra : BooleanAlgebra (T.LindenbaumTarski α n) where
  toHasCompl := instHasCompl
  toTop := instTop
  toBot := instBot
  toDistribLattice := instDistribLattice
  le_top := le_top
  bot_le := bot_le
  inf_compl_le_bot φ := by
    apply le_of_eq
    exact inf_not_eq_bot φ
  top_le_sup_compl φ := by
    apply le_of_eq
    symm
    exact sup_not_eq_top φ

end order

section all

def all (φ : T.LindenbaumTarski α (n + 1)) : T.LindenbaumTarski α n := by
  apply Quotient.liftOn φ (fun φ => LindenbaumTarski.mk (T := T) φ.all)
  intro φ ψ h
  rw [mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.all_congr h

scoped[FirstOrder] prefix:110 "∀ˡ" => FirstOrder.Language.Theory.LindenbaumTarski.all

theorem all_mk_eq_mk_all {φ : L.BoundedFormula α (n + 1)}
    : ∀ˡ(LindenbaumTarski.mk (T := T) φ) = LindenbaumTarski.mk φ.all := by
  simp only [LindenbaumTarski.all, mk_eq_mk_iff_equiv]
  rfl

theorem all_inf_eq_inf_all (φ ψ : T.LindenbaumTarski α (n + 1))
    : ∀ˡ(φ ⊓ ψ) = ∀ˡφ ⊓ ∀ˡψ := by
  induction φ, ψ using induction_on₂
  rw [inf_mk_eq_mk_inf, all_mk_eq_mk_all, all_mk_eq_mk_all, all_mk_eq_mk_all,
      inf_mk_eq_mk_inf, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.all_inf_equiv_inf_all

end all

section ex

def ex (φ : T.LindenbaumTarski α (n + 1)) : T.LindenbaumTarski α n := by
  apply Quotient.liftOn φ (fun φ => LindenbaumTarski.mk (T := T) φ.ex)
  intro φ ψ h
  rw [mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.ex_congr h

scoped[FirstOrder] prefix:110 "∃ˡ" => FirstOrder.Language.Theory.LindenbaumTarski.ex

theorem ex_mk_eq_mk_ex {φ : L.BoundedFormula α (n + 1)}
    : ∃ˡ(LindenbaumTarski.mk (T := T) φ) = LindenbaumTarski.mk φ.ex := by
  simp only [LindenbaumTarski.ex, mk_eq_mk_iff_equiv]
  rfl

theorem ex_sup_eq_sup_ex (φ ψ : T.LindenbaumTarski α (n + 1)) : ∃ˡ(φ ⊔ ψ) = ∃ˡφ ⊔ ∃ˡψ := by
  induction φ, ψ using induction_on₂
  rw [sup_mk_eq_mk_sup, ex_mk_eq_mk_ex, ex_mk_eq_mk_ex, ex_mk_eq_mk_ex, sup_mk_eq_mk_sup, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.ex_sup_equiv_sup_ex

theorem not_all_eq_ex_not (φ : T.LindenbaumTarski α (n + 1)) : ∼ (∀ˡφ) = ∃ˡ (∼φ) := by
  induction φ using induction_on
  rw [all_mk_eq_mk_all, not_mk_eq_mk_not, not_mk_eq_mk_not, ex_mk_eq_mk_ex, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.not_all_equiv_ex_not

theorem not_ex_eq_all_not (φ : T.LindenbaumTarski α (n + 1)) : ∼ (∃ˡφ) = ∀ˡ (∼φ) := by
  induction φ using induction_on
  rw [ex_mk_eq_mk_ex, not_mk_eq_mk_not, not_mk_eq_mk_not, all_mk_eq_mk_all, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.not_ex_equiv_all_not

@[simp]
theorem not_all_not_eq_ex (φ : T.LindenbaumTarski α (n + 1)) : ∼ (∀ˡ ∼φ) = ∃ˡφ := by
  induction φ using induction_on
  rw [not_mk_eq_mk_not, all_mk_eq_mk_all, not_mk_eq_mk_not, ex_mk_eq_mk_ex, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.not_all_not_equiv_ex

@[simp]
theorem not_ex_not_eq_all (φ : T.LindenbaumTarski α (n + 1)) : ∼ (∃ˡ ∼φ) = ∀ˡφ := by
  induction φ using induction_on
  rw [not_mk_eq_mk_not, ex_mk_eq_mk_ex, not_mk_eq_mk_not, all_mk_eq_mk_all, mk_eq_mk_iff_equiv]
  apply SemanticallyEquivalent.not_ex_not_equiv_all

end ex

section lInf

open List
variable (φ : T.LindenbaumTarski α n)
variable (l l₁ l₂ : List (T.LindenbaumTarski α n))

def lInf : T.LindenbaumTarski α n :=
  l.foldr (· ⊓ ·) ⊤

@[simp]
theorem lInf_nil : lInf ([] : List (T.LindenbaumTarski α n)) = ⊤ := by rfl

@[simp]
theorem lInf_singleton : lInf [φ] = φ := by
  rw [lInf, foldr_cons, foldr_nil, inf_top]

theorem lInf_cons : lInf (φ :: l) = φ ⊓ lInf l := by rfl

theorem lInf_append : lInf (l₁ ++ l₂) = lInf l₁ ⊓ lInf l₂ := by
  induction l₁ with
  | nil => rw [nil_append, lInf_nil, top_inf]
  | cons φ l₁ ih => rw [cons_append, lInf_cons, lInf_cons, ih, inf_assoc]

theorem lInf_mk_eq_mk_lInf (l : List (L.BoundedFormula α n))
    : lInf (l.map (@LindenbaumTarski.mk L α n T)) = @LindenbaumTarski.mk L α n T (BoundedFormula.lInf l) := by
  match l with
  | [] => rw [map_nil, lInf_nil, BoundedFormula.lInf_nil]; rfl
  | [φ] =>
    rw [map_singleton, lInf_singleton, BoundedFormula.lInf_singleton, mk_eq_mk_iff_equiv]
    symm
    apply SemanticallyEquivalent.inf_top
  | φ :: ψ :: l =>
    rw [BoundedFormula.lInf_cons_cons, map_cons, lInf_cons, ←inf_mk_eq_mk_inf]
    congr
    apply lInf_mk_eq_mk_lInf

theorem lInf_perm {l₁ l₂ : List (T.LindenbaumTarski α n)} (p : l₁ ~ l₂)
    : lInf l₁ = lInf l₂ := by
  induction p with
  | nil => rfl
  | cons φ p =>
    rw [lInf_cons, lInf_cons]
    congr 1
  | swap φ ψ l =>
    rw [lInf_cons, lInf_cons, lInf_cons, lInf_cons, ←inf_assoc, inf_comm ψ, inf_assoc]
  | trans _ _ ih₁ ih₂ =>
    rw [ih₁, ih₂]

theorem lInf_perm_map {l₁ l₂ : List ι} (p : l₁ ~ l₂) (f : ι → T.LindenbaumTarski α n)
    : lInf (l₁.map f) = lInf (l₂.map f) := by
  induction p with
  | nil => rw [map_nil]
  | cons x p ih => rw [List.map_cons, List.map_cons, lInf_cons, lInf_cons, ih]
  | swap x y l =>
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, lInf_cons, lInf_cons,
        lInf_cons, lInf_cons, ←inf_assoc, ←inf_assoc, inf_comm (f y)]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

end lInf

section lSup

open List
variable (φ : T.LindenbaumTarski α n)
variable (l l₁ l₂ : List (T.LindenbaumTarski α n))

def lSup (l : List (T.LindenbaumTarski α n)) : T.LindenbaumTarski α n :=
  l.foldr (· ⊔ ·) ⊥

@[simp]
theorem lSup_nil : lSup ([] : List (T.LindenbaumTarski α n)) = ⊥ := by rfl

@[simp]
theorem lSup_singleton : lSup [φ] = φ := by
  rw [lSup, foldr_cons, foldr_nil, sup_bot]

theorem lSup_cons : lSup (φ :: l) = φ ⊔ lSup l := by rfl

theorem lSup_append : lSup (l₁ ++ l₂) = lSup l₁ ⊔ lSup l₂ := by
  induction l₁ with
  | nil =>
    rw [nil_append, lSup_nil, bot_sup]
  | cons φ l₁ ih =>
    rw [cons_append, lSup_cons, lSup_cons, ih, sup_assoc]

theorem lSup_mk_eq_mk_lSup {l : List (L.BoundedFormula α n)}
    : lSup (l.map (@LindenbaumTarski.mk L α n T)) = @LindenbaumTarski.mk L α n T (BoundedFormula.lSup l) := by
  match l with
  | [] => rw [map_nil, lSup_nil, BoundedFormula.lSup_nil]; rfl
  | [φ] =>
    rw [map_singleton, lSup_singleton, BoundedFormula.lSup_singleton, mk_eq_mk_iff_equiv]
    symm
    apply SemanticallyEquivalent.sup_bot
  | φ :: ψ :: l =>
    rw [BoundedFormula.lSup_cons_cons, map_cons, lSup_cons, ←sup_mk_eq_mk_sup]
    congr
    apply lSup_mk_eq_mk_lSup

theorem lSup_perm {l₁ l₂ : List (T.LindenbaumTarski α n)} (p : l₁ ~ l₂)
    : lSup l₁ = lSup l₂ := by
  induction p with
  | nil => rfl
  | cons φ p =>
    rw [lSup_cons, lSup_cons]
    congr 1
  | swap φ ψ l =>
    rw [lSup_cons, lSup_cons, lSup_cons, lSup_cons, ←sup_assoc, sup_comm ψ, sup_assoc]
  | trans _ _ ih₁ ih₂ =>
    rw [ih₁, ih₂]

theorem lSup_perm_map {l₁ l₂ : List ι} (p : l₁ ~ l₂) (f : ι → T.LindenbaumTarski α n)
    : lSup (l₁.map f) = lSup (l₂.map f) := by
  induction p with
  | nil => rw [map_nil]
  | cons x p ih => rw [List.map_cons, List.map_cons, lSup_cons, lSup_cons, ih]
  | swap x y l =>
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, lSup_cons, lSup_cons,
        lSup_cons, lSup_cons, ←sup_assoc, ←sup_assoc, sup_comm (f y)]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

theorem not_lSup_eq_lInf_not : (lSup l).not = lInf (l.map (.not)) := by
  induction l with
  | nil => rw [lSup_nil, map_nil, lInf_nil]; rfl
  | cons φ l ih =>
    rw [lSup_cons, map_cons, lInf_cons, not_sup_eq_inf_not]
    apply congr_arg₂
    · rfl
    · exact ih

end lSup

section iInf

open Classical
open List Finset

variable {ι : Type*} (s s₁ s₂: Finset ι)
variable (f : ι → T.LindenbaumTarski α n)
variable (i i₁ i₂ : ι)
variable (φ ψ : T.LindenbaumTarski α n)

noncomputable def iInf := lInf (s.toList.map f)
-- noncomputable def iInf := (s.toList.map f).foldr (· ⊓ ·) ⊤

@[simp]
theorem iInf_empty : iInf ∅ f = ⊤ := by
  rw [iInf, toList_empty, map_nil, lInf_nil]

@[simp]
theorem iInf_cons {i : ι} {s : Finset ι} (hi : i ∉ s) : iInf (Finset.cons i s hi) f = f i ⊓ iInf s f := by
  let p := Finset.toList_cons hi
  rw [iInf, iInf, lInf_perm_map p, List.map_cons, lInf_cons]

theorem iInf_eq_Finset_inf : iInf s f = s.inf f := by
  induction s using cons_induction_on
  case h₁ =>
    rw [iInf_empty, Finset.inf_empty]
  case h₂ i s h ih =>
    rw [iInf_cons, Finset.inf_cons]
    apply congr_arg₂
    · rfl
    · exact ih

@[simp]
theorem inf_iInf_eq_iInf_of_mem {i : ι} {s : Finset ι} (hi : i ∈ s) : f i ⊓ iInf s f = iInf s f := by
  revert i
  induction s using Finset.cons_induction_on
  case h₁ => simp only [not_mem_empty, false_implies, implies_true]
  case h₂ j s h ih =>
    intro i hi
    simp only [cons_eq_insert, mem_insert] at hi
    rw [iInf_cons, ←inf_assoc, inf_comm (f i), inf_assoc]
    rcases hi with rfl | hi
    · rw [←inf_assoc, inf_self]
    · congr
      apply ih
      exact hi

end iInf

section iSup

open Classical
open List Finset

variable {ι : Type*} {κ : (i : ι) → Type*}
variable (s s₁ s₂: Finset ι) (t : (i : ι) → Finset (κ i))
variable (f : ι → T.LindenbaumTarski α n)
variable (g : (i : ι) → κ i → T.LindenbaumTarski α n)
variable (i i₁ i₂ : ι)
variable (φ ψ : T.LindenbaumTarski α n)

noncomputable def iSup := lSup (s.toList.map f)
-- noncomputable def iSup := (s.toList.map f).foldr (· ⊔ ·) ⊤

@[simp]
theorem iSup_empty : iSup ∅ f = ⊥ := by
  rw [iSup, toList_empty, map_nil, lSup_nil]

@[simp]
theorem iSup_cons {i : ι} {s : Finset ι} (hi : i ∉ s) : iSup (Finset.cons i s hi) f = f i ⊔ iSup s f := by
  let p := Finset.toList_cons hi
  rw [iSup, iSup, lSup_perm_map p, List.map_cons, lSup_cons]

theorem iSup_eq_Finset_sup : iSup s f = s.sup f := by
  induction s using cons_induction_on
  case h₁ =>
    rw [iSup_empty, Finset.sup_empty]
  case h₂ i s h ih =>
    rw [iSup_cons, Finset.sup_cons]
    apply congr_arg₂
    · rfl
    · exact ih

@[simp]
theorem sup_iSup_eq_iSup_of_mem {i : ι} {s : Finset ι} (hi : i ∈ s) : f i ⊔ iSup s f = iSup s f := by
  revert i
  induction s using Finset.cons_induction_on
  case h₁ => simp only [not_mem_empty, false_implies, implies_true]
  case h₂ j s h ih =>
    intro i hi
    simp only [cons_eq_insert, mem_insert] at hi
    rw [iSup_cons, ←sup_assoc, sup_comm (f i), sup_assoc]
    rcases hi with rfl | hi
    · rw [←sup_assoc, sup_self]
    · congr
      apply ih
      exact hi

theorem iInf_iSup :
    iInf s (fun i => iSup (t i) (fun j => g i j))
    = iSup (s.pi t) (fun p => iInf s.attach (fun ⟨i, hi⟩ => g i (p i hi))) := by
  simp_rw [iInf_eq_Finset_inf, iSup_eq_Finset_sup]
  apply inf_sup

theorem iSup_iInf :
    iSup s (fun i => iInf (t i) (fun j => g i j))
    = iInf (s.pi t) (fun p => iSup s.attach (fun ⟨i, hi⟩ => g i (p i hi))) := by
  simp_rw [iInf_eq_Finset_inf, iSup_eq_Finset_sup]
  apply sup_inf

theorem not_iInf_eq_iSup_not : ∼ (iInf s f) = iSup s (fun i => ∼ (f i)) := by
  simp_rw [iInf_eq_Finset_inf, iSup_eq_Finset_sup]
  sorry

end iSup

end

end LindenbaumTarski
