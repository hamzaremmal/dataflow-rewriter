/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Lean
import Batteries

import DataflowRewriter.AssocList
import DataflowRewriter.Simp
import DataflowRewriter.Basic

namespace DataflowRewriter

namespace PortMap

variable {Ident}
variable [DecidableEq Ident]

open Batteries (AssocList)

@[reducible] def cast_first {β : Type _ → Type _} {a b : (Σ α, β α)} (h : a = b) : a.fst = b.fst := by
  subst_vars; rfl

theorem rw_rule_execution {S : Type _} {a b : Σ (T : Type _), S → T → S → Prop}
{s s'} {v : a.fst} (h : a = b := by simp [drunfold]; rfl) :
  a.snd s v s' ↔ b.snd s ((cast_first h).mp v) s' := by subst_vars; rfl

theorem rule_contains {S} {a : PortMap Ident (Σ T, S → T → S → Prop)} {ident init_i v new_i}:
  (a.getIO ident).2 init_i v new_i →
  a.contains ident := by
  unfold PortMap.getIO
  intro H
  cases h : (AssocList.find? ident a)
  · have : ((AssocList.find? ident a).getD ⟨PUnit.{u_3 + 1}, fun x x x => False⟩) = ⟨PUnit.{u_3 + 1}, fun x x x => False⟩ := by
      rw [h]; rfl
    rw [rw_rule_execution this] at H; simp at H
  · rw [← AssocList.contains_find?_iff]
    exact Exists.intro _ h

theorem getIO_none {S} (m : PortMap Ident ((T : Type) × (S → T → S → Prop)))
        (ident : InternalPort Ident) :
  m.find? ident = none ->
  m.getIO ident = ⟨ PUnit, λ _ _ _ => False ⟩ := by
  intros H; simp only [PortMap.getIO, H]; simp

theorem getIO_some {S} (m : PortMap Ident ((T : Type) × (S → T → S → Prop)))
        (ident : InternalPort Ident) t :
  m.find? ident = some t ->
  m.getIO ident = t := by
  intros H; simp only [PortMap.getIO, H]; simp

theorem EqExt_getIO {S} {m m' : PortMap Ident ((T : Type) × (S → T → S → Prop))} :
  m.EqExt m' →
  ∀ i, m.getIO i = m'.getIO i := by
  unfold getIO AssocList.EqExt at *; intro hext i; rw [hext]


@[simp]
theorem cons_find? : ∀ {α} [HDEq : DecidableEq (InternalPort α)] β x v (pm: PortMap α β),
  (AssocList.find? x (AssocList.cons x v pm)) = v := by
   simpa

@[simp]
theorem getIO_cons {Ident} [DecidableEq Ident] {S}
  (pm : PortMap Ident ((T : Type) × (S → T → S → Prop))) x v:
  (PortMap.getIO (AssocList.cons x v pm) x) = v := by
    unfold PortMap.getIO; simpa

-- TODO: @[simp] ?
theorem getIO_map {S : Type _} (i : Nat) (sz : Nat) (f : Nat -> InternalPort Nat × (Σ T : Type _, (S → T → S → Prop))) k v :
  i < sz →
  f i = ⟨ k, v ⟩ →
  (PortMap.getIO
    (List.range sz |>.map (λ n => f n) |>.toAssocList)
    { inst := InstIdent.top, name := i } -- FIXME: This should be just ↑i...
    = v) := by
  intros Hlt Hf
  sorry

theorem getIO_not_contained_false {Ident} [DecidableEq Ident] {S}
  {pm : PortMap Ident ((T : Type) × (S → T → S → Prop))} {x1 x2 x3 x4}:
  ¬ pm.contains x1 → (pm.getIO x1).snd x2 x3 x4 → False := by
    intros H1 H2
    replace H1 := AssocList.contains_none H1
    replace H1 := PortMap.getIO_none _ _ H1
    rw [rw_rule_execution (h := H1)] at H2;
    dsimp at H2

theorem getIO_not_contained_false' {Ident} [DecidableEq Ident] {S}
  {pm : PortMap Ident ((T : Type) × (S → T → S → Prop))} {x1 x2 x3 x4}:
  pm.contains x1 = false → (pm.getIO x1).snd x2 x3 x4 → False := by
  intros; solve_by_elim [getIO_not_contained_false (Ident := Ident), ne_true_of_eq_false]

theorem getIO_cons_false
  {Ident} [DecidableEq Ident] {S}
  {pm : PortMap Ident ((T : Type) × (S → T → S → Prop))} {x1 v x2 x3 x4 x5}:
    ¬(x1 = x2) →
    ¬(pm.contains x2) →
    (PortMap.getIO (AssocList.cons x1 v pm) x2).snd x3 x4 x5 → False := by
  revert x2 x3 x4 x5
  generalize Hpm' : (AssocList.cons x1 v pm) = pm'
  intros x2 x3 x4 x5 H1 H2 H3
  have Hcontains : ¬ pm'.contains x2 := by
    rw [← Hpm']; simp; split_ands
    · exact H1
    · simp at H2; exact H2
  exact (getIO_not_contained_false Hcontains H3)

theorem getIO_cons_nil_false
  {Ident} [DecidableEq Ident] {S}
  x1 v x2 x3 x4 x5:
    ¬(x1 = x2) →
    (PortMap.getIO
      (AssocList.cons x1 v
        (AssocList.nil : PortMap Ident ((T : Type) × (S → T → S → Prop))))
      x2).snd x3 x4 x5 → False := by
  intros Hneq Hsnd
  apply (getIO_cons_false Hneq (by simpa) Hsnd)

end PortMap

end DataflowRewriter
