/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import Lean
import Init.Data.BitVec.Lemmas
import Qq

import DataflowRewriter.Simp
import DataflowRewriter.Module
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.Tactic
import DataflowRewriter.AssocList

import DataflowRewriter.Examples.NoC.Basic
import DataflowRewriter.Examples.NoC.BasicLemmas
import DataflowRewriter.Examples.NoC.Components

open Batteries (AssocList)

namespace DataflowRewriter.Examples.NoC

variable [P : NocParam]

-- Implementation --------------------------------------------------------------

def ε_nroute : Env :=
  [
    (s!"Split {P.DataS} {FlitHeaderS}", ⟨_, StringModule.split P.Data FlitHeader⟩),
    (s!"NBranch {P.DataS} {P.netsz}", ⟨_, nbranch⟩),
  ].toAssocList

theorem ε_nroute_split :
  ε_nroute.find? s!"Split {P.DataS} {FlitHeaderS}" = .some ⟨_, StringModule.split P.Data FlitHeader⟩ := by
    sorry

theorem ε_nroute_nbranch :
  ε_nroute.find? s!"NBranch {P.DataS} {P.netsz}" = .some ⟨_, nbranch⟩ := by
    sorry

def nroute_low : ExprLow String :=
  let split := ExprLow.base
    {
      input := [
        ⟨NatModule.stringify_input 0, NatModule.stringify_input 0⟩
      ].toAssocList,
      output := [
        ⟨
          NatModule.stringify_output 0,
          { inst := InstIdent.internal "Split", name := NatModule.stringify_output 0 }
        ⟩,
        ⟨
          NatModule.stringify_output 1,
          { inst := InstIdent.internal "Split", name := NatModule.stringify_output 1 }
        ⟩
      ].toAssocList,
    }
    s!"Split {P.DataS} {FlitHeaderS}"
  let nbranch := ExprLow.base
    {
      input := [
        ⟨
          NatModule.stringify_input 0,
          { inst := InstIdent.internal "NBranch", name := NatModule.stringify_input 0 }
        ⟩,
        ⟨
          NatModule.stringify_input 1,
          { inst := InstIdent.internal "NBranch", name := NatModule.stringify_input 1 }
        ⟩,
      ].toAssocList,
      output := List.range P.netsz |>.map (λ i => ⟨
        NatModule.stringify_output i,
        NatModule.stringify_output i,
      ⟩) |>.toAssocList,
    }
    s!"NBranch {P.DataS} {P.netsz}"
  let connection (i : Nat) : Connection String :=
    {
      output := {
        inst := InstIdent.internal "Split",
        name := NatModule.stringify_output i
      },
      input := {
        inst := InstIdent.internal "NBranch",
        name := NatModule.stringify_input i
      },
    }
  ExprLow.product nbranch split
  |> ExprLow.connect (connection 0)
  |> ExprLow.connect (connection 1)

def nroute_lowT : Type := by
  precomputeTac [T| nroute_low, ε_nroute] by
    simp [drunfold, seval, drdecide, -AssocList.find?_eq]
    rw [ε_nroute_split, ε_nroute_nbranch]
    simp [drunfold, seval, drcompute, drdecide]

def nroute_lowM : StringModule nroute_lowT := by
  precomputeTac [e| nroute_low, ε_nroute] by
    simp [drunfold, seval, drdecide, -AssocList.find?_eq]
    rw [ε_nroute_split, ε_nroute_nbranch]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl)
                                     (h' := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl))]; rfl
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?,AssocList.filter,-Prod.exists]
    unfold Module.connect''
    dsimp
    simp? [
      Module.liftR,
      Module.liftL,
      AssocList.mapVal_map_toAssocList,
      AssocList.mapKey_map_toAssocList,
      AssocList.mapKey_mapKey,
      AssocList.mapVal_mapKey,
      AssocList.eraseAll_append,
      AssocList.eraseAll_map_neq,
      AssocList.eraseAll_nil,
      AssocList.append_nil,
      AssocList.find?_append,
      AssocList.find?_map_neq,
      AssocList.bijectivePortRenaming_same,
      -AssocList.find?_eq,
      InternalPort.map,
      stringify_output_neq,
      stringify_input_neq,
      internalport_neq
    ]
    -- TODO: Find a way to make this portable
    -- We are trying to write under existentials and dependent types
    conv =>
      pattern (occs := *) And _ _
      all_goals congr
      any_goals
        rw [PortMap.rw_rule_execution
          (h := by simp [
            Module.liftR,
            Module.liftL,
            AssocList.mapVal_map_toAssocList,
            AssocList.mapKey_map_toAssocList,
            AssocList.mapKey_mapKey,
            AssocList.mapVal_mapKey,
            AssocList.eraseAll_append,
            AssocList.eraseAll_map_neq,
            AssocList.eraseAll_nil,
            AssocList.append_nil,
            AssocList.find?_append,
            AssocList.find?_map_neq,
            AssocList.bijectivePortRenaming_same,
            -AssocList.find?_eq,
            InternalPort.map,
            stringify_output_neq,
            stringify_input_neq,
            internalport_neq,
          ]
          <;> rfl)
        ]
        dsimp
      all_goals rfl
    skip

-- Correctness -----------------------------------------------------------------

instance : MatchInterface nroute_lowM nroute where
  input_types := by
    intros ident
    unfold nroute_lowM nroute nroute'
    by_cases H: (NatModule.stringify_input 0 : InternalPort String) = ident
    <;> simp [*, drunfold, drnat, PortMap.getIO_cons, NatModule.stringify_input, InternalPort.map] at *
    <;> simpa [*]
  output_types := by
    intros ident
    unfold nroute_lowM nroute nroute' lift_f mk_nroute_output_rule
    simp [NatModule.stringify, Module.mapIdent, InternalPort.map, NatModule.stringify_output] at *
    simp [AssocList.mapKey_map_toAssocList, InternalPort.map]
    apply (getIO_map_ident_match_1 (Heq := by simpa))
  inputs_present := by
    intros ident
    unfold nroute_lowM nroute nroute'
    by_cases H: (NatModule.stringify_input 0 : InternalPort String) = ident
    <;> simp [*, drunfold, drnat, PortMap.getIO_cons, NatModule.stringify_input, InternalPort.map] at *
    <;> simpa [*]
  outputs_present := by
    intros ident
    unfold nroute_lowM nroute nroute'
    simp [NatModule.stringify, Module.mapIdent]
    apply isSome_same_list
    constructor <;> intros H <;> obtain ⟨x, _, _⟩ := H <;> exists x <;> simpa

def φ (I : nroute_lowT) (S : nrouteT) : Prop :=
  (I.1.1 ++ I.2.1).length = (I.1.2 ++ I.2.2).length ∧
  S = List.zip (I.1.1 ++ I.2.1) (I.1.2 ++ I.2.2)

theorem zip_concat {α β} {l1 : List α} {l2 : List β} {v}
  (Hlen : List.length l1 = List.length l2) :
  (l1.zip l2) ++ [v] = (l1 ++ [v.1]).zip (l2 ++ [v.2]) := by
  revert Hlen
  induction l1 generalizing l2 <;> induction l2 <;> intros Hlen
  · simpa [List.zip]
  · contradiction
  · contradiction
  · rename_i _ _ HR1 _ _ _
    repeat rw [List.length_cons] at Hlen
    rw [add_left_inj] at Hlen
    specialize (HR1 Hlen)
    simpa [List.zip]

theorem nroute_low_refines_initial :
  Module.refines_initial nroute_lowM nroute φ := by
    unfold nroute_lowM nroute nroute'
    dsimp [Module.refines_initial, NatModule.stringify, Module.mapIdent]
    intros i Hi
    obtain ⟨Hi1, Hi2⟩ := Hi
    unfold φ
    rw [Hi1, Hi2]
    exists []

theorem nroute_low_refines_φ : nroute_lowM ⊑_{φ} nroute := by
  intros i s H
  obtain ⟨H1, H2⟩ := H
  constructor
  <;> unfold nroute nroute' nroute_lowM
  <;> intros ident mid_i v Hrule
  <;> dsimp [
    NatModule.stringify, Module.mapIdent,
    InternalPort.map, lift_f, mk_nroute_output_rule
  ] at v Hrule ⊢
  · case_transition Hcontains : (Module.inputs nroute_lowM), ident,
     (fun x => PortMap.getIO_not_contained_false' x Hrule)
    simp at Hcontains
    subst ident
    unfold PortMap.getIO at v Hrule ⊢
    exists s.concat v
    exists s.concat v
    rw [PortMap.rw_rule_execution
      (h := by rw [AssocList.find?_cons_eq] <;> rfl)
    ] at Hrule ⊢
    rw [AssocList.find?_cons_eq] at v
    dsimp at Hrule v ⊢
    obtain ⟨⟨Hrule1, Hrule2⟩, Hrule3⟩ := Hrule
    split_ands
    · rfl
    · constructor
    · rw [List.length_append] at H1
      simpa [Hrule1, Hrule2, ←Hrule3, ←add_assoc, H1]
    · simpa [H2, Hrule1, Hrule2, ←Hrule3, zip_concat (Hlen := H1)]
  · case_transition Hcontains : (Module.outputs nroute_lowM), ident,
     (fun x => PortMap.getIO_not_contained_false' x Hrule)
    simp [nroute_lowM] at Hcontains
    obtain ⟨n, HnFin, Hident⟩ := Hcontains
    subst ident
    unfold φ
    exists List.zip (mid_i.1.1 ++ mid_i.2.1) (mid_i.1.2 ++ mid_i.2.2)
    rw [PortMap.rw_rule_execution
      (h := by rw [AssocList.mapKey_map_toAssocList])
    ]
    rw [PortMap.rw_rule_execution
      (h := by apply (getIO_map_stringify_output) <;> rfl)
    ] at Hrule ⊢
    rw [getIO_map_stringify_output] at v
    dsimp at v Hrule ⊢
    unfold lift_f mk_nroute_output_rule
    dsimp at v Hrule ⊢
    obtain ⟨⟨Hrule1, Hrule2⟩, Hrule3⟩ := Hrule
    split_ands
    · simpa [H2, ←Hrule1, ←Hrule2, ←Hrule3, List.zip]
    · rw [←Hrule1, ←Hrule2, Hrule3] at H1
      dsimp at H1
      simp only [add_left_inj] at H1
      assumption
    · rfl
  · exists s; constructor -- FIXME: Names are wrong (Hrule, v...)
    · constructor
    · simp at v
      cases v
      · rename_i H; simp at H;
        subst ident
        obtain ⟨
          a, b, a', b', output,
          ⟨⟨Hrule1, Hrule2⟩, Hrule3⟩,
          ⟨Hrule4, Hrule5⟩,
          Hrule6
        ⟩ := Hrule
        unfold φ
        subst a a' s
        split_ands
        · rw [Hrule1, Hrule3] at H1
          dsimp at H1
          simpa [←Hrule6, Hrule5, H1]
        · simpa [Hrule1, Hrule3, Hrule5, ←Hrule6]
      · rename_i H; simp at H;
        subst ident
        obtain ⟨
          a, b, a', b', output,
          ⟨⟨Hrule1, Hrule2⟩, Hrule3⟩,
          ⟨Hrule4, Hrule5⟩,
          Hrule6
        ⟩ := Hrule
        unfold φ
        subst b b' s
        split_ands
        · rw [Hrule3] at H1; dsimp at H1
          simpa [←Hrule6, ←H1, Hrule1, Hrule4]
        · simpa [Hrule1, Hrule4, Hrule3, ←Hrule6]

theorem nroute_low_ϕ_indistinguishable :
  ∀ x y, φ x y → Module.indistinguishable nroute_lowM nroute x y := by
    intros x y Hφ
    constructor
    <;> intros ident new_i v Hrule
    <;> unfold nroute nroute' nroute_lowM at *
    <;> dsimp at v Hrule
    <;> dsimp [NatModule.stringify, Module.mapIdent]
    <;> obtain ⟨H1, H2⟩ := Hφ
    · case_transition Hcontains : (Module.inputs nroute_lowM), ident,
        (fun x => PortMap.getIO_not_contained_false' x Hrule)
      simp at Hcontains
      subst ident
      exists y.concat v
    · have ⟨n, Hn1, Hn2⟩ := getIO_map_ident Hrule
      subst ident
      exists List.zip (new_i.1.1 ++ x.2.1) (new_i.1.2 ++ x.2.2)
      rw [getIO_map_stringify_output] at v
      rw [PortMap.rw_rule_execution (h := by rw [AssocList.mapKey_map_toAssocList])]
      rw [PortMap.rw_rule_execution
        (h := by apply (getIO_map_stringify_output) <;> rfl)
      ] at Hrule ⊢
      unfold lift_f mk_nroute_output_rule
      dsimp at Hrule v ⊢
      obtain ⟨⟨Hrule1, Hrule2⟩, Hrule2⟩ := Hrule
      simpa [H2, ←Hrule2, ←Hrule1]

theorem nroute_low_correct : nroute_lowM ⊑ nroute := by
  apply (
    Module.refines_φ_refines
      nroute_low_ϕ_indistinguishable
      nroute_low_refines_initial
      nroute_low_refines_φ
  )

end DataflowRewriter.Examples.NoC
