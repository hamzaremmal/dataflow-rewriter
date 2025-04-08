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
import DataflowRewriter.ExprHighLemmas
import DataflowRewriter.Component
import DataflowRewriter.KernelRefl
import DataflowRewriter.Reduce
import DataflowRewriter.List
import DataflowRewriter.Tactic
import DataflowRewriter.AssocList
import DataflowRewriter.Examples.NoC.Basic
import DataflowRewriter.Examples.NoC.Components

open Batteries (AssocList)

namespace DataflowRewriter.NoC

variable [T: NocParam]

-- Implementation --------------------------------------------------------------

-- Bag with `n` inputs
def nbag (T : Type) (TS : String) (n : ℕ) : ExprHigh String :=
  {
    modules := [
      ⟨"Merge", -- Instance name
        ⟨
          {
            input :=
              List.range n |>.map (λ i =>
                ⟨
                  -- Type port (Must be inst InstIdent.top)
                  NatModule.stringify_input i,
                  -- Internal name, here a top level port
                  NatModule.stringify_input i,
                ⟩
              )
              |>.toAssocList,
            output := [⟨
                NatModule.stringify_output 0,
                -- Internal name
                {
                  -- Same Instance Name as above
                  inst := InstIdent.internal "Merge",
                  -- Arbitrary name
                  name := "merge_to_bag_out",
                }
              ⟩].toAssocList,
          },
          s!"Merge {TS} {n}" -- Instance Type
        ⟩
      ⟩,

      ⟨"Bag", -- Instance name
        ⟨
          {
            input := [
              ⟨
                NatModule.stringify_input 0,
                { inst := InstIdent.internal "Bag", name := "merge_to_bag_in" }
              ⟩
            ].toAssocList,
            output := [
              ⟨NatModule.stringify_output 0, NatModule.stringify_output 0⟩
            ].toAssocList,
          },
          s!"Bag {TS}" -- Instance Type
        ⟩
      ⟩,

    ].toAssocList,
    connections := [
      {
        output := { inst := InstIdent.internal "Merge", name := "merge_to_bag_out" },
        input := { inst := InstIdent.internal "Bag", name := "merge_to_bag_in" },
      }
    ],
  }

def nbagT :=
  [GT| nbag T.Data T.DataS T.netsz, ε']

def nbagM :=
  [Ge| nbag T.Data T.DataS T.netsz, ε']

attribute [drcompute] Batteries.AssocList.toList Function.uncurry Module.mapIdent List.toAssocList List.foldl Option.pure_def Option.bind_eq_bind Option.bind_some Module.renamePorts Batteries.AssocList.mapKey InternalPort.map toString Nat.repr Nat.toDigits Nat.toDigitsCore Nat.digitChar List.asString Option.bind Batteries.AssocList.mapVal Batteries.AssocList.eraseAll Batteries.AssocList.eraseP beq_self_eq_true Option.getD cond beq_self_eq_true  beq_iff_eq  InternalPort.mk.injEq  String.reduceEq  and_false  imp_self BEq.beq AssocList.bijectivePortRenaming AssocList.keysList AssocList.eraseAllP List.inter AssocList.filterId AssocList.append AssocList.filter

attribute [drdecide] InternalPort.mk.injEq and_false decide_False decide_True and_true Batteries.AssocList.eraseAllP  InternalPort.mk.injEq
  and_false  decide_False  decide_True  reduceCtorEq  cond  List.map List.elem_eq_mem List.mem_cons List.mem_singleton Bool.decide_or InternalPort.mk.injEq
  String.reduceEq and_false decide_false reduceCtorEq and_self Bool.or_self Bool.false_eq_true not_false_eq_true
  List.filter_cons_of_neg and_true List.filter_nil List.empty_eq decide_true List.nodup_cons List.not_mem_nil
  List.nodup_nil Bool.and_self reduceIte List.concat_eq_append dreduceIte List.append_nil

def nbagT_precompute : Type := by
  precomputeTac nbagT by
    unfold nbagT
    simp [drunfold,seval,drdecide,-AssocList.find?_eq]
    rw [ε'_merge,ε'_bag]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]

-- This should be spit out automatically
axiom nbagT_eq : nbagT = nbagT_precompute

def nbagM_precompute : StringModule nbagT_precompute := by
  precomputeTac [Ge| nbag T.Data T.DataS T.netsz, ε'] by
    simp [drunfold,seval,drdecide,-AssocList.find?_eq]
    rw [ε'_merge,ε'_bag]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq]
    rw [AssocList.find?_gss]
    conv =>
      pattern (occs := *) Module.connect'' _ _
      all_goals
        rw [(Module.connect''_dep_rw (h := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl)
                                     (h' := by simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?]; rfl))]; rfl
    -- simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,-Prod.exists]
    simp [drunfold,seval,drcompute,drdecide,-AssocList.find?_eq,Batteries.AssocList.find?,AssocList.filter,-Prod.exists]
    unfold Module.connect''
    dsimp

def ε : Env :=
  AssocList.cons
    s!"NBag {T.DataS} {T.netsz}" ⟨_, nbagM⟩ ε'

def noc : ExprHigh String :=
  {
    modules :=
      List.range T.netsz |>.map (λ i => [
        ⟨s!"Split{i}",
          ⟨
            {
              input := [
                ⟨NatModule.stringify_input 0, NatModule.stringify_input i⟩
              ].toAssocList,
              output := [
                ⟨
                  NatModule.stringify_output 0,
                  {
                    inst := InstIdent.internal s!"Split{i}",
                    name := s!"Data{i}_out"
                  }
                ⟩,
                ⟨
                  NatModule.stringify_output 1,
                  {
                    inst := InstIdent.internal s!"Split{i}",
                    name := s!"FlitHeader{i}_out"
                  }
                ⟩,
              ].toAssocList,
            },
            s!"Split {T.DataS} {FlitHeaderS}"
          ⟩
        ⟩,

        ⟨s!"NBranch{i}",
          ⟨
            {
              input := [
                ⟨
                  NatModule.stringify_input 0,
                  {
                    inst := InstIdent.internal s!"NBranch{i}",
                    name := s!"NBranch{i}_in1"
                  }
                ⟩,
                ⟨
                  NatModule.stringify_input 1,
                  {
                    inst := InstIdent.internal s!"NBranch{i}",
                    name := s!"NBranch{i}_in2"
                  }
                ⟩,
              ].toAssocList,
              output := List.range T.netsz |>.map (λ j =>
                ⟨
                  NatModule.stringify_output j,
                  {
                    inst := InstIdent.internal s!"NBranch{i}",
                    name := s!"NBranch{i}_out{j + 1}"
                  }
                ⟩
              ) |>.toAssocList
            },
            s!"NBranch {T.DataS} {T.netsz}"
          ⟩
        ⟩,

        ⟨s!"NBag{i}",
          ⟨
            {
              input := List.range T.netsz |>.map (λ j =>
                ⟨
                  NatModule.stringify_input j,
                  {
                    inst := InstIdent.internal s!"NBag{i}",
                    name := s!"NBag{i}_in{j + 1}"
                  }
                ⟩
              ) |>.toAssocList,
              output := [
                ⟨
                  NatModule.stringify_output 0,
                  NatModule.stringify_output i,
                ⟩,
              ].toAssocList,
            },
            s!"NBag {T.DataS} {T.netsz}"
          ⟩
        ⟩,
      ])
      |>.flatten
      |>.toAssocList,
    connections :=
      List.range T.netsz |>.map (λ i => ([
        {
          output :=
            {
              inst := InstIdent.internal s!"Split{i}",
              name := s!"Data{i}_out"
            }
          input :=
            {
              inst := InstIdent.internal s!"NBranch{i}",
              name := s!"Data{i}_in0"
            }
        },
        {
          output :=
            {
              inst := InstIdent.internal s!"Split{i}",
              name := s!"FlitHeader{i}_out"
            }
          input :=
            {
              inst := InstIdent.internal s!"NBranch{i}",
              name := s!"Data{i}_in1"
            }
        },
      ])
      ++
      (List.range T.netsz |>.map (λ j =>
        {
          output :=
            {
              inst := InstIdent.internal s!"NBranch{i}",
              name := s!"NBranch{i}_out{j + 1}"
            }
          input :=
            {
              inst := InstIdent.internal s!"NBag{i}",
              name := s!"NBag{i}_in{j + 1}"
            }
        }
      )))
      |>.flatten
  }

def nocM :=
  [Ge| noc, ε]

def nocT :=
  [GT| noc, ε]

def nocM_precompute :=

-- TODO: We could prove that any RouterID has an associated input rule which is
-- unique
-- TODO: We could do the same with output rules

theorem nocM_inpT i:
  (nocM.inputs.getIO (NatModule.stringify_input i)).1 = (T.Data × FlitHeader) :=
  by
    sorry

theorem nocM_outT i:
  (nocM.outputs.getIO (NatModule.stringify_output i)).1 = (T.Data × FlitHeader) :=
    by
      sorry

-- TODO: Say that v must be ⟨j, d⟩, and so should v'
-- We prove that for every input and output, we can route a message between them
theorem full_connectivity (i j : RouterID) (d : T.Data) in_s mid_s:
  -- From any initial state `in_s`, we can reach a new state `mid_s` by using
  -- the input rule associated to `i` used with value `v`
  (nocM.inputs.getIO (NatModule.stringify_input i)).2 in_s ((nocM_inpT i).mpr (d, ⟨j⟩)) mid_s →
  ∃ out_s,
  -- There exists a path from this `mid_s` to an output state `out_s`
  existSR nocM.internals mid_s out_s ∧
  -- This `out_s` can be used to actually extract the initial value `v` in the
  (nocM.outputs.getIO (NatModule.stringify_output j)).2 mid_s ((nocM_outT j).mpr (d, ⟨j⟩)) out_s
  := by sorry

end DataflowRewriter.NoC
