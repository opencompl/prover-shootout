/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat

This file implements Ackermannization [1, 2]

[1] https://lara.epfl.ch/w/_media/model-based.pdf
[2]  https://leodemoura.github.io/files/oregon08.pdf
-/
import Lean
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Rewrites
import Lean.Elab.Tactic.Conv
import Lean.Elab.Tactic.Conv.Basic
import Std

open Lean Meta Elab Tactic

/-- Provides tracing for the `ack` tactic. -/
initialize Lean.registerTraceClass `ack

namespace Ack


structure Config where

structure Context where
 config : Config

structure Call where
  name : Name
  x : Expr -- the fvarId for x
  xTy : Expr -- type of domain of f.
  fx : FVarId -- the fvarId for fx
  fxTy : Expr -- type of codomain of f.
  heqProof : Expr -- heqProof : x = f x
deriving Hashable, BEq, Inhabited

instance : ToMessageData Call where
  toMessageData c := m!"{Expr.fvar c.fx} : {c.fxTy} = f ({c.x} : {c.xTy}) with proof {c.heqProof}"

structure State where
  /-- mapping from a function `f` to all arguments `(x, fx)`. -/
  fn2apps : HashMap Expr (Std.HashSet Call) := {}
  gensymCounter : Nat := 0


def State.init (_cfg : Config) : State where

abbrev AckM := StateRefT State (ReaderT Context TacticM)

def run (m : AckM α) (ctx : Context) : TacticM α :=
  m.run' (State.init ctx.config) |>.run ctx

def gensym : AckM Name := do
  modify fun s => { s with gensymCounter := s.gensymCounter + 1 }
  return Name.mkNum `ack (← get).gensymCounter

def withMainContext (ma : AckM α) : AckM α := do
  (← getMainGoal).withContext ma

def withContext (g : MVarId) (ma : AckM α) : AckM α := do
  g.withContext ma

def getCalls (fn : Expr) : AckM (Std.HashSet Call) := do
  return (← get).fn2apps.findD fn {}

def hasCall (fn : Expr) (call : Call) : AckM Bool := do
  let calls ← getCalls fn
  return calls.contains call

def addCall (fn : Expr) (call : Call) : AckM Unit := do
  let calls ← getCalls fn
  modify fun s => { s with fn2apps := s.fn2apps.insert fn (calls.insert call) }

/-- create a trace node in trace class (i.e. `set_option traceClass true`),
with header `header`, whose default collapsed state is `collapsed`. -/
def withTraceNode (header : MessageData) (k : AckM α)
    (collapsed : Bool := true)
    (traceClass : Name := `ack) : AckM α :=
  Lean.withTraceNode traceClass (fun _ => return header) k (collapsed := collapsed)

def processingEmoji : String := "⚙️"

/-- Create a trace note that folds `header` with `(NOTE: can be large)`,
and prints `msg` under such a trace node.
-/
def traceLargeMsg (header : MessageData) (msg : MessageData) : AckM Unit :=
    withTraceNode m!"{header} (NOTE: can be large)" do
      trace[ack] msg


-- The proof of correctness of the Ackermannization transform.
theorem ackermannize_proof (A : Type _) (B : Type _)
    (f : A → B)
    (x y : A)
    (fx fy : B)
    (hfx : f x = fx) -- In the same order that `generalize h : f x = fx` would produce.
    (hfy : f y = fy) :
    x = y → fx = fy := by
  intros h
  subst h
  simp [← hfx, ← hfy]

def isBitblastTy (e : Expr) : Bool :=
  match_expr e with
  | BitVec _ => true
  | Bool => true
  | _ => false

/-
Introduce a new definition into the local context,
and return the FVarId of the new definition in the goal.
-/
def introDef (name : Name) (hdefVal : Expr) : AckM FVarId  := do
  withMainContext do
    let goal ← getMainGoal
    let hdefTy ← inferType hdefVal

    let goal ← goal.assert name hdefTy hdefVal
    let (fvar, goal) ← goal.intro1P
    replaceMainGoal [goal]
    return fvar

def doAck (eorig : Expr) : AckM Unit := do
  withMainContext do
  traceLargeMsg m!"🔝 TOPLEVEL '{eorig}'" m!"{toString eorig}"
  match eorig with
  | .mdata _ e => doAck e
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .proj .. | .lit .. => return ()
  | .app f args => do
      withTraceNode m!"processing '{eorig}'..." do
        doAck f
        doAck args
        withMainContext do
          let e := Expr.app f args
          let args := e.getAppArgs

          let ety ← inferType e
          if ! isBitblastTy ety then
            trace[ack] "{crossEmoji} '{eorig}' : '{ety}' not bitblastable.."
            return ()
          trace[ack] "{checkEmoji} found bitblastable call ('{f}' '{args}') : '{ety}'."

          let newName : Name ← gensym
          -- TODO: build the larger application...
          if h : args.size ≠  1 then
            trace[ack] "{crossEmoji} Expected fn app ('{f}' '{args}'). to have exactly one argument. Skipping..."
            return ()
          else
            let arg := args[0]
            -- let fxName : Name := name.appendAfter s!"App"
            -- let fx ← introDef fxName e -- this changes the main context.
            -- Implementation modeled after `Lean.MVarId.generalizeHyp`.
            let transparency := TransparencyMode.reducible
            let hyps := (← getLCtx).getFVarIds
            let hyps ← hyps.filterM fun h => do
              let type ← instantiateMVars (← h.getType)
              return (← withTransparency transparency <| kabstract type e).hasLooseBVars

            let goal ← getMainGoal
            let (reverted, goal) ← goal.revert hyps true
            let garg : GeneralizeArg := {
              expr := e,
              xName? := .some newName,
              hName? := newName.appendAfter "h"
            }
            let (fxs, goal) ← goal.generalize #[garg]
            let (reintros, goal) ← goal.introNP reverted.size
            replaceMainGoal [goal]

            withMainContext do
              let mut i := 0
              for r in reintros do
                trace[ack] "REINTROS[{i}]: {← r.getUserName} : {← r.getType}"
                i := i + 1

            withMainContext do
              let mut i := 0
              for r in fxs do
                trace[ack] "FXS[{i}]: {← r.getUserName} : {← r.getType}"
                i := i + 1

            let .some fx := fxs[0]?
              | throwTacticEx `ack goal m!"expected generalized variable"
            let .some f_x_eq_fx := fxs[1]?
              | throwTacticEx `ack goal m!"expected proof of generalized variable"

            withMainContext do
              trace[ack] "{processingEmoji} introduced new defn {Expr.fvar fx} := {e}."

              let calls ← getCalls f
              let call : Call := {
                name := newName
                x := arg,
                xTy := ← inferType arg,
                fx := fx,
                fxTy := ← fx.getType,
                heqProof := Expr.fvar f_x_eq_fx
              }

              trace[ack] "built ackermannization: {call} • {Expr.fvar fx}"

              for otherCall in calls do
                trace[ack] "building interference: {call.x} = {otherCall.x} => {call.fx.name} = {otherCall.fx.name}"
                let eqName := (otherCall.name).appendAfter s!"Sim" |>.append call.name
                let ackEq ← mkAppM ``Ack.ackermannize_proof
                  #[call.xTy, ety, -- A B
                    f, -- f
                    call.x, otherCall.x, -- x y
                    .fvar call.fx, .fvar otherCall.fx, -- fx fy
                    call.heqProof, otherCall.heqProof -- hfx hfy
                  ]
                let _ ← introDef eqName ackEq
                -- make a call of ackermannize_proof.
              addCall f call
            -- the application is now this fvar.
  | .lam .. | .letE .. => return ()
  | .forallE .. => return ()


-- For every bitvector (x : BitVec w),
-- for every function `(f : BitVec w → BitVec w')`
-- walk every function application (f x), and add a new fvar (fx : BitVec w').
-- Keep an equality that says `fx = f x`.
-- For function application of f, for each pair of bitvectors x, y, add a
-- hypothesis that says `x = y => fx = fy, with proof`
-- add a hyp that says that `fx =
def ack : AckM Unit := do
  withMainContext do
    for hyp in (← getLocalHyps) do
      doAck (← inferType hyp)
    doAck (← getMainTarget)



/--
Given a collection of facts, try prove `False` using the omega algorithm,
and close the goal using that.
-/
def ackTac (ctx : Context) : TacticM Unit := do
  -- evalTactic (← `(simp (config := {failIfUnchanged := false}) only [memory_rules]))
  run ack ctx


end Ack

/--
Allow elaboration of `Acker` arguments to tactics.
-/
declare_config_elab AckConfig Ack.Config

/--
Implement the ackermannize tactic frontend.
-/
syntax (name := ackermannize) "ack" (Lean.Parser.Tactic.config)? : tactic

@[tactic ackermannize]
def evalAckermannize : Tactic := fun
  | `(tactic| ack $[$cfg]? ) => do
    let config ← AckConfig (mkOptionalNode cfg)
    Ack.ackTac { config := config }
  | _ => throwUnsupportedSyntax
