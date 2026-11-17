import CollatzResearch
import Lean

open Lean Elab Command Meta

/-- Count the Prop-valued binders of each probed constant.

The source text cannot answer this reliably: a Lean hypothesis is usually
written as a binder (theorem t (h : P) : Q), not as an arrow in the type.
Only the elaborated environment knows that P is a proposition, so the
manifest's conditional/unconditional classification is taken from here.

Each row is PROP|<name>|<propBinders>|<instanceImplicitPropBinders>.
An instance-implicit Prop is resolved automatically and is therefore not a
hypothesis, so the manifest subtracts it before classifying.
-/
elab "#probePropBinders" : command => do
  let env ← liftCoreM (Lean.getEnv)
  let rows ← liftCoreM <| MetaM.run' (do
    let mut rows : Array String := #[]
    for target in probeTargets do
      let some (_, ci) :=
        env.constants.toList.find? (fun (n, _) => n.toString == target) | continue
      let (fvars, bis, _body) ← Meta.forallMetaTelescopeReducing ci.type
      let mut propBinders := 0
      let mut instPropBinders := 0
      for i in [:fvars.size] do
        let ft ← Meta.inferType fvars[i]!
        if ← Meta.isProp ft then
          propBinders := propBinders + 1
          match bis[i]! with
          | BinderInfo.instImplicit => instPropBinders := instPropBinders + 1
          | _ => pure ()
      rows := rows.push s!"PROP|{target}|{propBinders}|{instPropBinders}"
    pure rows.toList) {} {}
  for row in rows do
    logInfo row
