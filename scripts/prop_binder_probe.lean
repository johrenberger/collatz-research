import Lean

open Lean Elab Command Meta

/-- Whether an instance for `ty` can be obtained without extra assumptions.

An instance-implicit proposition is not automatically available. A theorem that
takes `[Fact p]` needs a proof of `p` from the caller or from another
assumption, and instance synthesis cannot conjure one, so such a binder is a
hypothesis. An instance-implicit proposition whose instance *can* be
synthesized on its own is not.
-/
private def synthesizable (ty : Expr) : MetaM Bool := do
  match ← Meta.trySynthInstance ty with
  | .some _ => pure true
  | .none => pure false
  | .undef => pure false

-- PROBE-RULE
/-- Count the Prop-valued binders of each probed constant.

The source text cannot answer this reliably: a Lean hypothesis is usually
written as a binder (theorem t (h : P) : Q), not as an arrow in the type.
Only the elaborated environment knows that P is a proposition, so the
manifest's conditional/unconditional classification is taken from here.

Each row is
PROP|<name>|<propBinders>|<instanceImplicitPropBinders>|<unsynthesizedInstancePropBinders>
where the last number counts the instance-implicit proposition binders whose
instance cannot be synthesized without extra assumptions.
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
      let mut unsynthesized := 0
      for i in [:fvars.size] do
        let ft ← Meta.inferType fvars[i]!
        if ← Meta.isProp ft then
          propBinders := propBinders + 1
          match bis[i]! with
          | BinderInfo.instImplicit =>
            instPropBinders := instPropBinders + 1
            if ← synthesizable ft then
              pure ()
            else
              unsynthesized := unsynthesized + 1
          | _ => pure ()
      rows := rows.push s!"PROP|{target}|{propBinders}|{instPropBinders}|{unsynthesized}"
    pure rows.toList) {} {}
  for row in rows do
    logInfo row
