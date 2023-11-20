/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Daniel Selsam, Mario Carneiro
-/
import Std.Lean.Util.EnvSearch
import Lean.Elab.Tactic.Config

namespace Lean.Elab.Command

/--
Options to control `getMatchingConstants` options below.
-/
structure PrintPrefixConfig where
  /-- Include declarations in imported environment. -/
  imported : Bool := true
  /-- Include declarations who types are propositions. -/
  propositions : Bool := true
  /-- Exclude definitions who types are not propositions. -/
  propositionsOnly : Bool := false
  /-- Flag to control whether we should print the type of a declartion. -/
  showTypes : Bool := true
  /--
  Set to true to include internal declarations (names with "_" or ending with match_ or proof_)
  -/
  internals : Bool := false

/-- Function elaborating `Config`. -/
declare_config_elab elabPrintPrefixConfig PrintPrefixConfig

/--
Command for #print prefix
-/
syntax (name := printPrefix) "#print prefix " (Lean.Parser.Tactic.config)? ident : command

/--
Returns true if any part of name starts with underscore or uses a num.

This can be used to hide internally generated names.
-/
def isInternalDetail : Name → Bool
  | .str p s     =>
    s.startsWith "_"
      || s.startsWith "match_"
      || s.startsWith "proof_"
      || p.isInternal
  | .num p _     => p.isInternal
  | _            => false

/--
`reverseName name` reverses the components of a name.
-/
private def reverseName : Name → (pre:Name := .anonymous) → Name
| .anonymous, p => p
| .str q s, p => reverseName q (.str p s)
| .num q n, p => reverseName q (.num p n)

/--
`takeNameSuffix n name` returns a pair `(pre, suf)` where `suf` contains the last `n` components
of the name and `pre` contains the rest.
-/
private def takeNameSuffix (cnt : Nat) (name : Name) (pre : Name := .anonymous) : Name × Name :=
  match cnt, name with
  | .succ cnt, .str q s => takeNameSuffix cnt q (.str pre s)
  | .succ cnt, .num q n => takeNameSuffix cnt q (.num pre n)
  | _, name => (name, reverseName prev)

/--
`matchName opts pre cinfo` returns true if the search options should include the constant.
-/
private def matchName (opts : PrintPrefixConfig) (pre : Name) (cinfo : ConstantInfo) : MetaM Bool := do
  let name := cinfo.name
  let preCnt := pre.getNumParts
  let nameCnt := name.getNumParts
  if preCnt > nameCnt then return false
  let (root, post) := takeNameSuffix (nameCnt - preCnt) name
  if root ≠ pre then return false
  if !opts.internals && isInternalDetail post then return false
  let isProp := (Expr.isProp <$> Lean.Meta.inferType cinfo.type) <|> pure false
  if opts.propositions then do
    if opts.propositionsOnly && !(←isProp) then return false
  else do
    if opts.propositionsOnly || (←isProp) then return false
  pure true

private def lexNameLt : Name -> Name -> Bool
| _, .anonymous => false
| .anonymous, _ => true
| .num p m, .num q n => m < n || m == n && lexNameLt p q
| .num _ _, .str _ _ => true
| .str _ _, .num _ _ => false
| .str p m, .str q n => m < n || m == n && lexNameLt p q

private def appendMatchingConstants (msg : String) (opts : PrintPrefixConfig) (pre : Name)
     : MetaM String := do
  let cinfos ← getMatchingConstants (matchName opts pre) opts.imported
  let cinfos := cinfos.qsort fun p q => lexNameLt (reverseName p.name) (reverseName q.name)
  let mut msg := msg
  let ppInfo cinfo :=
        if opts.showTypes then do
          pure s!"{cinfo.name} : {← Meta.ppExpr cinfo.type}\n"
        else
          pure s!"{cinfo.name}\n"
  for cinfo in cinfos do
    msg := msg ++ (← ppInfo cinfo)
  pure msg

/--
The command `#print prefix foo` will print all definitions that start with
the namespace `foo`.

By default, it will included imported names and filter out auto-generated
and internal names.  These options can be controlled by passing in config flags.
If the prefix itself contains internal components,


For example, the command below will print out all non-internal names in the
`List namespace.

```lean
#print prefix List
```

This command will also include internal commands:

```lean
#print prefix (config:={internals:=true}) List
```

The command below will exclude imported names:

```lean
#print prefix (config:={imported:=false}) List
```
-/
@[command_elab printPrefix] def elabPrintPrefix : CommandElab
| `(#print prefix%$tk $[$cfg:config]? $name:ident) => do
  let nameId := name.getId
  liftTermElabM do
    let opts ← elabPrintPrefixConfig (mkOptionalNode cfg)
    let mut msg ← appendMatchingConstants "" opts nameId
    if msg.isEmpty then
      if let [name] ← resolveGlobalConst name then
        msg ← appendMatchingConstants msg opts name
    if !msg.isEmpty then
      logInfoAt tk msg
| _ => throwUnsupportedSyntax
