import StrongRoberson.MainTheorem

/-!
# Signature identity audit for Theorem 6

This file deliberately depends on the assembled theorem and is not imported
by the proof.  The command hashes Lean's elaborated expression for the
declaration type (not its proof body) and fails elaboration if it differs from
the hash recorded before proof development.
-/

open Lean Elab Command

elab "#guard_signature_hash " id:ident " = " expected:num : command => do
  let env ← getEnv
  let some info := env.find? id.getId
    | throwError "unknown declaration {id.getId}"
  let actual := hash info.type
  let wanted := UInt64.ofNat expected.getNat
  unless actual = wanted do
    throwError "signature hash mismatch: expected {wanted}, got {actual}"
  logInfo m!"signature hash verified: {actual}"

#guard_signature_hash
  StrongRoberson.oddomorphism_implies_splitOffMinor = 1595059117
