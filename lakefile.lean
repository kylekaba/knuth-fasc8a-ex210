import Lake
open Lake DSL

package knuth_fasc8a_ex210 where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

@[default_target]
lean_lib KnuthFasc8aEx210 where

lean_exe knuth_cert_check where
  root := `KnuthFasc8aEx210.CertCheck
