import Lake
open Lake DSL

package knuth_fasc8a_ex210 where

@[default_target]
lean_lib KnuthFasc8aEx210 where

lean_exe knuth_cert_check where
  root := `KnuthFasc8aEx210.CertCheck
