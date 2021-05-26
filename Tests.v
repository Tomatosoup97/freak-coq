Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.

From Freak Require Import freak.

Module Tests.

Definition rnat x := <{ return x }>.
Definition x : string := "x".
Definition y : string := "y".
Definition s : string := "s".
Definition f : string := "f".
Hint Unfold rnat : core.

Example eval_nat: rnat 42 / {} -->* rnat 42 / {}.
Proof. normalize. Qed.

Example eval_app:
  <{ (\s -> return s) 42 }> / {} -->* rnat 42 / {}.
Proof. normalize. Qed.

Example eval_let_lambda_forget :
  <{ let f <- return (\s -> return s) in return 42 }> / {} -->*
  rnat 42 / {}.
Proof. normalize. Qed.

Example eval_let_lambda :
  <{ let f <- return (\s -> return s) in (f 42) }> / {} -->*
  rnat 42 / {}.
Proof. normalize. Qed.

Example if_true :
  <{ if true then return 1 else return 2 }> / {} -->* rnat 1 / {}.
Proof. normalize. Qed.

Example if_false :
  <{ if false then return 1 else return 2 }> / {} -->* rnat 2 / {}.
Proof. normalize. Qed.

Example var_capture :
  <{
    let x <- return 1 in
    let x <- return 2 in
    return x
  }> / {} -->* rnat 2 / {}.
Proof. normalize. Qed.

Example static_scope :
  <{
    let y <- return 1 in
    let f <- return (\x -> return y) in
    let y <- return 2 in f 3
  }> / {} -->* rnat 1 / {}.
Proof. normalize. Qed.

End Tests.

