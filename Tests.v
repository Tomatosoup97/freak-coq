Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.

From Freak Require Import Language.
From Freak Require Import Map.
From Freak Require Import Semantics.

Module Tests.

Definition rnat x := <{ return x }>.
Definition x : string := "x".
Definition y : string := "y".
Definition s : string := "s".
Definition f : string := "f".
Definition p : string := "p".
Definition k : string := "k".
Definition Const : string := "Const".
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


Example trivial_handler :
  <{ handle return 1 with ( |r #return x -> return x ) }> / {}
  -->* rnat 1 / {}.
Proof. normalize. Qed.

Example handler_return_overrite :
  <{ handle return 1 with ( |r #return x -> return 2 ) }> / {}
  -->* rnat 2 / {}.
Proof. normalize. Qed.

Example const_handler :
  <{ handle
        (do y <- Const @ 1 in return y)
    with (
        |o # Const , p , k |-> k 42 ;
        |r #return x -> return x ) }> / {}
  -->* rnat 42 / {}.
Proof.
    eapply multi_step.
    - eapply step_handle_op. simpl. auto. auto.
    - normalize.
Qed.

End Tests.

