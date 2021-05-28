Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Freak Require Import Map.
From Freak Require Import Language.
From Freak Require Import Subst.

(* Small-step operational semantics *)

Reserved Notation " t '-->' t' "
                  (at level 40, t' at level 39).

Inductive step : comp -> comp -> Prop :=
  | step_app x c v :
      <{ (\x -> c) v }> --> <{ [x:=v]c c }>
  | step_if_true c1 c2 :
      <{ if true then c1 else c2 }> --> c1
  | step_if_false c1 c2 :
      <{ if false then c1 else c2 }> --> c2
  | step_let x c1 c1' c2 :
      c1 --> c1' ->
      <{ let x <- c1 in c2 }> --> <{ let x <- c1' in c2 }>
  | step_let_return x v c :
      <{ let x <- return v in c }> --> <{ [x:=v]c c }>
  | step_handle h c c' :
      c --> c' ->
      <{ handle c with h }> --> <{ handle c' with h }>
  | step_handle_return h v :
      let x := get_hreturn_var (get_hreturn h) in
      let cr := get_hreturn_comp (get_hreturn h) in
      <{ handle (return v) with h }> -->
      <{ [x:=v]c cr }>
  | step_handle_op h op c algop v y :
      (find_handler h op) = Some algop ->
      op = opL algop ->
      let p := get_algop_param_var algop in
      let k := get_algop_cont_var algop in
      let ci := get_algop_comp algop in
      <{ handle (do y <- op @ v in c) with h }> -->
      <{ [k:=\y -> handle c with h]c ([p:=v]c ci) }>
  | step_handle_op_search h op c v y :
      (find_handler h op) = None ->
      <{ handle (do y <- op @ v in c) with h }> -->
      <{ do y <- op @ v in (handle c with h) }>

where "t '-->' t' " := (step t t').

Hint Constructors step : core.

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation multistep := (multi step).
Notation "t1 '-->*' t2 " :=
  (multistep t1 t2)
  (at level 40, t2 at level 39).

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  simpl;
  repeat (
    print_goal; eapply multi_step ;
    [ (eauto 10; fail) |
      (instantiate; simpl)] ;
    autorewrite with core
  );
  apply multi_refl.

