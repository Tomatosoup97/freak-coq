Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Freak Require Import Map.
From Freak Require Import Language.
From Freak Require Import Subst.

(* Small-step operational semantics *)

Definition state := total_map value.
Notation "'{}'" := (t_empty (v_nat 0)).

Reserved Notation " t / st '-->' t' / st' "
                  (at level 40, st at level 39, t' at level 39).

Inductive step : (comp*state) -> (comp*state) -> Prop :=
  | step_app x c v st :
      <{ (\x -> c) v }> / st --> <{ [x:=v]c c }> / st
  | step_if_true c1 c2 st :
      <{ if true then c1 else c2 }> / st --> c1 / st
  | step_if_false c1 c2 st :
      <{ if false then c1 else c2 }> /st --> c2 / st
  | step_let x c1 c1' c2 st st':
      c1 / st --> c1' / st' ->
      <{ let x <- c1 in c2 }> / st --> <{ let x <- c1' in c2 }> / st'
  | step_let_return x v c st :
      <{ let x <- return v in c }> / st --> <{ [x:=v]c c }> / st
  | step_assgn x v st :
      <{ x ::= v }> / st --> <{ return v }> / (x !-> v ; st)
  | step_handle h c c' st st' :
      c / st --> c' / st' ->
      <{ handle c with h }> / st --> <{ handle c' with h }> / st'
  | step_handle_return h v st :
      let x := get_hreturn_var (get_hreturn h) in
      let cr := get_hreturn_comp (get_hreturn h) in
      <{ handle (return v) with h }> / st -->
      <{ [x:=v]c cr }> / st
  | step_handle_op h op c algop v y st :
      (find_handler h op) = Some algop ->
      let p := get_algop_param_var algop in
      let op := opL algop in
      let k := get_algop_cont_var algop in
      let ci := get_algop_comp algop in
      <{ handle (do y <- op @ v in c) with h }> / st -->
      <{ [k:=\y -> handle c with h]c ([p:=v]c ci) }> / st
  | step_handle_op_search h op c v y st :
      (find_handler h op) = None ->
      <{ handle (do y <- op @ v in c) with h }> / st -->
      <{ do y <- op @ v in (handle c with h) }> / st

where "t / s '-->' t' / s' " := (step (t,s) (t',s')).

Hint Constructors step : core.

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation multistep := (multi step).
Notation "t1 / st1 '-->*' t2 / st2" :=
  (multistep (t1, st1) (t2, st2))
  (at level 40, st1 at level 39, t2 at level 39).

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (
    print_goal; eapply multi_step ;
    [ (eauto 10; autorewrite with core ; fail) |
      (instantiate; simpl)] ;
    autorewrite with core
  );
  apply multi_refl.

