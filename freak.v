Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Freak Require Import Map.

(* Syntax *)

Inductive value : Type :=
  | v_var : string -> value
  | v_lambda : string -> comp -> value
  | v_true : value
  | v_false : value

with comp : Type :=
  | c_return : value -> comp
  | c_app : value -> value -> comp
  | c_if : value -> comp -> comp -> comp
  | c_let : string -> comp -> comp -> comp
  | c_op : string -> value -> string -> comp -> comp
  | c_handle : comp -> handler -> comp

with hreturn : Type :=
    hr_ret : string -> comp -> hreturn

with algebraic_op : Type :=
    alg_op : string -> string -> string -> comp -> algebraic_op

with handler : Type :=
  | handler_return : hreturn -> handler
  | handler_op : algebraic_op -> handler -> handler
.

Hint Constructors value : core.
Hint Constructors comp : core.
Hint Constructors hreturn : core.
Hint Constructors algebraic_op : core.
Hint Constructors handler : core.

(* Parser *)

Declare Custom Entry freak.
Notation "<{ e }>" := e (e custom freak at level 99).
Notation "( x )" := x (in custom freak, x at level 99).
Notation "< x >" := x (in custom freak, x at level 99).
Notation "x" := x (in custom freak at level 0, x constr at level 0).

Notation "\ x -> y" :=
  (v_lambda x y) (in custom freak at level 90, x at level 99,
                  y custom freak at level 99,
                  left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := v_true (in custom freak at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := v_false (in custom freak at level 0).
Coercion v_var : string >-> value.

Notation "'return' x" := (c_return x) (in custom freak at level 10,
                                     x custom freak at level 99).
Notation "x y" := (c_app x y) (in custom freak at level 1, left associativity).
Notation "'if' x 'then' y 'else' z" :=
  (c_if x y z) (in custom freak at level 89,
                    x custom freak at level 99,
                    y custom freak at level 99,
                    z custom freak at level 99,
                    left associativity).

Notation "'let' x <- c1 'in' c2" :=
  (c_let x c1 c2) (in custom freak at level 89,
                    x custom freak at level 99,
                    c1 custom freak at level 99,
                    c2 custom freak at level 99,
                    left associativity).

Notation "'#return' x '->' c" :=
  (hr_ret x c) (in custom freak at level 89,
                        x at level 99,
                        c custom freak at level 99,
                        left associativity).

Notation "'|r' h" :=
  (handler_return h) (in custom freak at level 89,
                        h custom freak at level 99,
                        left associativity).

Notation "'#' op ',' p ',' k '|->' c" :=
  (alg_op op p k c) (in custom freak at level 89,
                      op at level 99,
                      p at level 99,
                      k at level 99,
                      c custom freak at level 99,
                      left associativity).

Notation "'|o' algop ';' h" :=
  (handler_op algop h) (in custom freak at level 91,
                      algop custom freak,
                      h custom freak at level 95,
                      left associativity).

Notation "'do' y '<-' op '@' v 'in' c" :=
  (c_op op v y c) (in custom freak at level 99,
                  op at level 99,
                  y at level 99,
                  c custom freak at level 99,
                  v custom freak at level 99,
                  left associativity).

Notation "'handle' c 'with' h" :=
  (c_handle c h) (in custom freak at level 1,
                  c custom freak at level 99,
                  h custom freak at level 99,
                  left associativity).

(* Substitution *)

Reserved Notation "'[' x ':=' s ']v' v" (in custom freak at level 20, x constr).
Reserved Notation "'[' x ':=' s ']c' c" (in custom freak at level 20, x constr).
Reserved Notation "'[' x ':=' s ']h' h" (in custom freak at level 20, x constr).

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Fixpoint subst_v (x : string) (s : value) (v: value) : value :=
  match v with
  | v_var y =>
      if x =?s y then s else v
  | <{\y -> fb}> =>
      if x =?s y then v else <{\y -> [x:=s]c fb}>
  | v_true => v_true
  | v_false => v_false
  end
where "'[' x ':=' s ']v' v" := (subst_v x s v) (in custom freak)

with subst_h (x : string) (s : value) (h: handler) : handler :=
  match h with
  | <{ |r #return y -> c }> =>
      if x =?s y then h else <{ |r #return y -> [x:=s]c c }>
  | <{ |o # op , p , k |-> c ; h }> =>
      if (x =?s op) || (x =?s p) || (x =?s k)
      then h
      else <{ |o # op , p , k |-> [x:=s]c c ; [x:=s]h h }>
  end
where "'[' x ':=' s ']h' h" := (subst_h x s h) (in custom freak)

with subst (x : string) (s : value) (c: comp) : comp :=
  match c with
  | <{ return y }> => <{ return [x:=s]v y }>
  | <{ v1 v2 }> => <{ ([x:=s]v v1) ([x:=s]v v1) }>
  | <{ if v then c1 else c2 }> =>
      <{if ([x:=s]v v) then ([x:=s]c c1) else ([x:=s]c c2)}>
  | <{ let y <- c1 in c2 }> =>
      if x =?s y
      then <{ let y <- [x:=s]c c1 in c2 }>
      else <{ let y <- [x:=s]c c1 in [x:=s]c c2 }>
  | <{ do y <- op @ v in c }> => <{ do y <- op @ ([x:=s]v v) in ([x:=s]c c) }>
  | <{ handle c with h }> => <{ handle ([x:=s]c c) with ([x:=s]h h) }>
  end
where "'[' x ':=' s ']c' c" := (subst x s c) (in custom freak).

(* Helpers *)

Fixpoint get_hreturn (h:handler) : hreturn :=
  match h with
  | handler_return hr => hr
  | handler_op op h => get_hreturn h
  end.

Definition get_hreturn_var (h:hreturn) : string :=
  match h with
  | <{ #return x -> c }> => x
  end.

Definition get_hreturn_comp (h:hreturn) : comp :=
  match h with
  | <{ #return x -> c }> => c
  end.

Definition get_algop_param_var (op: algebraic_op) : string :=
  match op with
  | <{ # op , p , k |-> c }> => p
  end.

Definition get_algop_comp (op: algebraic_op) : comp :=
  match op with
  | <{ # op , p , k |-> c }> => c
  end.

Definition get_algop_cont_var (op: algebraic_op) : string :=
  match op with
  | <{ # op , p , k |-> c }> => k
  end.

Definition opL (op:algebraic_op) : string :=
  match op with
  | <{ # op , p , k |-> c }> => op
  end.

Hint Unfold get_hreturn_var get_hreturn_comp
            get_algop_cont_var get_algop_cont_var opL get_algop_comp : core.

Fixpoint find_handler (h:handler) (op:string) : option algebraic_op :=
  match h with
  | handler_return hr => None
  | handler_op algop h =>
      if eqb_string op (opL algop)
      then Some algop
      else find_handler h op
  end.

Definition is_something {A: Type} (o: option A) : bool :=
  match o with
  | Some _ => true
  | None => false
  end.

Hint Unfold is_something : core.

(* Small-step operational semantics *)

Reserved Notation "t '-->' t'" (at level 40).

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
      let p := get_algop_param_var algop in
      let op := opL algop in
      let k := get_algop_cont_var algop in
      let ci := get_algop_comp algop in
      <{ handle (do y <- op @ v in c) with h }> -->
      <{ [k:=\y -> handle c with h]c ([p:=v]c ci) }>
  | step_handle_op_not_found h op c v y :
      (find_handler h op) = None ->
      <{ handle (do y <- op @ v in c) with h }> -->
      <{ do y <- op @ v in (handle c with h) }>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | (instantiate; simpl)]);
  apply multi_refl.
