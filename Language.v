Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.

From Freak Require Import Map.

(* Syntax *)

Inductive value : Type :=
  | v_var : string -> value
  | v_lambda : string -> comp -> value
  | v_true : value
  | v_false : value
  | v_nat : nat -> value

with comp : Type :=
  | c_return : value -> comp
  | c_app : value -> value -> comp
  | c_if : value -> comp -> comp -> comp
  | c_let : string -> comp -> comp -> comp
  | c_op : string -> value -> string -> comp -> comp
  | c_handle : comp -> handler -> comp
  | c_assgn : string -> value -> comp

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
Notation "'@' x" := (v_var x) (in custom freak at level 10, x at level 99).

Coercion v_nat : nat >-> value.

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

Notation "x '::=' c" :=
  (c_assgn x c) (in custom freak at level 91,
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

Definition is_something {A: Type} (o: option A) : bool :=
  match o with
  | Some _ => true
  | None => false
  end.

Hint Unfold is_something : core.

Hint Unfold get_hreturn_var get_hreturn_comp
            get_algop_cont_var get_algop_cont_var opL get_algop_comp : core.

Fixpoint find_handler (h:handler) (op:string) : option algebraic_op :=
  match h with
  | handler_return hr => None
  | handler_op algop h =>
      if op =?s (opL algop)
      then Some algop
      else find_handler h op
  end.

