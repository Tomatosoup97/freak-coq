Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.

From Freak Require Import Language.
From Freak Require Import Map.
From Freak Require Import Semantics.

Definition identity_handler : handler :=
    let x := "x"%string in
    <{ |r #return x -> return x }>.

(* Opt let *)

Reserved Notation "'~conv_let' f ',' fh '~' c"
  (in custom freak at level 10).
Reserved Notation "'~conv_let_v' f ',' fh '~' v"
  (in custom freak at level 10).
Reserved Notation "'~conv_let_h' f ',' fh '~' h"
  (in custom freak at level 10).

Fixpoint conv_let_v (f: comp -> comp) (fh : handler -> bool) (v: value) : value :=
  match v with
  | v_var y => v_var y
  | <{\y -> fb}> => <{\y -> ~conv_let f , fh~ fb}>
  | v_true => v_true
  | v_false => v_false
  | v_nat n => v_nat n
  end
  where "'~conv_let_v' f ',' fh '~' v" :=
        (conv_let_v f fh v) (in custom freak)

with conv_let_h (f: comp -> comp) (fh : handler -> bool)  (h: handler) : handler :=
  (* if h overrides get or put operation we stop conversion *)
  if fh h then h
  else
  match h with
  | <{ |r #return y -> c }> =>
        <{ |r #return y -> (~conv_let f, fh~ c) }>
  | <{ |o # op , p , k |-> c ; h }> =>
      let h' := conv_let_h f fh h in
      <{ |o # op , p , k |-> (~conv_let f, fh~ c) ; h' }>
  end
where "'~conv_let_h' f ',' fh '~' h" :=
        (conv_let_h f fh h) (in custom freak)

with conv_let (f: comp -> comp) (fh : handler -> bool)  (c: comp) : comp :=
  match c with
  | <{ return y }> =>
        <{ return (~conv_let_v f, fh~ y) }>
  | <{ v1 v2 }> =>
        <{ (~conv_let_v f, fh~ v1) (~conv_let_v f, fh~ v2) }>
  | <{ if v then c1 else c2 }> =>
        <{ if (~conv_let_v f, fh~ v)
           then (~conv_let f, fh~ c1)
           else (~conv_let f, fh~ c2) }>
  | <{ let y <- c1 in c2 }> =>
        <{ let y <- (~conv_let f, fh~ c1) in (~conv_let f, fh~ c2) }>
  | <{ do y <- op @ v in c }> =>
        let c' := conv_let f fh c in
        f <{ do y <- op @ v in c' }>
  | <{ handle c with h }> =>
        let h' := conv_let_h f fh h in
        <{ handle (~conv_let f, fh~ c) with h' }>
  end
where "'~conv_let' f ',' fh '~' c" :=
        (conv_let f fh c) (in custom freak).

Reserved Notation "'~opt_st~' c" (in custom freak at level 10).
Reserved Notation "'~opt_st_v~' v" (in custom freak at level 10).
Reserved Notation "'~opt_st_h~' h c" (in custom freak at level 10).

Definition conv_op (is_put: bool) (op: string) (coalgName: string) (c: comp) : comp :=
  match c with
  | <{ do y <- op' @ v in c' }> =>
        if (op =?s op') then
            if is_put
            then <{ let coalgName <- return v in
                    let y <- return true in c' }>
            else <{ let y <- return (@ coalgName) in c' }>
        else c
  | _ => c
  end.

Definition handler_exists (op: string) (h: handler) : bool :=
  is_something (find_handler h op).

(* Opt *)

Fixpoint opt_st_v (v: value) : value :=
  match v with
  | v_var y => v_var y
  | <{\y -> fb}> => <{\y -> ~opt_st~ fb}>
  | v_true => v_true
  | v_false => v_false
  | v_nat n => v_nat n
  end
  where "'~opt_st_v~' v" := (opt_st_v v) (in custom freak)

with opt_st_h (h: handler) (c: comp) : (handler * comp) :=
  match h with
  | <{
       (* Put s' k -> return (\s -> k true s' *)
       |o # put , sp , kp |-> return (\spl ->
            let kpp <- ((@ kp') true) in (@ kpp') (@ sp')
       );

       (* Get s' k -> return (\s -> k s s) *)
       |o # get , _ , kg |->
           return (\sgl ->
            let kgp <- ((@ kg') (@ sgl')) in (@ kgp') (@ sgl'')
       );

       (* return y -> return (\s -> return y) *)
       |r #return y -> return (\s -> return (@ y'))
    }> =>

    (* ensure handler variables are just as we expect them to be *)
    if (y =?s y') && (sp =?s sp') && (kp =?s kp') && (kpp =?s kpp') &&
       (sgl =?s sgl') && (sgl' =?s sgl'') && (kg =?s kg') &&
       (kgp =?s kgp')

    then let coalgName := ("_coalg_" ++ put ++ "_" ++ get)%string in
         let conv_put := conv_op true put coalgName in
         let conv_get := conv_op false get coalgName in
         let opt_put := conv_let conv_put (handler_exists put) in
         let opt_get := conv_let conv_get (handler_exists get) in
         let opt c := opt_put (opt_get c) in
         let context c := <{
            return (\s -> let coalgName <- return s in c)
         }> in
         (identity_handler, context (opt c))
    else (h, c)

  | <{ |r #return y -> c' }> => (<{ |r #return y -> (~opt_st~ c') }>, c)
  | <{ |o # op , p , k |-> c' ; h }> =>
    let (h', c'') := opt_st_h h c in
    (<{ |o # op , p , k |-> (~opt_st~ c') ; h' }>, c'')
  end
where "'~opt_st_h~' h c" := (opt_st_h h c) (in custom freak)

with opt_st (c: comp) : comp :=
  match c with
  | <{ return y }> =>
        <{ return (~opt_st_v~ y) }>
  | <{ v1 v2 }> =>
        <{ (~opt_st_v~ v1) (~opt_st_v~ v2) }>
  | <{ if v then c1 else c2 }> =>
        <{ if (~opt_st_v~ v) then (~opt_st~ c1) else (~opt_st~ c2) }>
  | <{ let y <- c1 in c2 }> =>
        <{ let y <- (~opt_st~ c1) in (~opt_st~ c2) }>
  | <{ do y <- op @ v in c }> =>
        <{ do y <- op @ (~opt_st_v~ v) in (~opt_st~ c) }>
  | <{ handle c with h }> =>
        let c' := opt_st c in
        let (h', c'') := opt_st_h h c' in
        <{ handle (c'') with h' }>
  end
where "'~opt_st~' c" := (opt_st c) (in custom freak).

