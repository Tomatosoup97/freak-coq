Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.

From Freak Require Import Language.
From Freak Require Import Maps.

(* Substitution *)

Reserved Notation "'[' x ':=' s ']v' v" (in custom freak at level 20, x constr).
Reserved Notation "'[' x ':=' s ']c' c" (in custom freak at level 20, x constr).
Reserved Notation "'[' x ':=' s ']h' h" (in custom freak at level 20, x constr).

Fixpoint subst_v (x : string) (s : value) (v: value) : value :=
  match v with
  | v_var y =>
      if x =?s y then s else v
  | <{\y -> fb}> =>
      if x =?s y then v else <{\y -> [x:=s]c fb}>
  | v_true => v_true
  | v_false => v_false
  | v_nat n => v_nat n
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
  | <{ v1 v2 }> => <{ ([x:=s]v v1) ([x:=s]v v2) }>
  | <{ if v then c1 else c2 }> =>
      <{if ([x:=s]v v) then ([x:=s]c c1) else ([x:=s]c c2)}>
  | <{ let y <- c1 in c2 }> =>
      if x =?s y
      then <{ let y <- [x:=s]c c1 in c2 }>
      else <{ let y <- [x:=s]c c1 in [x:=s]c c2 }>
  | <{ do y <- op @ v in c }> =>
      if x =?s y
      then <{ do y <- op @ ([x:=s]v v) in c }>
      else <{ do y <- op @ ([x:=s]v v) in ([x:=s]c c) }>
  | <{ handle c with h }> => <{ handle ([x:=s]c c) with ([x:=s]h h) }>
  end
where "'[' x ':=' s ']c' c" := (subst x s c) (in custom freak).

