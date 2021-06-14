Set Warnings "-notation-overridden,-parsing".
From Freak Require Import Sets.
From Freak Require Import Maps.
From Freak Require Import Language.
From Coq Require Import Strings.String.
From Coq Require Import Lists.ListSet.

Definition delta : Type := StrSet.

Inductive opty : Type :=
  | Ty_Op : string -> vty -> vty -> opty

with vty : Type :=
  | VTy_Bool  : vty
  | VTy_Nat  : vty
  | VTy_Arrow : vty -> cty -> vty
  | VTy_Handler : cty -> cty -> vty

with cty : Type :=
  | CTy_Comp : vty -> delta -> cty
.

Definition signature : Type := set opty.

Definition InSignature (op : opty) (sign: signature) :=
  set_In op sign.

Definition InDelta (op : string) (d: delta) :=
  StrSets.In op d.

Notation "'Bool'" := VTy_Bool (in custom freak at level 0).
Notation "'Nat'" := VTy_Nat (in custom freak at level 0).
Notation "A :-> C" := (VTy_Arrow A C)
  (in custom freak at level 40, right associativity).
Notation "C :=> D" := (VTy_Handler C D)
  (in custom freak at level 40, right associativity).
Notation "A ! Delta" := (CTy_Comp A Delta)
  (in custom freak at level 30, left associativity).

Definition context := partial_map vty.

Reserved Notation "Gamma '|-v' t ':' T"
    (at level 101, t custom freak, T custom freak at level 0).
Reserved Notation "Gamma '|-c' t ':' T"
    (at level 101, t custom freak, T custom freak at level 0).
Reserved Notation "Gamma '|-h' h ':' T"
    (at level 101, h custom freak, T custom freak at level 0).

Inductive v_has_type : context -> value -> vty -> Prop :=
  | T_Var : forall Gamma x A,
      Gamma x = Some A ->
      Gamma |-v x : A
  | T_True : forall Gamma,
      Gamma |-v true : Bool
  | T_False : forall Gamma,
      Gamma |-v false : Bool
  | T_Nat : forall Gamma (n: nat),
      Gamma |-v n : Nat
  | T_Lam : forall Gamma x c A C,
      x |-> A ; Gamma |-c c : C ->
      Gamma |-v \x -> c : (A :-> C)

where "Gamma '|-v' t ':' T" := (v_has_type Gamma t T)

with c_has_type : context -> comp -> cty -> Prop :=
  | T_Return : forall Gamma A v delta,
      Gamma |-v v : A ->
      Gamma |-c return v : (A ! delta)
  | T_If : forall Gamma v ct cf C,
      Gamma |-v v : Bool ->
      Gamma |-c ct : C ->
      Gamma |-c cf : C ->
      Gamma |-c if v then ct else cf : C
  | T_Let : forall Gamma x c1 c2 A B D,
      Gamma |-c c1 : (A ! D) ->
      x |-> A ; Gamma |-c c2 : (B ! D) ->
      Gamma |-c let x <- c1 in c2 : (B ! D)
  | T_App : forall Gamma v1 v2 A C,
      Gamma |-v v1 : (A :-> C) ->
      Gamma |-v v2 : A ->
      Gamma |-c v1 v2 : C
  | T_Handle : forall Gamma h c C D,
      Gamma |-h h : (C :=> D) ->
      Gamma |-c c : C ->
      Gamma |-c handle c with h : D
  | T_Op : forall Gamma y op v c A Aop Bop S D,
      InSignature (Ty_Op op Aop Bop) S ->
      Gamma |-v v : Aop ->
      y |-> Bop ; Gamma |-c c : (A ! D) ->
      InDelta op D ->
      Gamma |-c do y <- op @ v in c : (A ! D)

where "Gamma '|-c' t ':' T" := (c_has_type Gamma t T)

with h_has_type : context -> handler -> vty -> Prop :=
    | T_Handler : forall Gamma h A B D D' S,
        let x := get_hreturn_var (get_hreturn h) in
        let cr := get_hreturn_comp (get_hreturn h) in
        (forall opi Ai Bi ci p k,
            find_handler h opi = Some (alg_op opi p k ci) ->
            InSignature (Ty_Op opi Ai Bi) S ->
            (p |-> Ai ; (k |-> <{ Bi :-> (B ! D') }> ; Gamma)) |-c
            ci : (B ! D')
        ) ->
        x |-> A; Gamma |-c cr : (B ! D') ->
        StrSets.Subset (StrSets.diff D (get_handler_ops h)) D ->
        Gamma |-h h : (A ! D :=> B ! D')

where "Gamma '|-h' t ':' T" := (h_has_type Gamma t T).

Hint Constructors v_has_type : core.
Hint Constructors c_has_type : core.
Hint Constructors h_has_type : core.

Lemma weakening_v : forall Gamma Gamma' v A,
     inclusion Gamma Gamma' ->
     Gamma  |-v v : A  ->
     Gamma' |-v v : A

with weakening_c : forall Gamma Gamma' c C,
     inclusion Gamma Gamma' ->
     Gamma  |-c c : C  ->
     Gamma' |-c c : C
.
Proof.
  (* weakening_v proof *)
  ***
  intros.
  generalize dependent Gamma'.
  induction H0;
  eauto.

  (* weakening proof *)
  ***
  intros.
  generalize dependent Gamma'.
  induction H0; intros; eauto.
(* Somehow can't close this proof, even tho it has all goals finished *)
Admitted.


Lemma weakening : forall Gamma Gamma' c C,
     inclusion Gamma Gamma' ->
     Gamma  |-c c : C  ->
     Gamma' |-c c : C

with weakening_handler : forall Gamma Gamma' h C,
     inclusion Gamma Gamma' ->
     Gamma  |-h h : C  ->
     Gamma' |-h h : C
.
Proof.
  (* weakening proof *)
  ***
  intros.
  generalize dependent Gamma'.
  induction H0;
  eauto.

  (* weakening_h proof *)
  ***
  intros.
  generalize dependent Gamma'.
  induction H0. intros.
  eapply T_Handler.
  + intros. eauto.
    eapply weakening with (Gamma := (p |-> Ai; k |-> <{ Bi :-> B ! D' }>; Gamma)). {
        simple_inclusion.
    }
    eapply H.
    2: apply H4.
    auto.
  + apply weakening with (Gamma := (get_hreturn_var (get_hreturn h) |-> A; Gamma)). {
        simple_inclusion.
    }
    apply H0.
  + apply H1.
(* Somehow can't close this proof, even tho it has all goals finished *)
Admitted.

Lemma weakening_h : forall Gamma Gamma' h C,
     inclusion Gamma Gamma' ->
     Gamma  |-h h : C  ->
     Gamma' |-h h : C
.
Proof.
  intros.
  generalize dependent Gamma'.
  induction H0. intros.
  eapply T_Handler.
  + intros. eauto.
    eapply weakening with (Gamma := (p |-> Ai; k |-> <{ Bi :-> B ! D' }>; Gamma)). {
        simple_inclusion.
    }
    eapply H.
    2: apply H4.
    auto.
  + apply weakening with (Gamma := (get_hreturn_var (get_hreturn h) |-> A; Gamma)). {
        simple_inclusion.
    }
    apply H0.
  + apply H1.
Qed.

Lemma weakening_v_empty : forall Gamma v A,
     empty |-v v : A  ->
     Gamma |-v v : A.
Proof.
  intros Gamma t T.
  eapply weakening_v.
  discriminate.
Qed.

Hint Resolve weakening_v_empty : core.

