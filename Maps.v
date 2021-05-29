(*
In majority taken from Maps chapter in Software Foundations Logical Foundations

https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html
*)
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

(* Eqb string *)

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Notation "x =?s y" := (eqb_string x y) (at level 89).

Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof.
  intros s. unfold eqb_string.
  destruct (string_dec s s) as [Hs_eq | Hs_not_eq].
  - reflexivity.
  - destruct Hs_not_eq. reflexivity.
Qed.

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [Hs_eq | Hs_not_eq].
   - rewrite Hs_eq. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. exfalso. apply Hs_not_eq. apply H.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity.
Qed.

Theorem false_eqb_string : forall x y : string,
   x <> y -> eqb_string x y = false.
Proof.
  intros x y. rewrite eqb_string_false_iff. auto.
Qed.

Hint Resolve eqb_string_refl : core.
Hint Rewrite <- eqb_string_refl : core.

(* Total Map *)

Definition total_map (A : Type) := string -> A.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
    fun x' => if eqb_string x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

Hint Unfold t_empty : core.
Hint Unfold t_update : core.

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof. auto. Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update.
  autorewrite with core. auto.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v Hne.
  unfold t_update.
  assert (Heq: eqb_string x1 x2 = false). {
    apply eqb_string_false_iff. apply Hne.
  }
  rewrite -> Heq. reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros A m x v1 v2.
  unfold t_update.
  apply functional_extensionality.
  intros y.
  destruct (eqb_string x y); auto.
Qed.

Lemma eqb_stringP : forall x y : string,
    reflect (x = y) (eqb_string x y).
Proof.
  intros x y.
  apply iff_reflect.
  split.
  - intros H. apply eqb_string_true_iff. apply H.
  - intros H. apply eqb_string_true_iff. apply H.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros A m x.
  unfold t_update.
  apply functional_extensionality.
  intros y.
  destruct (eqb_stringP x y).
  - f_equal. apply e.
  - f_equal.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros A m v1 v2 x1 x2 Hne. unfold t_update.
  apply functional_extensionality.
  intros y.
  destruct (eqb_stringP x1 y).
  - destruct (eqb_stringP x2 y).
    + rewrite <- e in e0. contradiction.
    + reflexivity.
  - reflexivity.
Qed.

(* Partial maps *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq; auto.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

Definition inclusion {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

Lemma inclusion_update : forall (A : Type) (m m': partial_map A)
                              x vx,
  inclusion m m' ->
  inclusion (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold inclusion.
  intros A m m' x vx H.
  intros y vy.
  destruct (eqb_stringP x y) as [Hxy | Hxy].
  - rewrite Hxy.
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
  - rewrite update_neq. rewrite update_neq.
    + apply H.
    + apply Hxy.
    + apply Hxy.
Qed.

Hint Resolve inclusion_update : core.

