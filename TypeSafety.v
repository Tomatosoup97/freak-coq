Set Warnings "-notation-overridden,-parsing".
From Freak Require Import Sets.
From Freak Require Import Maps.
From Freak Require Import Language.
From Freak Require Import Semantics.
From Freak Require Import Types.

Ltac forward_gen H tac :=
  match type of H with
  | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

Ltac var_in_empty_gamma H := rewrite apply_empty in H; discriminate.

Lemma canonical_forms_bool : forall (v : value),
  empty |-v v : Bool ->
  (v = <{true}>) \/ (v = <{false}>).
Proof.
  intros. remember empty as Gamma.
  inversion H; subst; eauto.
  var_in_empty_gamma H0.
Qed.

Lemma canonical_forms_nat : forall (v : value),
  empty |-v v : Nat ->
  exists (n: nat), v = <{ n }>.
Proof.
  intros. remember empty as Gamma.
  inversion H; subst; eauto.
  var_in_empty_gamma H0.
Qed.

Lemma canonical_forms_fun : forall f A C ,
  empty |-v f : (A :-> C) ->
  exists x c, f = <{\x -> c}>.
Proof.
  intros. remember empty as Gamma.
  inversion H; subst; eauto.
  var_in_empty_gamma H0.
Qed.

Theorem progress : forall c A D,
  empty |-c c : (A ! D) ->
  (exists v, c = <{ return v }>) \/
  (exists c', c --> c') \/
  (exists op v c' y,
    InDelta op D /\ c = <{ do y <- op @ v in c' }>).
Proof.
  intros.
  remember empty as Gamma.
  (* remember <{ A ! D }> as cT. *)
  induction H;
  (* inversion HeqcT; *)
  subst.
  - (* Return *) left. eauto.
  - (* If *) right.
    apply canonical_forms_bool in H as [Hb | Hb]; subst; eauto.
  - (* Let *)
    right. left.
    forward IHc_has_type1. { reflexivity. }
    destruct IHc_has_type1 as [[v IH] | [[c' IH] | [op [v [c' [y [InD IH]]]]]]].
    (* + admit. *)
    + subst. eexists. eapply step_let_return.
    + exists <{ let x <- c' in c2 }>. apply step_let. apply IH.
    + subst. eexists. apply step_let_op.
  - (* App *)
    right. left.
    apply canonical_forms_fun in H as [x [c H]].
    subst. eauto.
  - (* Handle *)
    right. left.
    forward IHc_has_type. { reflexivity. }
    destruct IHc_has_type as [[v IH] | [[c' IH] | [op [v [c' [y [InD IH]]]]]]].
    (* + admit. *)
    + subst. eexists. apply step_handle_return.
    + eexists. apply step_handle. apply IH.
    + inversion H. subst.
      subst. destruct (find_handler h op) eqn:Ehandler.
      * (* h handles op *)
        eexists.
        eapply step_handle_op. apply Ehandler.
        eapply find_handler_op_label.
        apply Ehandler.
      * (* h does not handle op *)
        eexists. eapply step_handle_op_search. apply Ehandler.
  - (* Do op *)
    right. right.
    repeat eexists.
    (* apply H1. *)
    admit.
Admitted.

