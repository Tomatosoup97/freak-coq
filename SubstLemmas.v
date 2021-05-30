Set Warnings "-notation-overridden,-parsing".
From Freak Require Import Maps.
From Freak Require Import Language.
From Freak Require Import Subst.
From Freak Require Import Types.

Ltac forward_gen H tac :=
  match type of H with
  | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.


Lemma
substitution_lemma : forall Gamma x A c v C,
  x |-> A ; Gamma |-c c : C ->
  empty |-v v : A ->
  Gamma |-c [x:=v]c c : C

with substitution_lemma_v : forall Gamma x A s v B,
  x |-> A ; Gamma |-v s : B ->
  empty |-v v : A ->
  Gamma |-v [x:=v]v s : B

with substitution_lemma_h : forall Gamma x A h v B,
  x |-> A ; Gamma |-h h : B ->
  empty |-v v : A ->
  Gamma |-h [x:=v]h h : B.
Proof.
  (* substitution_lemma proof *)
  ***
  intros Gamma x A c v C Hc Hv.
  generalize dependent Gamma. generalize dependent C.
  induction c; intros C Gamma H;
  inversion H; clear H; subst; simpl; eauto.
  - (* let *)
    destruct (eqb_stringP x s); subst.
    + eapply T_Let.
      * apply IHc1. apply H5.
      * rewrite update_shadow in H6. apply H6.
    + eapply T_Let.
      * apply IHc1. apply H5.
      * apply IHc2. rewrite update_permute in H6; auto.
  - (* op *)
    destruct (eqb_stringP x s0); subst.
    + eapply T_Op; eauto.
      rewrite update_shadow in H8. apply H8.
    + eapply T_Op; eauto.
      apply IHc. rewrite update_permute; auto.

  (* substitution_lemma_v proof *)
  ***
  intros Gamma x A s v B Hs Hv.
  generalize dependent Gamma. generalize dependent B.
  induction s; intros B Gamma H;
  inversion H; clear H; subst; simpl; auto.
  - (* var *)
    destruct (eqb_stringP x s); subst.
    + rewrite update_eq in H2. inversion H2. subst.
      apply weakening_v_empty. apply Hv.
    + rewrite update_neq in H2. apply T_Var. apply H2.
      apply n.
  - (* lam *)
    destruct (eqb_stringP x s); subst.
    + rewrite update_shadow in H4.
      apply T_Lam. apply H4.
    + apply T_Lam.
      eapply substitution_lemma.
      * rewrite update_permute.
        apply H4. auto.
      * apply Hv.

  (* substitution_lemma_h proof *)
  ***
  intros Gamma x A h v B Hc Hv.
  generalize dependent Gamma. generalize dependent B.
  induction h; intros B Gamma H;
  inversion H; clear H; subst; simpl; eauto.
  - (* handle return *)
    destruct h.
    destruct (eqb_stringP x s); subst.
    + clear H0. simpl in *.
      eapply T_Handler; eauto.
      * intros. simpl in H. discriminate.
      * simpl. unfold x0 in H1. rewrite update_shadow in H1.
        apply H1.
    + clear H0. simpl in *.
      eapply T_Handler; eauto.
      * intros. simpl in H. discriminate.
      * simpl. unfold x0, cr in H1.
        eapply substitution_lemma.
        -- rewrite update_permute. apply H1.
           auto.
        -- auto.
  - (* handle op *)
    destruct a. rename s into op, s0 into p, s1 into k.
    simpl in *.
    destruct (get_hreturn h) eqn:Hret. simpl in *.
    unfold x0, cr in *. clear x0 cr.
    destruct ((x =?s op) || (x =?s p) || (x =?s k)) eqn:Evar; subst.
    + eapply T_Handler; eauto.
      (* TODO *)
      * intros.
        admit.
      * clear H0 H2. rewrite Hret. simpl. admit.
      * admit.
    + eapply T_Handler; eauto; admit.
Admitted.

