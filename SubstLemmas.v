Set Warnings "-notation-overridden,-parsing".
From Freak Require Import Maps.
From Freak Require Import Language.
From Freak Require Import Subst.
From Freak Require Import Types.

Lemma substitution_lemma_v : forall Gamma x A s v B,
  x |-> A ; Gamma |-v s : B ->
  empty |-v v : A ->
  Gamma |-v [x:=v]v s : B.
Proof.
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
      (* TODO: mutually recursive lemma *)
      admit.
Admitted.

Hint Resolve substitution_lemma_v : core.

Lemma substitution_lemma_h : forall Gamma x A h v B,
  x |-> A ; Gamma |-h h : B ->
  empty |-v v : A ->
  Gamma |-h [x:=v]h h : B.
Proof.
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
        (* TODO: mutually recursive *)
        admit.
  - (* handle op *)
    destruct a.
    simpl in *.
    destruct ((x =?s s) || (x =?s s0) || (x =?s s1)) eqn:Evar; subst.
    + eapply T_Handler; eauto.
      * intros.
        (* TODO: mutually recursive *)
        admit.
      * admit.
      * admit.
    + eapply T_Handler; eauto; admit.
Admitted.

Hint Resolve substitution_lemma_h : core.

Lemma substitution_lemma : forall Gamma x A c v C,
  x |-> A ; Gamma |-c c : C ->
  empty |-v v : A ->
  Gamma |-c [x:=v]c c : C.
Proof.
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
Qed.

Hint Resolve substitution_lemma : core.
