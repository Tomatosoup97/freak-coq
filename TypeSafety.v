Set Warnings "-notation-overridden,-parsing".
From Freak Require Import Sets.
From Freak Require Import Maps.
From Freak Require Import Language.
From Freak Require Import Subst.
From Freak Require Import Semantics.
From Freak Require Import Types.

Ltac forward_gen H tac :=
  match type of H with
  | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

Ltac var_in_empty_gamma_contra H :=
  rewrite apply_empty in H; discriminate.

Lemma canonical_forms_bool : forall (v : value),
  empty |-v v : Bool ->
  (v = <{true}>) \/ (v = <{false}>).
Proof.
  intros. remember empty as Gamma.
  inversion H; subst; eauto.
  var_in_empty_gamma_contra H0.
Qed.

Lemma canonical_forms_nat : forall (v : value),
  empty |-v v : Nat ->
  exists (n: nat), v = <{ n }>.
Proof.
  intros. remember empty as Gamma.
  inversion H; subst; eauto.
  var_in_empty_gamma_contra H0.
Qed.

Lemma canonical_forms_fun : forall f A C ,
  empty |-v f : (A :-> C) ->
  exists x c, f = <{\x -> c}>.
Proof.
  intros. remember empty as Gamma.
  inversion H; subst; eauto.
  var_in_empty_gamma_contra H0.
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

Theorem preservation : forall c c' C,
  empty |-c c : C ->
  c --> c' ->
  empty |-c c' : C.
Proof.
  intros c c' C HC. generalize dependent c'.
  remember empty as Gamma.
  induction HC;
  intros c' Hs; subst.
  - (* return *) inversion Hs.
  - (* if *) inversion Hs; subst; eauto.
  - (* let *)
    forward IHHC1. { reflexivity. }
    inversion Hs; subst.
    + (* let progress *) eauto.
    + (* let return *)
      eapply substitution_lemma.
      * apply HC2.
      * inversion HC1. apply H2.
    + (* let op *)
      rename c0 into c1.
      admit.
  - (* app *)
    inversion Hs; subst.
    inversion H; subst.
    eapply substitution_lemma; eauto.
  - (* handle *)
    forward IHHC. { reflexivity. }
    inversion Hs; clear Hs; subst.
    + eauto.
    + inversion H; subst.
      assert (Hx0: x = x0). { unfold x, x0. reflexivity. }
      assert (Hcr0: cr = cr0). { unfold cr, cr0. reflexivity. }
      rewrite <- Hx0 in *. rewrite <- Hcr0 in *.
      eapply substitution_lemma.
      apply H5.
      inversion HC; subst. apply H4.
    +
      (*
      eapply substitution_lemma.
      * eapply substitution_lemma.
        -- inversion H; clear H; subst.
           eapply H3.
           ++ destruct algop.
              apply H2.
           ++ inversion HC; subst.
              eapply H9.
       *)

      inversion H. inversion HC.
      destruct algop. clear H HC.
      assert (Hsign: S0 = S). { admit. } (* TODO *)
      subst. simpl in *.
      eapply substitution_lemma.
      * eapply substitution_lemma.
        eapply H3. eapply H2.
        apply H13. apply H15.
      * admit.
    + admit.
  - (* op *)
    admit.
Admitted.

