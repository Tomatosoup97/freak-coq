Set Warnings "-notation-overridden,-parsing".
From Coq Require Import MSets.MSetWeakList.
From Coq Require Import Structures.OrderedTypeEx.
From Coq Require Import Structures.OrdersAlt.

Module String_as_OT := Update_OT String_as_OT.
Module StrSets := Coq.MSets.MSetWeakList.Make String_as_OT.

Definition StrSet := StrSets.t.

Lemma subset_diff : forall S x, Sets.StrSets.Subset (Sets.StrSets.diff S x) S.
Proof.
  unfold StrSets.Subset. intros.
  apply StrSets.diff_spec in H.
  destruct H as [H1 H2].
  apply H1.
Qed.

