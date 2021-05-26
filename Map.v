Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.

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

Hint Resolve eqb_string_refl : core.
Hint Rewrite <- eqb_string_refl : core.

(* Total Map *)

(* TODO: consider taking from stdlib *)
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

