Set Warnings "-notation-overridden,-parsing".
From Coq Require Import MSets.MSetWeakList.
From Coq Require Import Structures.OrderedTypeEx.
From Coq Require Import Structures.OrdersAlt.

Module String_as_OT := Update_OT String_as_OT.
Module StrSets := Coq.MSets.MSetWeakList.Make String_as_OT.

Definition StrSet := StrSets.t.

