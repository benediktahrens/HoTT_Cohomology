

Require Import HoTT.Homotopy.

Set Implicit Arguments.
Unset Strict Implicit.

Ltac pathvia b := (apply (concat (y:=b))).
