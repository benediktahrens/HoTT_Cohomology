Set Implicit Arguments.
Unset Strict Implicit.

Require Import HoTT.Homotopy.
Require Import pointed_spaces.
Require Import tactics.

Import pt_map_notation.

Section reduced_suspension_def.

Variable A : pt_type.

Record rsusp : Type := {
  rsusp_carrier :> Type ;
  rsusb_base : rsusp_carrier ;
  rsusb_bloop : forall a : A, rsusb_base = rsusb_base ;
  rsusb_bloop_triv : rsusb_bloop (point A) = idpath ;
  
  rsusp_elim : forall (P : rsusp_carrier -> Type),
        forall (d_base : P rsusb_base), 
        forall (d_loop : forall a : A, rsusb_bloop a # d_base = d_base),
         True
}.

End reduced_suspension_def.