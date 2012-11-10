
Require Import HoTT.Homotopy.
Require Import pointed_spaces.

Set Implicit Arguments.
Unset Strict Implicit.
Import pointed_spaces.pt_map_notation.

Definition loop_space_type (X : pt_type) : Type := point X = point X.

Definition loop_space (X : pt_type) : pt_type :=
  {| carrier := loop_space_type X ;
     point := idpath |}.


Section loop_space_functorial.

Variables X Y : pt_type.
Variable f : X .-> Y.

Definition loop_space_map_carrier (* (X Y : pt_type) (f : pt_map X Y)*) :
   loop_space_type X -> loop_space_type Y :=
   fun p => 
     !pt_map_point f @ map f p @ pt_map_point f.

Definition loop_space_map_refl : 
   loop_space_map_carrier idpath = idpath.
Proof.
  unfold loop_space_map_carrier.
  rewrite idpath_map.
  apply opposite_left_inverse.
Defined.


Definition loop_space_map_concat (p q : loop_space_type X) :
   loop_space_map_carrier (p @ q) = 
     loop_space_map_carrier p @ loop_space_map_carrier q.
Proof.
  transitivity (!pt_map_point f @ map f p @ map f q @ pt_map_point f).
  unfold loop_space_map_carrier.
  apply whisker_left.
  rewrite concat_map.
  rewrite concat_associativity.
  reflexivity.
  unfold loop_space_map_carrier.
  repeat rewrite concat_associativity.
  apply whisker_left.
  apply whisker_left.
  repeat  rewrite <- concat_associativity.
  apply whisker_right.
(*  rewrite concat_associativity. *)
  rewrite opposite_right_inverse.
  reflexivity.
Defined.

Definition loop_space_map : loop_space X .-> loop_space Y.
exists loop_space_map_carrier.
simpl.
exact loop_space_map_refl.
Defined.

End loop_space_functorial.



